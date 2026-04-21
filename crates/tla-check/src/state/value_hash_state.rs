// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State-level fingerprint computation and trace conversion.
//!
//! Contains state fingerprinting functions (`compute_fingerprint`,
//! `compute_fingerprint_from_array`, etc.) and trace-to-value conversion
//! utilities for TLCExt!Trace support.
//!
//! Extracted from `value_hash.rs` as part of #3338.

use crate::value::MVPerm;
use crate::var_index::{VarIndex, VarRegistry};
use crate::Value;
use std::sync::Arc;
use tla_core::{FNV_OFFSET, FNV_PRIME};
use tla_value::CompactValue;

use super::value_hash::value_fingerprint;
use super::Fingerprint;
use tla_core::kani_types::OrdMap;

/// Convert a slice of states to a TLCExt!Trace value.
///
/// Part of #1117: Returns a tuple of records where each record represents a state.
/// This is the format expected by TLCExt!Trace operator.
///
/// Format: <<[var1 |-> v1, var2 |-> v2, ...], [var1 |-> v1', ...], ...>>
pub(crate) fn states_to_trace_value(states: &[super::State]) -> Value {
    let records: Vec<Value> = states.iter().map(super::State::to_record).collect();
    Value::Tuple(records.into())
}

// ============================================================================
// State fingerprint computation
// ============================================================================

/// Compute salt for a variable at given position (same algorithm as VarRegistry)
fn compute_var_salt_inline(idx: usize, name: &str) -> u64 {
    let mut hash = FNV_OFFSET;
    for byte in (idx as u64).to_le_bytes() {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    for byte in name.bytes() {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash ^= 0xFF;
    hash = hash.wrapping_mul(FNV_PRIME);
    hash
}

/// Compute fingerprint from minimum values found during symmetry reduction.
///
/// This uses the same algorithm as `compute_fingerprint` but takes pre-computed
/// minimum values from the symmetry reduction algorithm, avoiding the need to
/// reconstruct an OrdMap.
pub(super) fn compute_fingerprint_from_min_vals(
    vars_vec: &[(&Arc<str>, &Value)],
    min_vals: &[Value],
) -> Fingerprint {
    let mut combined = 0u64;
    for (i, ((name, _), value)) in vars_vec.iter().zip(min_vals.iter()).enumerate() {
        let salt = compute_var_salt_inline(i, name);
        let value_fp = value_fingerprint(value);
        let contribution = salt.wrapping_mul(value_fp.wrapping_add(1));
        combined ^= contribution;
    }

    // Final mixing to improve distribution
    combined = combined.wrapping_mul(FNV_PRIME);
    combined ^= combined >> 33;
    combined = combined.wrapping_mul(FNV_PRIME);

    Fingerprint(combined)
}

pub(super) fn compute_fingerprint(vars: &OrdMap<Arc<str>, Value>) -> Fingerprint {
    // Use XOR-based combination (same algorithm as compute_fingerprint_from_array)
    // Variables in OrdMap are in sorted order, matching registry order
    let mut combined = 0u64;
    for (i, (name, value)) in vars.iter().enumerate() {
        let salt = compute_var_salt_inline(i, name);
        let value_fp = value_fingerprint(value);
        let contribution = salt.wrapping_mul(value_fp.wrapping_add(1));
        combined ^= contribution;
    }

    // Final mixing to improve distribution
    combined = combined.wrapping_mul(FNV_PRIME);
    combined ^= combined >> 33;
    combined = combined.wrapping_mul(FNV_PRIME);

    Fingerprint(combined)
}

/// Compute fingerprint from an array of values and variable registry
///
/// Uses pre-computed salts from the registry to avoid hashing variable names
/// in the hot path. Each variable contributes independently via XOR combination
/// of its salt with its value's fingerprint.
///
/// NOTE: This produces different fingerprints than `compute_fingerprint` (State-based).
/// ArrayState and State should not be mixed in the same seen set.
pub(crate) fn compute_fingerprint_from_array(
    values: &[Value],
    registry: &VarRegistry,
) -> Fingerprint {
    // Combine per-variable contributions via XOR
    // Each contribution is: salt[i] mixed with value_fingerprint(values[i])
    let mut combined = 0u64;
    for (i, value) in values.iter().enumerate() {
        let salt = registry.fp_salt(VarIndex::new(i));
        let value_fp = value_fingerprint(value);
        // Mix salt and value fingerprint together, then XOR into result
        // Use wrapping_mul for mixing to get better avalanche effect
        let contribution = salt.wrapping_mul(value_fp.wrapping_add(1));
        combined ^= contribution;
    }

    // Final mixing to improve distribution
    combined = finalize_fingerprint_xor(combined, FNV_PRIME);

    Fingerprint(combined)
}

#[inline]
pub(crate) fn finalize_fingerprint_xor(mut combined: u64, fnv_prime: u64) -> u64 {
    combined = combined.wrapping_mul(fnv_prime);
    combined ^= combined >> 33;
    combined = combined.wrapping_mul(fnv_prime);
    combined
}

#[inline]
pub(super) fn combined_xor_from_array(values: &[Value], registry: &VarRegistry) -> u64 {
    let mut combined_xor = 0u64;
    for (i, value) in values.iter().enumerate() {
        let value_fp = value_fingerprint(value);
        let salt = registry.fp_salt(VarIndex::new(i));
        let contribution = salt.wrapping_mul(value_fp.wrapping_add(1));
        combined_xor ^= contribution;
    }
    combined_xor
}

/// Compute a state-dedup fingerprint directly from a compact slot.
///
/// Part of #3579: ArrayState now stores `CompactValue`, so hot fingerprint paths
/// should read inline scalars directly and borrow heap-backed values by reference
/// instead of cloning through `Value::from(&CompactValue)`.
///
/// Part of #3805: Bool and SmallInt use precomputed lookup tables directly,
/// avoiding Value construction and byte-at-a-time FP64 computation entirely.
///
/// Part of #3805 (Wave 9): `#[inline(always)]` + reordered branches: Int first
/// (most common leaf in state fingerprinting — function keys, process IDs, counters),
/// then Bool, then heap. Single `is_inline()` guard funnels both fast paths.
#[inline(always)]
pub(crate) fn compact_value_fingerprint(value: &CompactValue) -> u64 {
    // Hot path: Int is the most common leaf value type in state fingerprinting
    // (function/seq keys, counters, process IDs). Check first for best branch prediction.
    if value.is_int() {
        let n = value.as_int();
        if let Some(fp) = crate::fingerprint::fp64_smallint_lookup(n) {
            return fp;
        }
        return value_fingerprint(&Value::SmallInt(n));
    }
    if value.is_bool() {
        return crate::fingerprint::fp64_bool_lookup(value.as_bool());
    }
    if value.is_heap() {
        return value_fingerprint(value.as_heap_value());
    }

    // Interned string/model value/nil — currently unreachable in production
    // since CompactValue::from(Value) boxes these types, but guard for safety.
    value_fingerprint(&Value::from(value))
}

/// Compute a state-dedup fingerprint from a CompactValue array.
///
/// Part of #3579: CompactValue variant of `compute_fingerprint_from_array`.
/// Reads inline scalars directly and borrows heap values by reference,
/// avoiding the `materialize_values()` allocation that would be needed to
/// call the `&[Value]` version.
pub(crate) fn compute_fingerprint_from_compact_array(
    values: &[CompactValue],
    registry: &VarRegistry,
) -> Fingerprint {
    let combined = combined_xor_from_compact_array(values, registry);
    Fingerprint(finalize_fingerprint_xor(combined, FNV_PRIME))
}

/// Compute combined XOR from a CompactValue array.
///
/// Part of #3579: CompactValue storage variant. Reads inline scalars directly
/// and fingerprints heap-backed values by reference, avoiding per-slot clones
/// on the state hashing hot path.
#[inline]
pub(super) fn combined_xor_from_compact_array(
    values: &[CompactValue],
    registry: &VarRegistry,
) -> u64 {
    let mut combined_xor = 0u64;
    for (i, cv) in values.iter().enumerate() {
        let value_fp = compact_value_fingerprint(cv);
        let salt = registry.fp_salt(VarIndex::new(i));
        let contribution = salt.wrapping_mul(value_fp.wrapping_add(1));
        combined_xor ^= contribution;
    }
    combined_xor
}

/// Compute the canonical (symmetry-reduced) fingerprint from array values.
///
/// Finds the lexicographically minimum permuted state across all permutations
/// (including identity), then fingerprints that minimum state.
///
/// IMPORTANT: This must use lexicographic minimum, NOT minimum fingerprint.
/// fp(lexmin(g(S))) != min(fp(g(S))) because fingerprint order != lexicographic order.
/// Using min(fp) was the bug in Issue #86.
///
/// Uses TLC's interleaved permute-compare with early exit: for each permutation,
/// compare variable-by-variable against the current minimum, skipping the rest
/// if this permutation is already greater.
///
/// Part of #3011: enables symmetry reduction in the parallel checker.
#[cfg(test)]
pub(crate) fn compute_canonical_fingerprint_from_array(
    values: &[Value],
    registry: &VarRegistry,
    mvperms: &[MVPerm],
) -> Fingerprint {
    use std::cmp::Ordering;

    if mvperms.is_empty() {
        return compute_fingerprint_from_array(values, registry);
    }

    // Start with identity (the original values).
    let mut min_vals: Vec<Value> = values.to_vec();

    // TLC-style interleaved permute-compare with early exit.
    'next_perm: for mvperm in mvperms {
        let mut work_vals: Vec<Value> = Vec::with_capacity(values.len());
        let mut cmp = Ordering::Equal;

        for (i, value) in values.iter().enumerate() {
            let permuted = value.permute_fast(mvperm);

            if cmp == Ordering::Equal {
                cmp = permuted.cmp(&min_vals[i]);
                if cmp == Ordering::Greater {
                    continue 'next_perm;
                }
            }
            work_vals.push(permuted);
        }

        if cmp == Ordering::Less {
            min_vals = work_vals;
        }
    }

    // Fingerprint the lexicographic minimum state.
    compute_fingerprint_from_array(&min_vals, registry)
}

/// Compute the canonical (symmetry-reduced) fingerprint from compact array values.
///
/// Part of #3579: CompactValue storage variant of
/// `compute_canonical_fingerprint_from_array`. This keeps symmetry-reduced
/// fingerprinting on the compact representation until the final lexicographic
/// minimum is chosen, avoiding the eager `materialize_values()` allocation in
/// hot replay/init paths.
pub(crate) fn compute_canonical_fingerprint_from_compact_array(
    values: &[CompactValue],
    registry: &VarRegistry,
    mvperms: &[MVPerm],
) -> Fingerprint {
    use std::cmp::Ordering;

    if mvperms.is_empty() {
        return compute_fingerprint_from_compact_array(values, registry);
    }

    let mut min_vals: Vec<Value> = values.iter().map(Value::from).collect();

    'next_perm: for mvperm in mvperms {
        let mut work_vals: Vec<Value> = Vec::with_capacity(values.len());
        let mut cmp = Ordering::Equal;

        for (i, value) in values.iter().enumerate() {
            let permuted = if value.is_heap() {
                value.as_heap_value().permute_fast(mvperm)
            } else {
                Value::from(value).permute_fast(mvperm)
            };

            if cmp == Ordering::Equal {
                cmp = permuted.cmp(&min_vals[i]);
                if cmp == Ordering::Greater {
                    continue 'next_perm;
                }
            }
            work_vals.push(permuted);
        }

        if cmp == Ordering::Less {
            min_vals = work_vals;
        }
    }

    compute_fingerprint_from_array(&min_vals, registry)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compact_value_fingerprint_matches_value_fingerprint_for_representative_values() {
        let values = vec![
            Value::Bool(true),
            Value::int(-7),
            Value::seq(vec![Value::int(1), Value::Bool(false)]),
            Value::record([("x", Value::int(2)), ("flag", Value::Bool(true))]),
            Value::set(vec![Value::int(3), Value::int(4)]),
        ];

        for value in values {
            let compact = CompactValue::from(value.clone());
            assert_eq!(
                compact_value_fingerprint(&compact),
                value_fingerprint(&value),
                "compact fingerprint must match Value fingerprint for {value:?}"
            );
        }
    }

    #[test]
    fn combined_xor_from_compact_array_matches_value_array() {
        let registry = VarRegistry::from_names(["a", "b", "c", "d"]);
        let values = vec![
            Value::int(1),
            Value::Bool(false),
            Value::seq(vec![Value::int(2), Value::int(3)]),
            Value::record([("x", Value::Bool(true))]),
        ];
        let compact: Vec<CompactValue> = values.iter().cloned().map(CompactValue::from).collect();

        assert_eq!(
            combined_xor_from_compact_array(&compact, &registry),
            combined_xor_from_array(&values, &registry),
            "compact-state XOR must stay bit-for-bit identical to Value-state XOR"
        );
    }

    #[test]
    fn compute_canonical_fingerprint_from_compact_array_matches_value_array() {
        let registry = VarRegistry::from_names(["x", "y", "z"]);
        let values = vec![
            Value::try_model_value("a2").unwrap(),
            Value::record([("flag", Value::Bool(true))]),
            Value::try_model_value("a1").unwrap(),
        ];
        let compact: Vec<CompactValue> = values.iter().cloned().map(CompactValue::from).collect();

        let perm = crate::value::FuncValue::from_sorted_entries(vec![
            (
                Value::try_model_value("a1").unwrap(),
                Value::try_model_value("a2").unwrap(),
            ),
            (
                Value::try_model_value("a2").unwrap(),
                Value::try_model_value("a1").unwrap(),
            ),
        ]);
        let mvperms = vec![crate::value::MVPerm::from_func_value(&perm).unwrap()];

        assert_eq!(
            compute_canonical_fingerprint_from_compact_array(&compact, &registry, &mvperms),
            compute_canonical_fingerprint_from_array(&values, &registry, &mvperms),
            "compact-array symmetry fingerprint must match the Value-array baseline"
        );
    }
}
