// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FlatState interpreter adapter for BFS model checking.
//!
//! Provides the Tier 0 (interpreter) cold path for FlatState-based BFS:
//!
//! ```text
//!   FlatState → ArrayState → eval actions → ArrayState → FlatState
//! ```
//!
//! This adapter enables the BFS loop to natively store and dequeue FlatState
//! buffers (contiguous `[i64]` arrays) while still using the interpreter for
//! action evaluation. The conversion overhead is O(V) per state where V is the
//! number of state variables — acceptable as a cold path until JIT compilation
//! can operate directly on `[i64]` buffers.
//!
//! # Design
//!
//! The adapter wraps `FlatBfsBridge` with convenience methods for the BFS
//! successor pipeline:
//!
//! 1. **`flat_to_array`** — Convert a `FlatState` to `ArrayState` for eval.
//!    Uses `to_array_state_with_fallback` when the layout has Dynamic vars.
//!
//! 2. **`array_to_flat`** — Convert an `ArrayState` back to `FlatState` after
//!    eval produces successor states.
//!
//! 3. **`flat_fingerprint_to_traditional`** — Compute the traditional 64-bit
//!    `Fingerprint` from a `FlatState` for dedup consistency with the
//!    interpreter path. This is the critical correctness requirement: the
//!    seen-set uses 64-bit fingerprints, and they MUST match regardless of
//!    whether the state was generated via the flat or interpreter path.
//!
//! 4. **`batch_convert_successors`** — Convert a batch of ArrayState successors
//!    to FlatStates, computing fingerprints for each. Used after the interpreter
//!    generates successors to prepare them for flat-path enqueue.
//!
//! # Correctness
//!
//! The adapter guarantees fingerprint identity:
//!   `fingerprint(flat_to_array(s)) == fingerprint(s)` for all states `s`.
//!
//! This is enforced by `FlatBfsBridge::verify_roundtrip_fingerprint` and
//! tested in `flat_bfs_bridge.rs`.
//!
//! Part of #4126: FlatState as native BFS representation (Phase E of supremacy plan).

use std::sync::Arc;

use super::flat_bfs_bridge::FlatBfsBridge;
use super::flat_state::{FlatReconstructionError, FlatState};
use super::state_layout::StateLayout;
use super::{ArrayState, Fingerprint};
use crate::var_index::VarRegistry;
use tla_value::CompactValue;

/// Short human-readable type tag for a `CompactValue`. Used in roundtrip
/// diagnostics (issue #4275) to explain which variable differed between the
/// original and the reconstructed state.
fn value_type_tag(cv: &CompactValue) -> &'static str {
    use tla_value::Value;
    match Value::from(cv) {
        Value::SmallInt(_) => "SmallInt",
        Value::Int(_) => "Int",
        Value::Bool(_) => "Bool",
        Value::String(_) => "String",
        Value::ModelValue(_) => "ModelValue",
        Value::Set(_) => "Set",
        Value::Tuple(_) => "Tuple",
        Value::Seq(_) => "Seq",
        Value::Func(_) => "Func",
        Value::IntFunc(_) => "IntFunc",
        Value::Record(_) => "Record",
        _ => "Other",
    }
}

/// Interpreter adapter for FlatState-based BFS.
///
/// Wraps `FlatBfsBridge` with BFS-specific convenience methods and tracks
/// statistics for performance monitoring.
///
/// Created once per model-checking run alongside the `FlatBfsBridge`. The
/// adapter is `Clone` to allow one per BFS worker thread (each holding an
/// `Arc` to the shared layout).
///
/// Part of #4126.
#[derive(Debug, Clone)]
pub(crate) struct FlatBfsAdapter {
    /// The underlying bridge for conversions and fingerprinting.
    bridge: FlatBfsBridge,
    /// Number of flat→array conversions performed (for stats).
    flat_to_array_count: u64,
    /// Number of array→flat conversions performed (for stats).
    array_to_flat_count: u64,
    /// Whether the flat roundtrip has been verified against the first initial
    /// state. Only set to true when `verify_roundtrip` confirms that
    /// ArrayState → FlatState → ArrayState preserves the fingerprint.
    ///
    /// The BFS pipeline must check `roundtrip_verified()` before using Flat
    /// queue entries. Without this check, specs with string/model-value
    /// variables that are classified as `Scalar` (but lose data in the i64
    /// roundtrip) would silently corrupt states.
    ///
    /// Part of #4126.
    roundtrip_verified: bool,
}

impl FlatBfsAdapter {
    /// Create a new adapter from a `FlatBfsBridge`.
    #[must_use]
    pub(crate) fn new(bridge: FlatBfsBridge) -> Self {
        FlatBfsAdapter {
            bridge,
            flat_to_array_count: 0,
            array_to_flat_count: 0,
            roundtrip_verified: false,
        }
    }

    /// Create a new adapter from a `StateLayout`.
    ///
    /// Constructs the underlying `FlatBfsBridge` internally.
    #[must_use]
    pub(crate) fn from_layout(layout: Arc<StateLayout>) -> Self {
        Self::new(FlatBfsBridge::new(layout))
    }

    /// Verify that the flat roundtrip preserves state identity for the given
    /// initial state. If the roundtrip fingerprint matches, marks this adapter
    /// as safe for BFS use (`roundtrip_verified` = true).
    ///
    /// This catches specs where string/model-value variables are classified as
    /// `Scalar` by layout inference but lose data in the i64 roundtrip
    /// (e.g., `"black"` → 0 → `SmallInt(0)`). The `is_fully_flat()` check
    /// alone is insufficient because it only tests for `Dynamic` vars.
    ///
    /// Returns `true` if the roundtrip is safe, `false` if it would corrupt data.
    ///
    /// Part of #4126.
    pub(crate) fn verify_roundtrip(
        &mut self,
        initial_state: &mut ArrayState,
        registry: &VarRegistry,
    ) -> bool {
        // Check 1: Fingerprint identity through flat roundtrip.
        let fp_ok = self
            .bridge
            .verify_roundtrip_fingerprint(initial_state, registry);
        if !fp_ok {
            self.roundtrip_verified = false;
            return false;
        }

        // Check 2: Value-level identity through flat roundtrip.
        // This catches cases where the fingerprint happens to match but the
        // reconstructed values have different types (e.g., Func → IntFunc
        // coercion, or String → SmallInt(0)). The interpreter may use
        // type-specific code paths that would fail on the wrong Value variant.
        //
        // IMPORTANT: Use `to_array_state_with_fallback` to mirror the
        // fingerprint check's semantics. Dynamic vars (Sets, Tuples, complex
        // Funcs) store a 0 placeholder in the flat buffer; reconstructing
        // without fallback produces `Value::Bool(false)` which would never
        // equal the original non-Bool value, triggering spurious FAIL warnings
        // on every spec containing Set/Tuple/Seq state vars (Fixes #4275).
        let flat = self.bridge.to_flat(initial_state);
        let roundtrip =
            match self
                .bridge
                .try_to_array_state_with_fallback(&flat, registry, initial_state)
            {
                Ok(roundtrip) => roundtrip,
                Err(_) => {
                    self.roundtrip_verified = false;
                    return false;
                }
            };
        let original_values = initial_state.values();
        let roundtrip_values = roundtrip.values();
        let values_ok = original_values.len() == roundtrip_values.len()
            && original_values
                .iter()
                .zip(roundtrip_values.iter())
                .all(|(a, b)| a == b);

        self.roundtrip_verified = values_ok;
        values_ok
    }

    /// Whether the adapter has been verified safe for BFS roundtrip.
    ///
    /// The BFS pipeline must check this before producing `Flat` queue entries.
    /// An adapter that has not been verified (or failed verification) must not
    /// be used for the flat BFS path.
    ///
    /// Part of #4126.
    #[must_use]
    pub(crate) fn roundtrip_verified(&self) -> bool {
        self.roundtrip_verified
    }

    /// Diagnose a roundtrip failure by finding the first variable whose
    /// reconstructed value differs from the original. Returns a human-readable
    /// description `(var_idx, kind_name, summary)` suitable for logging.
    ///
    /// Returns `None` when the roundtrip actually succeeds at the value level.
    ///
    /// Used by `infer_flat_state_layout` to produce actionable warnings
    /// (issue #4275): bare "FAIL" messages made it impossible to tell whether
    /// the failure was a real layout bug or a spurious symptom of a Dynamic
    /// fallback path.
    #[must_use]
    pub(crate) fn diagnose_roundtrip(
        &self,
        initial_state: &ArrayState,
        registry: &VarRegistry,
    ) -> Option<String> {
        let flat = self.bridge.to_flat(initial_state);
        let roundtrip =
            match self
                .bridge
                .try_to_array_state_with_fallback(&flat, registry, initial_state)
            {
                Ok(roundtrip) => roundtrip,
                Err(err) => return Some(format!("reconstruction failed: {err}")),
            };
        let original_values = initial_state.values();
        let roundtrip_values = roundtrip.values();

        if original_values.len() != roundtrip_values.len() {
            return Some(format!(
                "var count mismatch: original={} roundtrip={}",
                original_values.len(),
                roundtrip_values.len()
            ));
        }

        let layout = self.bridge.layout();
        for (idx, (orig, rt)) in original_values
            .iter()
            .zip(roundtrip_values.iter())
            .enumerate()
        {
            if orig != rt {
                let kind = layout
                    .iter()
                    .nth(idx)
                    .map(|vl| format!("{:?}", vl.kind))
                    .unwrap_or_else(|| "?".to_string());
                let orig_ty = value_type_tag(orig);
                let rt_ty = value_type_tag(rt);
                return Some(format!(
                    "var[{idx}] kind={kind} original_type={orig_ty} roundtrip_type={rt_ty}"
                ));
            }
        }
        None
    }

    /// Convert a `FlatState` to `ArrayState` for interpreter evaluation.
    ///
    /// For fully-flat layouts (no Dynamic vars), this is an exact conversion.
    /// For layouts with Dynamic vars, the caller must provide the `original`
    /// ArrayState to fill in the Dynamic variable values.
    ///
    /// This is the "left side" of the sandwich:
    ///   FlatState → **ArrayState** → eval → ArrayState → FlatState
    pub(crate) fn try_flat_to_array(
        &mut self,
        flat: &FlatState,
        registry: &VarRegistry,
        original: Option<&ArrayState>,
    ) -> Result<ArrayState, FlatReconstructionError> {
        self.flat_to_array_count += 1;
        if self.bridge.is_fully_flat() {
            self.bridge.try_to_array_state(flat, registry)
        } else {
            match original {
                Some(orig) => self
                    .bridge
                    .try_to_array_state_with_fallback(flat, registry, orig),
                None => self.bridge.try_to_array_state(flat, registry),
            }
        }
    }

    /// Convert a `FlatState` to `ArrayState` for interpreter evaluation.
    ///
    /// Compatibility wrapper for broad callers. New raw/native materialization
    /// paths should use [`Self::try_flat_to_array`] and propagate the error.
    pub(crate) fn flat_to_array(
        &mut self,
        flat: &FlatState,
        registry: &VarRegistry,
        original: Option<&ArrayState>,
    ) -> ArrayState {
        self.try_flat_to_array(flat, registry, original)
            .expect("FlatBfsAdapter::flat_to_array reconstruction failed")
    }

    /// Convert an `ArrayState` to `FlatState` after successor generation.
    ///
    /// This is the "right side" of the sandwich:
    ///   FlatState → ArrayState → eval → **ArrayState** → FlatState
    #[must_use]
    pub(crate) fn array_to_flat(&mut self, array: &ArrayState) -> FlatState {
        self.array_to_flat_count += 1;
        self.bridge.to_flat(array)
    }

    /// Convert an `ArrayState` to `FlatState` only if the current layout can
    /// represent this concrete state without truncation or fallback data.
    #[must_use]
    pub(crate) fn try_array_to_flat_lossless(&mut self, array: &ArrayState) -> Option<FlatState> {
        let flat =
            FlatState::try_from_array_state_lossless(array, Arc::clone(self.bridge.layout()))?;
        self.array_to_flat_count += 1;
        Some(flat)
    }

    /// Compute the traditional 64-bit `Fingerprint` from a `FlatState`.
    ///
    /// This fingerprint is compatible with the interpreter path's fingerprint
    /// and can be used for dedup in the seen-set. The conversion path is:
    ///   FlatState → ArrayState → fingerprint pipeline → Fingerprint
    ///
    /// For fully-flat layouts, the roundtrip is exact. For Dynamic layouts,
    /// the `original` ArrayState must be provided.
    pub(crate) fn try_traditional_fingerprint(
        &self,
        flat: &FlatState,
        registry: &VarRegistry,
        original: Option<&ArrayState>,
    ) -> Result<Fingerprint, FlatReconstructionError> {
        self.bridge
            .try_traditional_fingerprint(flat, registry, original)
    }

    /// Compute the traditional 64-bit `Fingerprint` from a `FlatState`.
    ///
    /// Compatibility wrapper for broad callers. New raw/native materialization
    /// paths should use [`Self::try_traditional_fingerprint`] and propagate the
    /// error.
    #[must_use]
    pub(crate) fn traditional_fingerprint(
        &self,
        flat: &FlatState,
        registry: &VarRegistry,
        original: Option<&ArrayState>,
    ) -> Fingerprint {
        self.try_traditional_fingerprint(flat, registry, original)
            .expect("FlatBfsAdapter::traditional_fingerprint reconstruction failed")
    }

    /// Compute the 128-bit flat fingerprint for fast dedup.
    ///
    /// This is faster than the traditional fingerprint (no Value roundtrip)
    /// but lives in a different hash space. Can be used for a flat-only
    /// seen-set that doesn't need to interoperate with interpreter states.
    #[must_use]
    pub(crate) fn flat_fingerprint(&self, flat: &FlatState) -> u128 {
        self.bridge.flat_fingerprint_from_flat(flat)
    }

    /// Convert a batch of ArrayState successors to FlatStates.
    ///
    /// Returns `Vec<(FlatState, Fingerprint)>` where the Fingerprint is the
    /// traditional 64-bit fingerprint for dedup compatibility.
    ///
    /// Used after the interpreter generates successors from a parent state.
    pub(crate) fn batch_convert_successors(
        &mut self,
        successors: &[(ArrayState, Fingerprint)],
    ) -> Vec<(FlatState, Fingerprint)> {
        successors
            .iter()
            .map(|(array, fp)| {
                let flat = self.array_to_flat(array);
                (flat, *fp)
            })
            .collect()
    }

    /// Whether the layout is fully flattenable (no Dynamic vars).
    ///
    /// When true, flat↔array roundtrips are exact without needing an
    /// original ArrayState fallback.
    #[must_use]
    pub(crate) fn is_fully_flat(&self) -> bool {
        self.bridge.is_fully_flat()
    }

    /// Number of i64 slots per state.
    #[must_use]
    pub(crate) fn num_slots(&self) -> usize {
        self.bridge.num_slots()
    }

    /// Bytes per flat state buffer.
    #[must_use]
    pub(crate) fn bytes_per_state(&self) -> usize {
        self.bridge.bytes_per_state()
    }

    /// Get the shared layout.
    #[must_use]
    pub(crate) fn layout(&self) -> &Arc<StateLayout> {
        self.bridge.layout()
    }

    /// Get the underlying bridge (for direct access to fingerprinting backends).
    #[must_use]
    pub(crate) fn bridge(&self) -> &FlatBfsBridge {
        &self.bridge
    }

    /// Number of flat→array conversions performed.
    #[must_use]
    pub(crate) fn flat_to_array_count(&self) -> u64 {
        self.flat_to_array_count
    }

    /// Number of array→flat conversions performed.
    #[must_use]
    pub(crate) fn array_to_flat_count(&self) -> u64 {
        self.array_to_flat_count
    }

    /// Reset conversion counters.
    pub(crate) fn reset_stats(&mut self) {
        self.flat_to_array_count = 0;
        self.array_to_flat_count = 0;
    }

    /// Log adapter statistics to stderr.
    pub(crate) fn report_stats(&self) {
        if self.flat_to_array_count > 0 || self.array_to_flat_count > 0 {
            eprintln!(
                "FlatBfsAdapter: {} flat→array, {} array→flat conversions, {} slots/state, {} bytes/state, fully_flat={}",
                self.flat_to_array_count,
                self.array_to_flat_count,
                self.num_slots(),
                self.bytes_per_state(),
                self.is_fully_flat(),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::layout_inference::infer_layout;
    use crate::Value;
    use std::sync::Arc;
    use tla_value::value::IntIntervalFunc;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_adapter_scalar_roundtrip() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y", "z"]);
        let array = ArrayState::from_values(vec![
            Value::SmallInt(42),
            Value::Bool(true),
            Value::SmallInt(-7),
        ]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);
        let mut adapter = FlatBfsAdapter::new(bridge);

        assert!(adapter.is_fully_flat());
        assert_eq!(adapter.num_slots(), 3);
        assert_eq!(adapter.bytes_per_state(), 24);

        // Convert array → flat → array roundtrip
        let flat = adapter.array_to_flat(&array);
        assert_eq!(flat.buffer(), &[42, 1, -7]);

        let restored = adapter.flat_to_array(&flat, &registry, None);
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(0)),
            Value::SmallInt(42)
        );
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(1)),
            Value::Bool(true)
        );
        assert_eq!(
            restored.get(crate::var_index::VarIndex::new(2)),
            Value::SmallInt(-7)
        );

        assert_eq!(adapter.array_to_flat_count(), 1);
        assert_eq!(adapter.flat_to_array_count(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_adapter_fingerprint_consistency() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y"]);
        let mut array = ArrayState::from_values(vec![Value::SmallInt(42), Value::SmallInt(-7)]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);
        let mut adapter = FlatBfsAdapter::new(bridge);

        let original_fp = array.fingerprint(&registry);
        let flat = adapter.array_to_flat(&array);
        let roundtrip_fp = adapter.traditional_fingerprint(&flat, &registry, None);

        assert_eq!(
            original_fp, roundtrip_fp,
            "traditional fingerprint must be preserved through flat roundtrip"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_adapter_int_array_roundtrip() {
        let registry = crate::var_index::VarRegistry::from_names(["pc", "arr"]);
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![
                Value::SmallInt(10),
                Value::SmallInt(20),
                Value::SmallInt(30),
            ],
        );
        let array =
            ArrayState::from_values(vec![Value::SmallInt(1), Value::IntFunc(Arc::new(func))]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);
        let mut adapter = FlatBfsAdapter::new(bridge);

        assert!(adapter.is_fully_flat());
        assert_eq!(adapter.num_slots(), 4); // 1 scalar + 3 array elements

        let flat = adapter.array_to_flat(&array);
        assert_eq!(flat.buffer(), &[1, 10, 20, 30]);

        let restored = adapter.flat_to_array(&flat, &registry, None);
        let val = restored.get(crate::var_index::VarIndex::new(1));
        match val {
            Value::IntFunc(ref f) => {
                assert_eq!(f.len(), 3);
                assert_eq!(f.values()[0], Value::SmallInt(10));
            }
            other => panic!("expected IntFunc, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_adapter_dynamic_var_needs_fallback() {
        use tla_value::value::SortedSet;

        let registry = crate::var_index::VarRegistry::from_names(["count", "data"]);
        let set = SortedSet::from_sorted_vec(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ]);
        let array = ArrayState::from_values(vec![Value::SmallInt(99), Value::Set(Arc::new(set))]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);
        let mut adapter = FlatBfsAdapter::new(bridge);

        assert!(!adapter.is_fully_flat());

        let flat = adapter.array_to_flat(&array);
        assert_eq!(flat.buffer()[0], 99);
        assert_eq!(flat.buffer()[1], 0); // Dynamic placeholder

        // Without fallback, dynamic var gets placeholder
        let naive = adapter.flat_to_array(&flat, &registry, None);
        assert_eq!(
            naive.get(crate::var_index::VarIndex::new(1)),
            Value::Bool(false)
        );

        // With fallback, dynamic var is preserved
        let patched = adapter.flat_to_array(&flat, &registry, Some(&array));
        let data = patched.get(crate::var_index::VarIndex::new(1));
        match data {
            Value::Set(ref s) => assert_eq!(s.len(), 3),
            other => panic!("expected Set, got {other:?}"),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_adapter_lossless_conversion_falls_back_for_sequence_over_capacity() {
        use crate::state::state_layout::{
            FlatValueLayout, SequenceBoundEvidence, SlotType, VarLayoutKind,
        };
        use tla_value::value::SeqValue;

        let registry = crate::var_index::VarRegistry::from_names(["queue"]);
        let layout = Arc::new(StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::Sequence {
                    bound: SequenceBoundEvidence::Observed,
                    max_len: 0,
                    element_layout: Box::new(FlatValueLayout::Scalar(SlotType::Int)),
                },
            }],
        ));
        let bridge = FlatBfsBridge::new(layout);
        let mut adapter = FlatBfsAdapter::new(bridge);
        let seq = |items: Vec<Value>| Value::Seq(Arc::new(SeqValue::from_vec(items)));

        let empty = ArrayState::from_values(vec![seq(vec![])]);
        assert!(adapter.try_array_to_flat_lossless(&empty).is_some());

        let nonempty = ArrayState::from_values(vec![seq(vec![Value::SmallInt(1)])]);
        assert!(
            adapter.try_array_to_flat_lossless(&nonempty).is_none(),
            "adapter must not enqueue a Flat entry that would lose sequence elements"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_adapter_recursive_sequence_invalid_raw_length_returns_error() {
        use crate::state::state_layout::{
            FlatValueLayout, SequenceBoundEvidence, SlotType, VarLayoutKind,
        };

        let registry = crate::var_index::VarRegistry::from_names(["queue"]);
        let layout = Arc::new(StateLayout::new(
            &registry,
            vec![VarLayoutKind::Recursive {
                layout: FlatValueLayout::Sequence {
                    bound: SequenceBoundEvidence::ProvenInvariant {
                        invariant: Arc::from("BoundedQueue"),
                    },
                    max_len: 1,
                    element_layout: Box::new(FlatValueLayout::Scalar(SlotType::Int)),
                },
            }],
        ));
        let bridge = FlatBfsBridge::new(Arc::clone(&layout));
        let mut adapter = FlatBfsAdapter::new(bridge);
        let flat = FlatState::from_buffer(Box::new([-1, 10]), layout);

        let err = adapter
            .try_flat_to_array(&flat, &registry, None)
            .unwrap_err();
        assert_eq!(
            err,
            FlatReconstructionError::NegativeSequenceLength { raw_len: -1 }
        );
        assert_eq!(
            adapter
                .try_traditional_fingerprint(&flat, &registry, None)
                .unwrap_err(),
            err
        );
    }

    /// Regression test for #4275: `verify_roundtrip` on a state containing a
    /// Dynamic-classified variable (Set, Tuple, Seq, complex Func) previously
    /// returned `false` unconditionally because Check 2 (value-level) used
    /// `to_array_state` without the `initial_state` fallback, producing a
    /// `Value::Bool(false)` placeholder that never matched the original Set.
    ///
    /// Fix: route Check 2 through `to_array_state_with_fallback` to match the
    /// fingerprint check's semantics. The roundtrip is correct at the eval
    /// boundary because callers always have the source ArrayState available.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_verify_roundtrip_with_dynamic_var_passes() {
        use tla_value::value::SortedSet;

        let registry = crate::var_index::VarRegistry::from_names(["count", "data"]);
        let set = SortedSet::from_sorted_vec(vec![
            Value::SmallInt(1),
            Value::SmallInt(2),
            Value::SmallInt(3),
        ]);
        let mut array =
            ArrayState::from_values(vec![Value::SmallInt(99), Value::Set(Arc::new(set))]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);
        let mut adapter = FlatBfsAdapter::new(bridge);

        assert!(!adapter.is_fully_flat());

        let ok = adapter.verify_roundtrip(&mut array, &registry);
        assert!(
            ok,
            "verify_roundtrip must succeed for Set-valued state (#4275)"
        );
        assert!(adapter.roundtrip_verified());
        // And the diagnostic helper returns None on success.
        assert!(adapter.diagnose_roundtrip(&array, &registry).is_none());
    }

    /// Covers the case where a Dynamic-producing var is not in the first init
    /// state at all — empty initial Set still roundtrips via fallback.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_verify_roundtrip_with_tuple_var_passes() {
        let registry = crate::var_index::VarRegistry::from_names(["pc", "queue"]);
        let tuple = vec![Value::SmallInt(1), Value::SmallInt(2)];
        let mut array =
            ArrayState::from_values(vec![Value::SmallInt(0), Value::Tuple(Arc::from(tuple))]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);
        let mut adapter = FlatBfsAdapter::new(bridge);

        let ok = adapter.verify_roundtrip(&mut array, &registry);
        assert!(ok, "verify_roundtrip must succeed for Tuple-valued state");
        assert!(adapter.roundtrip_verified());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_adapter_batch_convert_successors() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y"]);
        let sample = ArrayState::from_values(vec![Value::SmallInt(0), Value::SmallInt(0)]);
        let layout = Arc::new(infer_layout(&sample, &registry));
        let bridge = FlatBfsBridge::new(layout);
        let mut adapter = FlatBfsAdapter::new(bridge);

        let mut s1 = ArrayState::from_values(vec![Value::SmallInt(1), Value::SmallInt(2)]);
        let fp1 = s1.fingerprint(&registry);
        let mut s2 = ArrayState::from_values(vec![Value::SmallInt(3), Value::SmallInt(4)]);
        let fp2 = s2.fingerprint(&registry);

        let successors = vec![(s1, fp1), (s2, fp2)];
        let converted = adapter.batch_convert_successors(&successors);

        assert_eq!(converted.len(), 2);
        assert_eq!(converted[0].0.buffer(), &[1, 2]);
        assert_eq!(converted[0].1, fp1);
        assert_eq!(converted[1].0.buffer(), &[3, 4]);
        assert_eq!(converted[1].1, fp2);
        assert_eq!(adapter.array_to_flat_count(), 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_adapter_stats_and_reset() {
        let registry = crate::var_index::VarRegistry::from_names(["x"]);
        let sample = ArrayState::from_values(vec![Value::SmallInt(0)]);
        let layout = Arc::new(infer_layout(&sample, &registry));
        let bridge = FlatBfsBridge::new(layout);
        let mut adapter = FlatBfsAdapter::new(bridge);

        assert_eq!(adapter.flat_to_array_count(), 0);
        assert_eq!(adapter.array_to_flat_count(), 0);

        let flat = adapter.array_to_flat(&sample);
        let _ = adapter.flat_to_array(&flat, &registry, None);
        let _ = adapter.flat_to_array(&flat, &registry, None);

        assert_eq!(adapter.array_to_flat_count(), 1);
        assert_eq!(adapter.flat_to_array_count(), 2);

        adapter.reset_stats();
        assert_eq!(adapter.flat_to_array_count(), 0);
        assert_eq!(adapter.array_to_flat_count(), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_adapter_from_layout() {
        let registry = crate::var_index::VarRegistry::from_names(["x", "y"]);
        let sample = ArrayState::from_values(vec![Value::SmallInt(0), Value::SmallInt(0)]);
        let layout = Arc::new(infer_layout(&sample, &registry));
        let adapter = FlatBfsAdapter::from_layout(layout);

        assert!(adapter.is_fully_flat());
        assert_eq!(adapter.num_slots(), 2);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_adapter_ewd998_like_roundtrip() {
        // End-to-end test simulating the BFS sandwich for an EWD998-like spec.
        let registry =
            crate::var_index::VarRegistry::from_names(["active", "counter", "token_pos"]);
        let active = IntIntervalFunc::new(
            0,
            2,
            vec![Value::Bool(true), Value::Bool(false), Value::Bool(false)],
        );
        let counter = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(0), Value::SmallInt(0), Value::SmallInt(0)],
        );
        let mut init = ArrayState::from_values(vec![
            Value::IntFunc(Arc::new(active)),
            Value::IntFunc(Arc::new(counter)),
            Value::SmallInt(0),
        ]);
        let layout = Arc::new(infer_layout(&init, &registry));
        let bridge = FlatBfsBridge::new(layout);
        let mut adapter = FlatBfsAdapter::new(bridge);

        // Step 1: Convert init state to flat
        let flat_init = adapter.array_to_flat(&init);
        assert_eq!(flat_init.buffer(), &[1, 0, 0, 0, 0, 0, 0]);

        // Step 2: Convert back to array for eval
        let array_for_eval = adapter.flat_to_array(&flat_init, &registry, None);

        // Step 3: Simulate action (SendMsg: counter[0] -= 1, token_pos stays)
        let succ_counter = IntIntervalFunc::new(
            0,
            2,
            vec![Value::SmallInt(-1), Value::SmallInt(0), Value::SmallInt(0)],
        );
        let mut successor = ArrayState::from_values(vec![
            Value::IntFunc(Arc::new(IntIntervalFunc::new(
                0,
                2,
                vec![Value::Bool(true), Value::Bool(false), Value::Bool(false)],
            ))),
            Value::IntFunc(Arc::new(succ_counter)),
            Value::SmallInt(0),
        ]);

        // Step 4: Convert successor to flat for enqueue
        let flat_succ = adapter.array_to_flat(&successor);
        assert_eq!(flat_succ.buffer(), &[1, 0, 0, -1, 0, 0, 0]);
        assert_ne!(flat_init, flat_succ);

        // Step 5: Verify fingerprint consistency
        let fp_via_array = init.fingerprint(&registry);
        let fp_via_flat = adapter.traditional_fingerprint(&flat_init, &registry, None);
        assert_eq!(fp_via_array, fp_via_flat);

        let succ_fp_via_array = successor.fingerprint(&registry);
        let succ_fp_via_flat = adapter.traditional_fingerprint(&flat_succ, &registry, None);
        assert_eq!(succ_fp_via_array, succ_fp_via_flat);

        // Stats
        assert_eq!(adapter.array_to_flat_count(), 2);
        assert_eq!(adapter.flat_to_array_count(), 1);
    }

    /// Test the auto-detection predicates that `should_use_flat_bfs()` relies on.
    ///
    /// Verifies that:
    /// 1. Fully scalar layouts → `is_fully_flat() == true` AND roundtrip passes
    /// 2. Layouts with Dynamic vars → `is_fully_flat() == false`
    /// 3. IntArray layouts → `is_fully_flat() == true` (compound but flattenable)
    ///
    /// Part of #4126: auto-detection for scalar specs.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_flat_bfs_auto_detect_predicates() {
        // Case 1: All scalar → should auto-detect as flat
        let registry = crate::var_index::VarRegistry::from_names(["x", "y", "z"]);
        let scalar_state = ArrayState::from_values(vec![
            Value::SmallInt(42),
            Value::Bool(true),
            Value::SmallInt(-7),
        ]);
        let layout = Arc::new(infer_layout(&scalar_state, &registry));
        let bridge = FlatBfsBridge::new(layout);
        let mut adapter = FlatBfsAdapter::new(bridge);
        let mut verify = scalar_state.clone();
        let roundtrip_ok = adapter.verify_roundtrip(&mut verify, &registry);
        assert!(
            adapter.is_fully_flat(),
            "all-scalar layout must be fully flat"
        );
        assert!(roundtrip_ok, "all-scalar roundtrip must pass");
        assert!(adapter.roundtrip_verified(), "verified flag must be set");

        // Case 2: Dynamic var (set) → should NOT auto-detect
        use tla_value::value::SortedSet;
        let reg2 = crate::var_index::VarRegistry::from_names(["count", "data"]);
        let set = SortedSet::from_sorted_vec(vec![Value::SmallInt(1), Value::SmallInt(2)]);
        let dynamic_state =
            ArrayState::from_values(vec![Value::SmallInt(99), Value::Set(Arc::new(set))]);
        let layout2 = Arc::new(infer_layout(&dynamic_state, &reg2));
        let bridge2 = FlatBfsBridge::new(layout2);
        let adapter2 = FlatBfsAdapter::new(bridge2);
        assert!(
            !adapter2.is_fully_flat(),
            "dynamic layout must NOT be fully flat"
        );

        // Case 3: IntArray → should auto-detect (flattenable compound)
        let reg3 = crate::var_index::VarRegistry::from_names(["pc", "arr"]);
        let func = IntIntervalFunc::new(
            0,
            2,
            vec![
                Value::SmallInt(10),
                Value::SmallInt(20),
                Value::SmallInt(30),
            ],
        );
        let array_state =
            ArrayState::from_values(vec![Value::SmallInt(1), Value::IntFunc(Arc::new(func))]);
        let layout3 = Arc::new(infer_layout(&array_state, &reg3));
        let bridge3 = FlatBfsBridge::new(layout3);
        let mut adapter3 = FlatBfsAdapter::new(bridge3);
        let mut verify3 = array_state.clone();
        let roundtrip_ok3 = adapter3.verify_roundtrip(&mut verify3, &reg3);
        assert!(
            adapter3.is_fully_flat(),
            "IntArray layout must be fully flat"
        );
        assert!(roundtrip_ok3, "IntArray roundtrip must pass");
    }

    /// Regression test for #4278: `ScalarString` variables stored as
    /// `CompactValue` TAG_HEAP (the production path) must roundtrip through
    /// the flat buffer without being corrupted to the NameId-0 interned string.
    ///
    /// Before the fix, `compact_value_to_i64` only handled TAG_STRING (inline
    /// NameId) tags and returned 0 for TAG_HEAP strings. Reconstruction then
    /// produced `resolve_name_id(0)` which is the first-interned name ("active"
    /// in EWD840), silently breaking flat-BFS roundtrip verification.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_verify_roundtrip_scalar_string_heap_tag() {
        // EWD840-like state: scalar String variable `tcolor` = "black".
        let registry = crate::var_index::VarRegistry::from_names(["tcolor"]);
        let mut array = ArrayState::from_values(vec![Value::String(Arc::from("black"))]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);
        let mut adapter = FlatBfsAdapter::new(bridge);

        assert!(
            adapter.is_fully_flat(),
            "ScalarString layout must be fully flat"
        );
        let ok = adapter.verify_roundtrip(&mut array, &registry);
        assert!(
            ok,
            "verify_roundtrip must succeed for ScalarString with TAG_HEAP (#4278)"
        );
        assert!(adapter.roundtrip_verified());
        assert!(adapter.diagnose_roundtrip(&array, &registry).is_none());
    }

    /// Regression test for #4277: `StringKeyedArray` layout with ModelValue
    /// domain keys (e.g. `RM = {rm1, rm2, rm3}` ModelValues in 2PCwithBTM)
    /// must reconstruct keys as `Value::ModelValue`, not `Value::String`.
    ///
    /// Before the fix, `StringKeyedArray` only stored `domain_keys:
    /// Vec<Arc<str>>` and always emitted `Value::String` on reconstruction.
    /// ModelValue domains silently reconstructed as String, failing equality
    /// comparison in roundtrip verification.
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_verify_roundtrip_string_keyed_modelvalue_domain() {
        use tla_value::value::FuncValue;

        // 2PCwithBTM-like state: `rmState = [rm \in RM |-> "working"]` where
        // RM = {rm1, rm2, rm3} is a set of ModelValues.
        let registry = crate::var_index::VarRegistry::from_names(["rmState"]);
        let rm_state = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
            (
                Value::ModelValue(Arc::from("rm1")),
                Value::String(Arc::from("working")),
            ),
            (
                Value::ModelValue(Arc::from("rm2")),
                Value::String(Arc::from("working")),
            ),
            (
                Value::ModelValue(Arc::from("rm3")),
                Value::String(Arc::from("working")),
            ),
        ])));
        let mut array = ArrayState::from_values(vec![rm_state]);
        let layout = Arc::new(infer_layout(&array, &registry));
        let bridge = FlatBfsBridge::new(layout);
        let mut adapter = FlatBfsAdapter::new(bridge);

        let ok = adapter.verify_roundtrip(&mut array, &registry);
        assert!(
            ok,
            "verify_roundtrip must succeed for StringKeyedArray with ModelValue domain (#4277)"
        );
        assert!(adapter.roundtrip_verified());
        assert!(adapter.diagnose_roundtrip(&array, &registry).is_none());
    }
}
