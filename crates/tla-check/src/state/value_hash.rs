// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Value fingerprint dispatcher and re-exports for state hashing.
//!
//! Part of #3338: This module is the facade for the value hashing subsystem.
//! The actual implementations are split into focused submodules:
//! - `value_hash_additive`: Commutative additive fingerprints for compound types
//! - `value_hash_fnv`: FNV-1a recursive hash for all Value variants
//! - `value_hash_state`: State-level fingerprint computation + trace conversion
//!
//! This module retains `value_fingerprint()` (the top-level dispatcher) and
//! re-exports all public items for backward compatibility.

use crate::Value;

// Additive fingerprint functions — extracted to value_hash_additive.rs (#3338)
use super::value_hash_additive::{
    compute_func_additive_fp, compute_int_func_additive_fp, compute_interval_additive_fp,
    compute_record_additive_fp, compute_seq_additive_fp, compute_set_additive_fp,
    compute_tuple_additive_fp,
};

/// Compute the fingerprint of a single value for state-level dedup.
///
/// Part of #3168: For Func and IntFunc types, uses a commutative (additive)
/// hash instead of FP64. This enables:
/// 1. O(1) cached lookups for unchanged nested values (vs FP64's O(N) recursive walk)
/// 2. Future O(1) incremental updates for EXCEPT operations
///
/// Seq also uses additive (same as IntFunc(min=1)) for cross-type consistency.
/// For other types (Set, Record, primitives), uses FP64 with caching.
///
/// Part of #3805: SmallInt and Bool use precomputed lookup tables to eliminate
/// byte-at-a-time FP64 computation. SmallInt is the most common leaf type
/// (function/seq keys, counters, booleans encoded as ints).
///
/// Note: `tla_value::value_fingerprint` (in the tla-value crate) still uses FP64
/// for TLC-compatible TLCFP operator. This function is for state dedup only.
pub fn value_fingerprint(value: &Value) -> u64 {
    use crate::fingerprint::FP64_INIT;

    // Part of #3805: Fast path for primitives using precomputed O(1) lookup tables.
    // SmallInt and Bool are the most common leaf value types in state fingerprinting.
    // The table covers SmallInt [-256, 1023] — outside that range, fall back to
    // byte-at-a-time FP64 computation via fingerprint_extend.
    match value {
        Value::Bool(b) => return crate::fingerprint::fp64_bool_lookup(*b),
        Value::SmallInt(n) => {
            if let Some(fp) = crate::fingerprint::fp64_smallint_lookup(*n) {
                return fp;
            }
            return value
                .fingerprint_extend(FP64_INIT)
                .expect("state dedup: value fingerprint within TLC-compatible limits");
        }
        _ => {}
    }

    // Func: use additive fingerprint (commutative, supports cached nested lookups)
    if let Value::Func(func) = value {
        if let Some(cached) = func.get_additive_fp() {
            return cached;
        }
        let fp = compute_func_additive_fp(func);
        if !tla_value::parallel_readonly_value_caches_active() {
            func.cache_additive_fp(fp);
        }
        return fp;
    }

    // IntFunc: use additive fingerprint
    if let Value::IntFunc(func) = value {
        if let Some(cached) = func.get_additive_fp() {
            return cached;
        }
        let fp = compute_int_func_additive_fp(func);
        if !tla_value::parallel_readonly_value_caches_active() {
            func.cache_additive_fp(fp);
        }
        return fp;
    }

    // Part of #3246: Set uses additive fingerprint (same commutative scheme as
    // Func/IntFunc/Record). Enables O(1) incremental updates via SortedSet::insert()
    // for the PaxosCommit `msgs \cup {m}` pattern.
    if let Value::Set(set) = value {
        if let Some(cached) = set.get_additive_fp() {
            return cached;
        }
        let fp = compute_set_additive_fp(set);
        if !tla_value::parallel_readonly_value_caches_active() {
            set.cache_additive_fp(fp);
        }
        return fp;
    }

    // Part of #3278: Interval is extensionally equal to its materialized Set,
    // so state dedup must use the same additive set fingerprint.
    if let Value::Interval(interval) = value {
        return compute_interval_additive_fp(interval);
    }

    // Part of #3221: Record uses additive fingerprint (same scheme as Func/IntFunc)
    // with NameId keys. This enables O(1) incremental cache updates for nested
    // EXCEPT operations on Record fields.
    if let Value::Record(rec) = value {
        if let Some(cached) = rec.get_additive_fp() {
            return cached;
        }
        let fp = compute_record_additive_fp(rec);
        if !tla_value::parallel_readonly_value_caches_active() {
            rec.cache_additive_fp(fp);
        }
        return fp;
    }

    // Part of #3168: Seq uses additive fingerprint (same as IntFunc with min=1)
    // so that Seq([a,b,c]) and IntFunc({1→a, 2→b, 3→c}) produce identical
    // state dedup fingerprints.
    // Part of #3196: Use dedicated additive_fp cache, not the shared cached_fp
    // which is reserved for FP64 (TLC-compatible) fingerprinting.
    if let Value::Seq(seq) = value {
        if let Some(cached) = seq.get_additive_fp() {
            return cached;
        }
        let fp = compute_seq_additive_fp(seq);
        if !tla_value::parallel_readonly_value_caches_active() {
            seq.cache_additive_fp(fp);
        }
        return fp;
    }

    // Part of #3191: Tuple uses additive fingerprint (same as Seq and IntFunc with min=1).
    // TLC treats tuples and sequences as the same type (FcnRcdValue).
    // Without this, <<>> (Tuple) and the result of RemoveAt (Seq) with the same
    // content would produce different fingerprints, causing missed deduplication.
    if let Value::Tuple(elems) = value {
        return compute_tuple_additive_fp(elems);
    }

    // All other types: FP64 directly (cheap for primitives)
    value
        .fingerprint_extend(FP64_INIT)
        .expect("state dedup: value fingerprint within TLC-compatible limits")
}

// FNV-1a hash functions — extracted to value_hash_fnv.rs (#3338)
pub(crate) use super::value_hash_fnv::hash_value;

// State fingerprint functions — extracted to value_hash_state.rs (#3338)
pub(super) use super::value_hash_state::{
    combined_xor_from_array, combined_xor_from_compact_array, compact_value_fingerprint,
    compute_fingerprint, compute_fingerprint_from_min_vals,
};
pub(crate) use super::value_hash_state::{
    compute_canonical_fingerprint_from_compact_array, compute_fingerprint_from_array,
    compute_fingerprint_from_compact_array, finalize_fingerprint_xor, states_to_trace_value,
};

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Mutex, MutexGuard};
    use tla_value::{FuncValue, IntIntervalFunc, SeqValue};

    static READONLY_VALUE_CACHE_TEST_LOCK: Mutex<()> = Mutex::new(());

    /// Part of #3334: uses the public run-scoped guard to activate read-only mode.
    /// Field order matters: _run_guard drops first (teardown), then _lock (release).
    struct ReadonlyValueCacheGuard {
        _run_guard: tla_value::ParallelValueInternRunGuard,
        _lock: MutexGuard<'static, ()>,
    }

    impl ReadonlyValueCacheGuard {
        fn new() -> Self {
            let lock = READONLY_VALUE_CACHE_TEST_LOCK
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            let run_guard = tla_value::ParallelValueInternRunGuard::new(
                tla_value::SharedValueCacheMode::Readonly,
            );
            Self {
                _lock: lock,
                _run_guard: run_guard,
            }
        }
    }

    #[test]
    fn parallel_readonly_value_cache_value_hash_func_preserves_result_without_cache_write() {
        let _guard = ReadonlyValueCacheGuard::new();
        let value = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
            (Value::SmallInt(1), Value::Bool(true)),
            (Value::SmallInt(2), Value::Bool(false)),
        ])));
        let Value::Func(func) = &value else {
            panic!("expected function");
        };

        let fp1 = value_fingerprint(&value);
        let fp2 = value_fingerprint(&value);

        assert_eq!(fp1, fp2);
        assert_eq!(func.get_additive_fp(), None);
    }

    #[test]
    fn parallel_readonly_value_cache_value_hash_int_func_preserves_result_without_cache_write() {
        let _guard = ReadonlyValueCacheGuard::new();
        let value = Value::IntFunc(Arc::new(IntIntervalFunc::new(
            1,
            2,
            vec![Value::Bool(true), Value::Bool(false)],
        )));
        let Value::IntFunc(func) = &value else {
            panic!("expected int function");
        };

        let fp1 = value_fingerprint(&value);
        let fp2 = value_fingerprint(&value);

        assert_eq!(fp1, fp2);
        assert_eq!(func.get_additive_fp(), None);
    }

    #[test]
    fn parallel_readonly_value_cache_value_hash_set_preserves_result_without_cache_write() {
        let _guard = ReadonlyValueCacheGuard::new();
        let value = Value::set([Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]);
        let Value::Set(set) = &value else {
            panic!("expected set");
        };

        let fp1 = value_fingerprint(&value);
        let fp2 = value_fingerprint(&value);

        assert_eq!(fp1, fp2);
        assert_eq!(set.get_additive_fp(), None);
    }

    #[test]
    fn parallel_readonly_value_cache_value_hash_seq_preserves_result_without_cache_write() {
        let _guard = ReadonlyValueCacheGuard::new();
        let value = Value::Seq(Arc::new(SeqValue::from(vec![
            Value::Bool(true),
            Value::Bool(false),
        ])));
        let Value::Seq(seq) = &value else {
            panic!("expected sequence");
        };

        let fp1 = value_fingerprint(&value);
        let fp2 = value_fingerprint(&value);

        assert_eq!(fp1, fp2);
        assert_eq!(seq.get_additive_fp(), None);
    }

    #[test]
    fn parallel_readonly_value_cache_value_hash_record_preserves_result_without_cache_write() {
        let _guard = ReadonlyValueCacheGuard::new();
        let value = Value::record([("x", Value::Bool(true)), ("y", Value::Bool(false))]);
        let Value::Record(record) = &value else {
            panic!("expected record");
        };

        let fp1 = value_fingerprint(&value);
        let fp2 = value_fingerprint(&value);

        assert_eq!(fp1, fp2);
        assert_eq!(record.get_additive_fp(), None);
    }
}
