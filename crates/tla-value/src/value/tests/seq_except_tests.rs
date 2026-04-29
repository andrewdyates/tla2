// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for SeqValue::except() and except_if_changed() methods.
//!
//! These methods are critical correctness paths for TLA+ EXCEPT on sequences.
//! The model checker's inner loop uses them to compute successor states,
//! so bugs here would cause incorrect state exploration.
//! Part of #3031.

use std::sync::Arc;

use crate::value::seq::SeqValue;
use crate::value::{
    clear_string_intern_table, clear_tlc_string_tokens, lock_intern_state, FuncValue, Value,
};

#[test]
fn test_seq_except_updates_single_element() {
    let s = SeqValue::from_vec(vec![
        Value::SmallInt(10),
        Value::SmallInt(20),
        Value::SmallInt(30),
    ]);

    let result = s.except(1, Value::SmallInt(99));

    assert_eq!(result.len(), 3);
    assert_eq!(result[0], Value::SmallInt(10));
    assert_eq!(result[1], Value::SmallInt(99));
    assert_eq!(result[2], Value::SmallInt(30));
}

#[test]
fn test_seq_except_does_not_mutate_original() {
    let s = SeqValue::from_vec(vec![
        Value::SmallInt(10),
        Value::SmallInt(20),
        Value::SmallInt(30),
    ]);

    let _result = s.except(1, Value::SmallInt(99));

    // Original must be unchanged (im::Vector structural sharing)
    assert_eq!(s[0], Value::SmallInt(10));
    assert_eq!(
        s[1],
        Value::SmallInt(20),
        "original element must be unchanged"
    );
    assert_eq!(s[2], Value::SmallInt(30));
}

#[test]
fn test_seq_except_first_element() {
    let s = SeqValue::from_vec(vec![
        Value::SmallInt(1),
        Value::SmallInt(2),
        Value::SmallInt(3),
    ]);

    let result = s.except(0, Value::SmallInt(99));
    assert_eq!(result[0], Value::SmallInt(99));
    assert_eq!(result[1], Value::SmallInt(2));
    assert_eq!(result[2], Value::SmallInt(3));
}

#[test]
fn test_seq_except_last_element() {
    let s = SeqValue::from_vec(vec![
        Value::SmallInt(1),
        Value::SmallInt(2),
        Value::SmallInt(3),
    ]);

    let result = s.except(2, Value::SmallInt(99));
    assert_eq!(result[0], Value::SmallInt(1));
    assert_eq!(result[1], Value::SmallInt(2));
    assert_eq!(result[2], Value::SmallInt(99));
}

#[test]
fn test_seq_except_if_changed_returns_updated_when_different() {
    let s = SeqValue::from_vec(vec![Value::SmallInt(10), Value::SmallInt(20)]);

    let result = s.except_if_changed(0, Value::SmallInt(99));

    assert_eq!(result[0], Value::SmallInt(99));
    assert_eq!(result[1], Value::SmallInt(20));
    // Original unchanged
    assert_eq!(s[0], Value::SmallInt(10));
}

#[test]
fn test_seq_except_if_changed_short_circuits_when_same() {
    // Use enough elements to exceed im::Vector's InlineArray threshold.
    // Inline vectors (≤2-3 elements for Value-sized types) are value-copied
    // on clone, so ptr_eq always returns false. With ≥8 elements the vector
    // is heap-allocated (Single variant) and clone shares the same PoolRef.
    let s = SeqValue::from_vec((0..8).map(|i| Value::SmallInt(i)).collect());

    let result = s.except_if_changed(0, Value::SmallInt(0));

    // Value unchanged, so result should share the same backing im::Vector
    assert!(
        result.ptr_eq(&s),
        "except_if_changed with same value should share storage"
    );
    assert_eq!(result[0], Value::SmallInt(0));
    assert_eq!(result[7], Value::SmallInt(7));
}

#[test]
fn test_seq_except_invalidates_fingerprint_cache() {
    let s = SeqValue::from_vec(vec![Value::SmallInt(1), Value::SmallInt(2)]);

    // Force a fingerprint computation to populate the cache
    let _ = crate::fingerprint::value_fingerprint(&Value::Seq(Arc::new(s.clone()))).unwrap();

    let result = s.except(0, Value::SmallInt(99));

    // The result's fingerprint cache should be unset (u64::MAX sentinel)
    // We can verify this by checking that result and original have different fingerprints
    let fp_orig = crate::fingerprint::value_fingerprint(&Value::Seq(Arc::new(s))).unwrap();
    let fp_result = crate::fingerprint::value_fingerprint(&Value::Seq(Arc::new(result))).unwrap();
    assert_ne!(
        fp_orig, fp_result,
        "different sequences must have different fingerprints"
    );
}

#[test]
fn test_seq_except_single_element_seq() {
    let s = SeqValue::from_vec(vec![Value::SmallInt(42)]);

    let result = s.except(0, Value::SmallInt(7));
    assert_eq!(result.len(), 1);
    assert_eq!(result[0], Value::SmallInt(7));
    // Original unchanged
    assert_eq!(s[0], Value::SmallInt(42));
}

fn sample_func() -> FuncValue {
    FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), Value::Bool(true)),
        (Value::SmallInt(2), Value::Bool(false)),
    ])
}

fn sample_string_domain_func() -> FuncValue {
    let beta = Value::string("beta");
    let alpha = Value::string("alpha");
    FuncValue::from_sorted_entries(vec![(alpha, Value::Bool(true)), (beta, Value::Bool(false))])
}

#[test]
fn test_func_except_same_value_reuses_storage() {
    let func = sample_func();

    let result = func.clone().except(Value::SmallInt(1), Value::Bool(true));

    assert!(result.ptr_eq(&func));
}

#[test]
fn test_func_except_out_of_domain_reuses_storage() {
    let func = sample_func();

    let result = func.clone().except(Value::SmallInt(99), Value::Bool(true));

    assert!(result.ptr_eq(&func));
}

#[test]
fn test_func_except_changed_value_clones_only_values_when_shared() {
    let func = sample_func();
    let domain_ptr = func.domain_ptr();
    let values_ptr = func.values_ptr();

    let result = func.clone().except(Value::SmallInt(1), Value::Bool(false));

    // Part of #3371: With lazy overlay, ptr_eq returns false because the
    // overlay is non-empty, even though the underlying buffers are shared.
    assert!(!result.ptr_eq(&func));
    assert_eq!(
        result.domain_ptr(),
        domain_ptr,
        "EXCEPT should share the immutable domain buffer"
    );
    // Part of #3371: With lazy overlay, the values buffer is shared (not
    // cloned). The delta is stored in the overlay instead of COW-cloning.
    assert_eq!(
        result.values_ptr(),
        values_ptr,
        "overlay EXCEPT should share the values buffer (delta in overlay)"
    );
    assert!(
        result.has_overlay(),
        "overlay EXCEPT should activate the overlay"
    );
    assert_eq!(result.apply(&Value::SmallInt(1)), Some(&Value::Bool(false)));

    assert_eq!(func.apply(&Value::SmallInt(1)), Some(&Value::Bool(true)));
}

#[test]
fn test_func_except_changed_value_keeps_values_buffer_when_unique() {
    let func = sample_func();
    let domain_ptr = func.domain_ptr();
    let before_ptr = func.values_ptr();

    let result = func.except(Value::SmallInt(1), Value::Bool(false));

    assert_eq!(result.domain_ptr(), domain_ptr);
    assert_eq!(result.values_ptr(), before_ptr);
    assert_eq!(result.apply(&Value::SmallInt(1)), Some(&Value::Bool(false)));
}

#[test]
fn test_func_except_preserves_tlc_order_cache_when_shared() {
    let _guard = lock_intern_state();
    clear_string_intern_table();
    clear_tlc_string_tokens();

    let func = sample_string_domain_func();
    let cached_order: Arc<[usize]> = vec![1, 0].into();
    func.cache_tlc_normalized_order(Arc::clone(&cached_order));

    let result = func
        .clone()
        .except(Value::string("alpha"), Value::Bool(false));

    assert_eq!(result.tlc_normalized_order(), Some(cached_order.as_ref()));
    assert_eq!(func.tlc_normalized_order(), Some(cached_order.as_ref()));

    clear_tlc_string_tokens();
    clear_string_intern_table();
}

#[test]
fn test_func_except_preserves_tlc_order_cache_when_unique() {
    let _guard = lock_intern_state();
    clear_string_intern_table();
    clear_tlc_string_tokens();

    let func = sample_string_domain_func();
    let cached_order: Arc<[usize]> = vec![1, 0].into();
    func.cache_tlc_normalized_order(Arc::clone(&cached_order));

    let result = func.except(Value::string("alpha"), Value::Bool(false));

    assert_eq!(result.tlc_normalized_order(), Some(cached_order.as_ref()));

    clear_tlc_string_tokens();
    clear_string_intern_table();
}

#[cfg(feature = "memory-stats")]
#[test]
fn test_func_except_memory_stats_count_shared_clone() {
    use std::sync::atomic::Ordering;

    use crate::value::memory_stats::{reset, FUNC_EXCEPT_CLONE_COUNT, FUNC_EXCEPT_COUNT};

    reset();
    let func = sample_func();

    let result = func.clone().except(Value::SmallInt(1), Value::Bool(false));

    assert_eq!(result.apply(&Value::SmallInt(1)), Some(&Value::Bool(false)));
    assert_eq!(FUNC_EXCEPT_COUNT.load(Ordering::Relaxed), 1);
    assert_eq!(FUNC_EXCEPT_CLONE_COUNT.load(Ordering::Relaxed), 1);
}

// === IntIntervalFunc take_at / restore_at tests (Part of #3073) ===

#[test]
fn test_int_func_take_at_in_domain() {
    use crate::value::IntIntervalFunc;
    let mut f = IntIntervalFunc::new(1, 3, vec![Value::int(10), Value::int(20), Value::int(30)]);
    let (old_val, pos, _old_entry_hash) = f.take_at(&Value::int(2)).expect("key 2 in domain");
    assert_eq!(old_val, Value::int(20));
    assert_eq!(pos, 1); // array index for key 2 with min=1
                        // After take, slot holds placeholder
    assert_eq!(f.apply(&Value::int(2)), Some(&Value::Bool(false)));
}

#[test]
fn test_int_func_take_restore_roundtrip() {
    use crate::value::IntIntervalFunc;
    let mut f = IntIntervalFunc::new(1, 3, vec![Value::int(10), Value::int(20), Value::int(30)]);
    let (old_val, pos, old_entry_hash) = f.take_at(&Value::int(2)).unwrap();
    assert_eq!(old_val, Value::int(20));
    // Restore with a new value
    f.restore_at(pos, old_entry_hash, Value::int(99));
    assert_eq!(f.apply(&Value::int(1)), Some(&Value::int(10)));
    assert_eq!(f.apply(&Value::int(2)), Some(&Value::int(99)));
    assert_eq!(f.apply(&Value::int(3)), Some(&Value::int(30)));
}

#[test]
fn test_int_func_take_at_out_of_domain() {
    use crate::value::IntIntervalFunc;
    let mut f = IntIntervalFunc::new(1, 3, vec![Value::int(10), Value::int(20), Value::int(30)]);
    assert!(f.take_at(&Value::int(0)).is_none());
    assert!(f.take_at(&Value::int(4)).is_none());
    assert!(f.take_at(&Value::Bool(true)).is_none());
}

#[test]
fn test_int_func_take_restore_preserves_cow() {
    use crate::value::IntIntervalFunc;
    let f = IntIntervalFunc::new(1, 2, vec![Value::int(10), Value::int(20)]);
    // Clone to create shared reference (refcount = 2)
    let mut f2 = f.clone();
    let (old_val, pos, old_entry_hash) = f2.take_at(&Value::int(1)).unwrap();
    assert_eq!(old_val, Value::int(10));
    f2.restore_at(pos, old_entry_hash, Value::int(99));
    // f2 should have the update
    assert_eq!(f2.apply(&Value::int(1)), Some(&Value::int(99)));
    // Original f should be unchanged (COW cloned the Vec)
    assert_eq!(f.apply(&Value::int(1)), Some(&Value::int(10)));
}
