// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Function-like additive cache preservation and nested-overflow propagation tests.
//!
//! Part of #3168: additive state-dedup fingerprints must propagate nested errors
//! and preserve cached values across targeted updates for function-like containers.

use crate::dedup_fingerprint::state_value_fingerprint;
use crate::value::FuncValue;
use crate::{IntIntervalFunc, KSubsetValue, Value};
use std::sync::Arc;

use super::state_value_fingerprint_unwrap;

fn cache_func_state_fp(func: &FuncValue) -> u64 {
    let fp = state_value_fingerprint_unwrap(&Value::Func(Arc::new(func.clone())));
    func.cache_additive_fp(fp);
    fp
}

fn cache_int_func_state_fp(func: &IntIntervalFunc) -> u64 {
    let fp = state_value_fingerprint_unwrap(&Value::IntFunc(Arc::new(func.clone())));
    func.cache_additive_fp(fp);
    fp
}

fn sample_inner_bool_func(true_at_one: bool) -> FuncValue {
    FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), Value::Bool(true_at_one)),
        (Value::SmallInt(2), Value::Bool(false)),
    ])
}

fn oversized_ksubset_value() -> Value {
    // Use a non-enumerable base (StringSet) so to_sorted_set() returns None
    // and fingerprinting falls through to the structural path, where
    // fp_usize_to_i32(k, "k-subset size") triggers I32Overflow.
    // Previous version used `Value::set([Value::SmallInt(1)])` which is
    // enumerable — k > |base| just produces an empty set, bypassing overflow.
    Value::KSubset(KSubsetValue::new(Value::StringSet, (i32::MAX as usize) + 1))
}

fn assert_nested_overflow(value: Value) {
    let err = state_value_fingerprint(&value)
        .expect_err("nested overflow values should return FingerprintError, not panic");
    assert!(
        matches!(
            err,
            crate::value::value_fingerprint::FingerprintError::I32Overflow {
                context: "k-subset size",
                ..
            }
        ),
        "expected k-subset overflow, got {err:?}",
    );
}

#[test]
fn test_func_additive_fingerprint_propagates_nested_overflow_error() {
    assert_nested_overflow(Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), oversized_ksubset_value()),
    ]))));
}

#[test]
fn test_func_additive_fingerprint_propagates_nested_key_overflow_error() {
    assert_nested_overflow(Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (oversized_ksubset_value(), Value::Bool(true)),
    ]))));
}

#[test]
fn test_int_func_additive_fingerprint_propagates_nested_overflow_error() {
    assert_nested_overflow(Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        1,
        vec![oversized_ksubset_value()],
    ))));
}

#[test]
fn test_seq_additive_fingerprint_propagates_nested_overflow_error() {
    assert_nested_overflow(Value::Seq(Arc::new(crate::SeqValue::from(vec![
        oversized_ksubset_value(),
    ]))));
}

#[test]
fn test_record_additive_fingerprint_propagates_nested_overflow_error() {
    assert_nested_overflow(Value::record([("overflow", oversized_ksubset_value())]));
}

#[test]
fn test_tuple_additive_fingerprint_propagates_nested_overflow_error() {
    assert_nested_overflow(Value::Tuple(vec![oversized_ksubset_value()].into()));
}

#[test]
fn test_func_except_updates_cached_additive_fingerprint() {
    let outer = FuncValue::from_sorted_entries(vec![
        (
            Value::SmallInt(1),
            Value::Func(Arc::new(sample_inner_bool_func(true))),
        ),
        (Value::SmallInt(2), Value::Bool(true)),
    ]);
    let original_fp = cache_func_state_fp(&outer);
    let updated_inner = sample_inner_bool_func(true).except(Value::SmallInt(1), Value::Bool(false));

    let updated = outer.clone().except(
        Value::SmallInt(1),
        Value::Func(Arc::new(updated_inner.clone())),
    );

    let expected = state_value_fingerprint_unwrap(&Value::Func(Arc::new(
        FuncValue::from_sorted_entries(vec![
            (Value::SmallInt(1), Value::Func(Arc::new(updated_inner))),
            (Value::SmallInt(2), Value::Bool(true)),
        ]),
    )));

    assert_eq!(outer.get_additive_fp(), Some(original_fp));
    assert_eq!(updated.get_additive_fp(), Some(expected));
}

#[test]
fn test_func_take_restore_updates_cached_additive_fingerprint() {
    let mut outer = FuncValue::from_sorted_entries(vec![
        (
            Value::SmallInt(1),
            Value::Func(Arc::new(sample_inner_bool_func(true))),
        ),
        (Value::SmallInt(2), Value::Bool(true)),
    ]);
    cache_func_state_fp(&outer);
    let (old_val, pos, old_entry_hash, source) =
        outer.take_at(&Value::SmallInt(1)).expect("key 1 in domain");
    let Value::Func(ref inner) = old_val else {
        panic!("expected nested function");
    };
    let updated_inner =
        Arc::unwrap_or_clone(Arc::clone(inner)).except(Value::SmallInt(1), Value::Bool(false));
    outer.restore_at(
        pos,
        old_entry_hash,
        source,
        Value::Func(Arc::new(updated_inner.clone())),
    );

    let expected = state_value_fingerprint_unwrap(&Value::Func(Arc::new(
        FuncValue::from_sorted_entries(vec![
            (Value::SmallInt(1), Value::Func(Arc::new(updated_inner))),
            (Value::SmallInt(2), Value::Bool(true)),
        ]),
    )));
    assert_eq!(outer.get_additive_fp(), Some(expected));
}

#[test]
fn test_int_func_except_updates_cached_additive_fingerprint() {
    let func = IntIntervalFunc::new(
        1,
        2,
        vec![
            Value::Func(Arc::new(sample_inner_bool_func(true))),
            Value::Bool(true),
        ],
    );
    let original_fp = cache_int_func_state_fp(&func);
    let updated_inner = sample_inner_bool_func(true).except(Value::SmallInt(1), Value::Bool(false));

    let updated = func.clone().except(
        Value::SmallInt(1),
        Value::Func(Arc::new(updated_inner.clone())),
    );

    let expected = state_value_fingerprint_unwrap(&Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::Func(Arc::new(updated_inner)), Value::Bool(true)],
    ))));

    assert_eq!(func.get_additive_fp(), Some(original_fp));
    assert_eq!(updated.get_additive_fp(), Some(expected));
}

#[test]
fn test_int_func_take_restore_updates_cached_additive_fingerprint() {
    let mut func = IntIntervalFunc::new(
        1,
        2,
        vec![
            Value::Func(Arc::new(sample_inner_bool_func(true))),
            Value::Bool(true),
        ],
    );
    cache_int_func_state_fp(&func);
    let (old_val, pos, old_entry_hash) =
        func.take_at(&Value::SmallInt(1)).expect("key 1 in domain");
    let Value::Func(ref inner) = old_val else {
        panic!("expected nested function");
    };
    let updated_inner =
        Arc::unwrap_or_clone(Arc::clone(inner)).except(Value::SmallInt(1), Value::Bool(false));
    func.restore_at(
        pos,
        old_entry_hash,
        Value::Func(Arc::new(updated_inner.clone())),
    );

    let expected = state_value_fingerprint_unwrap(&Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::Func(Arc::new(updated_inner)), Value::Bool(true)],
    ))));
    assert_eq!(func.get_additive_fp(), Some(expected));
}

// Part of #3386: overlay-aware take_at / restore_at tests.

#[test]
fn test_func_take_at_overlay_returns_overlay_source() {
    use crate::FuncTakeSource;
    // Build base: {1 -> TRUE, 2 -> FALSE}
    let base = FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), Value::Bool(true)),
        (Value::SmallInt(2), Value::Bool(false)),
    ]);
    // Apply an overlay at key 1: overrides TRUE -> FALSE
    let mut func = base.except(Value::SmallInt(1), Value::Bool(false));

    // take_at(key=1) should pull from the overlay, not the base
    let (val, idx, _hash, source) = func.take_at(&Value::SmallInt(1)).unwrap();
    assert_eq!(val, Value::Bool(false), "should get the overlay value");
    assert_eq!(idx, 0);
    assert_eq!(source, FuncTakeSource::Overlay);

    // Restore with modified value — should go back into the overlay
    func.restore_at(idx, _hash, source, Value::Bool(true));

    // After restore, reading key 1 should give the restored value
    assert_eq!(*func.apply(&Value::SmallInt(1)).unwrap(), Value::Bool(true));
}

#[test]
fn test_func_take_at_base_returns_base_source() {
    use crate::FuncTakeSource;
    // Build base: {1 -> TRUE, 2 -> FALSE}
    let base = FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), Value::Bool(true)),
        (Value::SmallInt(2), Value::Bool(false)),
    ]);
    // Apply overlay at key 1 only — key 2 stays in base
    let mut func = base.except(Value::SmallInt(1), Value::Bool(false));

    // take_at(key=2) should come from the base array
    let (val, idx, _hash, source) = func.take_at(&Value::SmallInt(2)).unwrap();
    assert_eq!(val, Value::Bool(false), "should get the base value");
    assert_eq!(idx, 1);
    assert_eq!(source, FuncTakeSource::Base);

    // Restore to base
    func.restore_at(idx, _hash, source, Value::Bool(true));
    assert_eq!(*func.apply(&Value::SmallInt(2)).unwrap(), Value::Bool(true));
}

#[test]
fn test_func_overlay_take_restore_preserves_fingerprint() {
    use crate::FuncTakeSource;
    // Build base with nested function, then overlay to create lazy state
    let inner = FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), Value::Bool(true)),
        (Value::SmallInt(2), Value::Bool(false)),
    ]);
    let base = FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), Value::Func(Arc::new(inner))),
        (Value::SmallInt(2), Value::Bool(true)),
    ]);
    // Overlay at key 2 to leave key 1 in base
    let updated_inner = FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), Value::Bool(false)),
        (Value::SmallInt(2), Value::Bool(false)),
    ]);
    let mut func = base.except(
        Value::SmallInt(1),
        Value::Func(Arc::new(updated_inner.clone())),
    );
    let original_fp = cache_func_state_fp(&func);

    // Take from overlay (key 1 was overridden)
    let (old_val, pos, old_entry_hash, source) = func.take_at(&Value::SmallInt(1)).unwrap();
    assert_eq!(source, FuncTakeSource::Overlay);

    // Restore same value — fingerprint should be preserved exactly
    func.restore_at(pos, old_entry_hash, source, old_val);
    assert_eq!(func.get_additive_fp(), Some(original_fp));
}
