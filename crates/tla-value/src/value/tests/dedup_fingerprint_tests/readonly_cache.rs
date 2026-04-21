// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Readonly-cache mode tests: verify that fingerprint reads do not write
//! cached state when parallel readonly caches are enabled.

use crate::value::FuncValue;
use crate::{IntIntervalFunc, Value};
use std::sync::{Arc, Mutex, MutexGuard};

use super::state_value_fingerprint_unwrap;

static READONLY_VALUE_CACHE_TEST_LOCK: Mutex<()> = Mutex::new(());

/// Part of #3334: uses the public run-scoped guard to activate read-only mode.
/// Field order matters: _run_guard drops first (teardown), then _lock (release).
struct ReadonlyValueCacheGuard {
    _run_guard: crate::ParallelValueInternRunGuard,
    _lock: MutexGuard<'static, ()>,
}

impl ReadonlyValueCacheGuard {
    fn new() -> Self {
        let lock = READONLY_VALUE_CACHE_TEST_LOCK
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let run_guard =
            crate::ParallelValueInternRunGuard::new(crate::SharedValueCacheMode::Readonly);
        Self {
            _run_guard: run_guard,
            _lock: lock,
        }
    }
}

#[test]
fn parallel_readonly_value_cache_additive_func_preserves_result_without_cache_write() {
    let _guard = ReadonlyValueCacheGuard::new();
    let value = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), Value::Bool(true)),
        (Value::SmallInt(2), Value::Bool(false)),
    ])));
    let Value::Func(func) = &value else {
        panic!("expected function");
    };

    let fp1 = state_value_fingerprint_unwrap(&value);
    let fp2 = state_value_fingerprint_unwrap(&value);

    assert_eq!(fp1, fp2);
    assert_eq!(func.get_additive_fp(), None);
}

#[test]
fn parallel_readonly_value_cache_additive_int_func_preserves_result_without_cache_write() {
    let _guard = ReadonlyValueCacheGuard::new();
    let value = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::Bool(true), Value::Bool(false)],
    )));
    let Value::IntFunc(func) = &value else {
        panic!("expected int function");
    };

    let fp1 = state_value_fingerprint_unwrap(&value);
    let fp2 = state_value_fingerprint_unwrap(&value);

    assert_eq!(fp1, fp2);
    assert_eq!(func.get_additive_fp(), None);
}

#[test]
fn parallel_readonly_value_cache_additive_set_preserves_result_without_cache_write() {
    let _guard = ReadonlyValueCacheGuard::new();
    let value = Value::set([Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]);
    let Value::Set(set) = &value else {
        panic!("expected set");
    };

    let fp1 = state_value_fingerprint_unwrap(&value);
    let fp2 = state_value_fingerprint_unwrap(&value);

    assert_eq!(fp1, fp2);
    assert_eq!(set.get_additive_fp(), None);
}

#[test]
fn parallel_readonly_value_cache_additive_seq_preserves_result_without_cache_write() {
    let _guard = ReadonlyValueCacheGuard::new();
    let value = Value::Seq(Arc::new(crate::SeqValue::from(vec![
        Value::Bool(true),
        Value::Bool(false),
    ])));
    let Value::Seq(seq) = &value else {
        panic!("expected sequence");
    };

    let fp1 = state_value_fingerprint_unwrap(&value);
    let fp2 = state_value_fingerprint_unwrap(&value);

    assert_eq!(fp1, fp2);
    assert_eq!(seq.get_additive_fp(), None);
}

#[test]
fn parallel_readonly_value_cache_additive_record_preserves_result_without_cache_write() {
    let _guard = ReadonlyValueCacheGuard::new();
    let value = Value::record([("x", Value::Bool(true)), ("y", Value::Bool(false))]);
    let Value::Record(record) = &value else {
        panic!("expected record");
    };

    let fp1 = state_value_fingerprint_unwrap(&value);
    let fp2 = state_value_fingerprint_unwrap(&value);

    assert_eq!(fp1, fp2);
    assert_eq!(record.get_additive_fp(), None);
}
