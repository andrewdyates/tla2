// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the worker-local value fingerprinting and state management.
//!
//! Part of #3337: Verifies fingerprint parity between the shared
//! (`value_hash::value_fingerprint`) and worker-local (`WorkerFpMemo`) paths.

use std::sync::Arc;

use crate::state::value_hash::value_fingerprint as shared_value_fingerprint;
use crate::state::worker_value_hash::{WorkerArrayState, WorkerFpMemo};
use crate::state::ArrayState;
use crate::value::{FuncValue, IntIntervalFunc, SeqValue};
use crate::var_index::{VarIndex, VarRegistry};
use crate::Value;

// --- Fingerprint parity tests ---

#[test]
fn test_worker_fp_parity_bool() {
    let value = Value::Bool(true);
    let shared_fp = shared_value_fingerprint(&value);
    let mut memo = WorkerFpMemo::new();
    let worker_fp = memo.value_fingerprint(&value);
    assert_eq!(shared_fp, worker_fp, "Bool fingerprint parity");
}

#[test]
fn test_worker_fp_parity_smallint() {
    for n in [-100, -1, 0, 1, 42, 1000] {
        let value = Value::SmallInt(n);
        let shared_fp = shared_value_fingerprint(&value);
        let mut memo = WorkerFpMemo::new();
        let worker_fp = memo.value_fingerprint(&value);
        assert_eq!(shared_fp, worker_fp, "SmallInt({n}) fingerprint parity");
    }
}

#[test]
fn test_worker_fp_parity_string() {
    let value = Value::String(Arc::from("hello"));
    let shared_fp = shared_value_fingerprint(&value);
    let mut memo = WorkerFpMemo::new();
    let worker_fp = memo.value_fingerprint(&value);
    assert_eq!(shared_fp, worker_fp, "String fingerprint parity");
}

#[test]
fn test_worker_fp_parity_model_value() {
    let value = Value::ModelValue(Arc::from("mv1"));
    let shared_fp = shared_value_fingerprint(&value);
    let mut memo = WorkerFpMemo::new();
    let worker_fp = memo.value_fingerprint(&value);
    assert_eq!(shared_fp, worker_fp, "ModelValue fingerprint parity");
}

#[test]
fn test_worker_fp_parity_func() {
    let value = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), Value::Bool(true)),
        (Value::SmallInt(2), Value::Bool(false)),
        (Value::SmallInt(3), Value::String(Arc::from("x"))),
    ])));
    let shared_fp = shared_value_fingerprint(&value);
    let mut memo = WorkerFpMemo::new();
    let worker_fp = memo.value_fingerprint(&value);
    assert_eq!(shared_fp, worker_fp, "Func fingerprint parity");
}

#[test]
fn test_worker_fp_parity_int_func() {
    let value = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        3,
        vec![Value::Bool(true), Value::Bool(false), Value::SmallInt(42)],
    )));
    let shared_fp = shared_value_fingerprint(&value);
    let mut memo = WorkerFpMemo::new();
    let worker_fp = memo.value_fingerprint(&value);
    assert_eq!(shared_fp, worker_fp, "IntFunc fingerprint parity");
}

#[test]
fn test_worker_fp_parity_set() {
    let value = Value::set([Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]);
    let shared_fp = shared_value_fingerprint(&value);
    let mut memo = WorkerFpMemo::new();
    let worker_fp = memo.value_fingerprint(&value);
    assert_eq!(shared_fp, worker_fp, "Set fingerprint parity");
}

#[test]
fn test_worker_fp_parity_seq() {
    let value = Value::Seq(Arc::new(SeqValue::from(vec![
        Value::Bool(true),
        Value::SmallInt(10),
    ])));
    let shared_fp = shared_value_fingerprint(&value);
    let mut memo = WorkerFpMemo::new();
    let worker_fp = memo.value_fingerprint(&value);
    assert_eq!(shared_fp, worker_fp, "Seq fingerprint parity");
}

#[test]
fn test_worker_fp_parity_tuple() {
    let value = Value::Tuple(
        vec![
            Value::Bool(true),
            Value::SmallInt(42),
            Value::String(Arc::from("z")),
        ]
        .into(),
    );
    let shared_fp = shared_value_fingerprint(&value);
    let mut memo = WorkerFpMemo::new();
    let worker_fp = memo.value_fingerprint(&value);
    assert_eq!(shared_fp, worker_fp, "Tuple fingerprint parity");
}

#[test]
fn test_worker_fp_parity_record() {
    let value = Value::record([("x", Value::Bool(true)), ("y", Value::SmallInt(5))]);
    let shared_fp = shared_value_fingerprint(&value);
    let mut memo = WorkerFpMemo::new();
    let worker_fp = memo.value_fingerprint(&value);
    assert_eq!(shared_fp, worker_fp, "Record fingerprint parity");
}

#[test]
fn test_worker_fp_parity_nested() {
    // Nested value: Func with Set values
    let set_val = Value::set([Value::SmallInt(1), Value::SmallInt(2)]);
    let value = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::String(Arc::from("a")), set_val.clone()),
        (Value::String(Arc::from("b")), Value::Bool(false)),
    ])));
    let shared_fp = shared_value_fingerprint(&value);
    let mut memo = WorkerFpMemo::new();
    let worker_fp = memo.value_fingerprint(&value);
    assert_eq!(shared_fp, worker_fp, "Nested Func(Set) fingerprint parity");
}

// --- Round-trip tests ---

#[test]
fn test_worker_array_state_round_trip_primitives() {
    let registry = VarRegistry::from_names(["x", "y", "z"]);
    let mut state = ArrayState::new(3);
    state.set(VarIndex::new(0), Value::Bool(true));
    state.set(VarIndex::new(1), Value::SmallInt(42));
    state.set(VarIndex::new(2), Value::String(Arc::from("hello")));

    let shared_fp = state.fingerprint(&registry);

    let mut worker_state = WorkerArrayState::from_array_state(&state);
    let worker_fp = worker_state.fingerprint(&registry);

    assert_eq!(
        shared_fp, worker_fp,
        "WorkerArrayState round-trip fingerprint parity"
    );

    // Promote back to shared and verify fingerprint
    let mut promoted = worker_state.into_array_state();
    let promoted_fp = promoted.fingerprint(&registry);
    assert_eq!(
        shared_fp, promoted_fp,
        "Promoted ArrayState fingerprint parity"
    );
}

#[test]
fn test_worker_array_state_round_trip_compound() {
    let registry = VarRegistry::from_names(["f", "s", "r"]);
    let func = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), Value::Bool(true)),
        (Value::SmallInt(2), Value::Bool(false)),
    ])));
    let set = Value::set([Value::SmallInt(10), Value::SmallInt(20)]);
    let record = Value::record([("a", Value::SmallInt(1)), ("b", Value::SmallInt(2))]);

    let mut state = ArrayState::new(3);
    state.set(VarIndex::new(0), func);
    state.set(VarIndex::new(1), set);
    state.set(VarIndex::new(2), record);

    let shared_fp = state.fingerprint(&registry);

    let mut worker_state = WorkerArrayState::from_array_state(&state);
    let worker_fp = worker_state.fingerprint(&registry);

    assert_eq!(
        shared_fp, worker_fp,
        "WorkerArrayState compound round-trip fingerprint parity"
    );

    // Verify values are structurally equal (convert CompactValue → Value for comparison)
    assert_eq!(state.values().len(), worker_state.values().len());
    for (i, (orig, worker)) in state
        .materialize_values()
        .iter()
        .zip(worker_state.values().iter())
        .enumerate()
    {
        assert_eq!(
            format!("{orig:?}"),
            format!("{worker:?}"),
            "Slot {i} structural equality"
        );
    }
}

#[test]
fn test_worker_array_state_unshared_arcs() {
    use crate::state::worker_value_hash::array_state::unshare_value;

    // Verify that unshared values have different Arc pointers
    let original = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![(
        Value::SmallInt(1),
        Value::Bool(true),
    )])));
    let unshared = unshare_value(&original);

    if let (Value::Func(orig_arc), Value::Func(new_arc)) = (&original, &unshared) {
        assert_ne!(
            Arc::as_ptr(orig_arc),
            Arc::as_ptr(new_arc),
            "Unshared Func should have a different Arc pointer"
        );
    } else {
        panic!("Expected Func variants");
    }
}

#[test]
fn test_worker_fp_memo_caching() {
    // Verify memo actually caches (second call should use cached value)
    let value = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![
        (Value::SmallInt(1), Value::Bool(true)),
        (Value::SmallInt(2), Value::Bool(false)),
    ])));

    let mut memo = WorkerFpMemo::new();
    let fp1 = memo.value_fingerprint(&value);
    let fp2 = memo.value_fingerprint(&value);
    assert_eq!(fp1, fp2, "Memo should return consistent fingerprints");

    // After clear, should still produce the same result
    memo.clear();
    let fp3 = memo.value_fingerprint(&value);
    assert_eq!(fp1, fp3, "Cleared memo should recompute same fingerprint");
}
