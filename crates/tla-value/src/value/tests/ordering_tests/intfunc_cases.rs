// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::{FuncBuilder, IntIntervalFunc, Value};
use std::cmp::Ordering;
use std::sync::Arc;

// === Tuple/Seq vs IntFunc cross-type ordering ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_tuple_eq_intfunc_same_mapping() {
    // <<10, 20>> = IntFunc(min=1, max=2, [10, 20])
    let tuple = Value::tuple([Value::int(10), Value::int(20)]);
    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::int(10), Value::int(20)],
    )));

    assert_eq!(
        tuple, intfunc,
        "Tuple and IntFunc with same 1-based mapping should be equal"
    );
    assert_eq!(tuple.cmp(&intfunc), Ordering::Equal);
    assert_eq!(intfunc.cmp(&tuple), Ordering::Equal);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_seq_eq_intfunc_same_mapping() {
    // Seq <<5, 6, 7>> = IntFunc(min=1, max=3, [5, 6, 7])
    let seq = Value::seq([Value::int(5), Value::int(6), Value::int(7)]);
    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        3,
        vec![Value::int(5), Value::int(6), Value::int(7)],
    )));

    assert_eq!(seq, intfunc);
    assert_eq!(seq.cmp(&intfunc), Ordering::Equal);
    assert_eq!(intfunc.cmp(&seq), Ordering::Equal);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_tuple_vs_intfunc_nonunit_min() {
    // Tuple <<1, 2>> has implicit keys 1, 2
    // IntFunc(min=2, max=3, [1, 2]) has keys 2, 3
    // First key compare: 1 vs 2 => tuple < intfunc
    let tuple = Value::tuple([Value::int(1), Value::int(2)]);
    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        2,
        3,
        vec![Value::int(1), Value::int(2)],
    )));

    assert_ne!(tuple, intfunc, "Different domains should not be equal");
    assert!(
        tuple < intfunc,
        "Key 1 < key 2, so tuple should sort before intfunc"
    );
}

// === Func vs IntFunc cross-type ordering ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_func_eq_intfunc_same_mapping() {
    // Func [1 |-> "a", 2 |-> "b"] = IntFunc(1, 2, ["a", "b"])
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::string("a"));
    fb.insert(Value::int(2), Value::string("b"));
    let func = Value::Func(Arc::new(fb.build()));
    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::string("a"), Value::string("b")],
    )));

    assert_eq!(
        func, intfunc,
        "Func and IntFunc with same mapping should be equal"
    );
    assert_eq!(func.cmp(&intfunc), Ordering::Equal);
    assert_eq!(intfunc.cmp(&func), Ordering::Equal);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_func_vs_intfunc_different_values() {
    // Func [1 |-> 1] vs IntFunc(1, 1, [2])
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::int(1));
    let func = Value::Func(Arc::new(fb.build()));
    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(1, 1, vec![Value::int(2)])));

    assert!(func < intfunc, "[1|->1] should be < [1|->2]");
    assert!(intfunc > func, "antisymmetry");
}

// === IntFunc vs IntFunc ordering ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_intfunc_by_min_first() {
    // Same values, different min: should compare by min first
    let a = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::int(1), Value::int(2)],
    )));
    let b = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        2,
        3,
        vec![Value::int(1), Value::int(2)],
    )));
    assert!(a < b, "IntFunc with min=1 should be < min=2");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_intfunc_by_max_then_values() {
    // Same min, different max
    let a = Value::IntFunc(Arc::new(IntIntervalFunc::new(1, 1, vec![Value::int(1)])));
    let b = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::int(1), Value::int(2)],
    )));
    assert!(a < b, "IntFunc with max=1 should be < max=2");
}
