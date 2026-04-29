// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::{FuncBuilder, Value};
use std::cmp::Ordering;
use std::sync::Arc;

// === Tuple/Seq/Func cross-type equality ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_tuple_eq_seq_same_elements() {
    // <<1, 2, 3>> as tuple should equal <<1, 2, 3>> as seq
    let tuple = Value::tuple([Value::int(1), Value::int(2), Value::int(3)]);
    let seq = Value::seq([Value::int(1), Value::int(2), Value::int(3)]);
    assert_eq!(tuple, seq);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_tuple_ne_different_length() {
    let short = Value::tuple([Value::int(1)]);
    let long = Value::tuple([Value::int(1), Value::int(2)]);
    assert_ne!(short, long);
    assert!(short < long);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_record_equality() {
    let r1 = Value::record([("a", Value::int(1)), ("b", Value::int(2))]);
    let r2 = Value::record([("a", Value::int(1)), ("b", Value::int(2))]);
    assert_eq!(r1, r2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_record_different_keys() {
    let r1 = Value::record([("a", Value::int(1))]);
    let r2 = Value::record([("b", Value::int(1))]);
    assert_ne!(r1, r2);
}

// === Bug #179: Tuple/Seq vs Func cross-type ordering ===
// CRITICAL: These must produce the same ordering as FuncValue::cmp
// to ensure binary search works correctly in sorted sets.

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_tuple_eq_func_same_mapping() {
    // <<10, 20>> = [1 |-> 10, 2 |-> 20] in TLA+
    let tuple = Value::tuple([Value::int(10), Value::int(20)]);
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::int(10));
    fb.insert(Value::int(2), Value::int(20));
    let func = Value::Func(Arc::new(fb.build()));

    assert_eq!(
        tuple, func,
        "Tuple and Func with same mapping should be equal"
    );
    assert_eq!(tuple.cmp(&func), Ordering::Equal);
    assert_eq!(func.cmp(&tuple), Ordering::Equal);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_tuple_lt_func_different_values() {
    // <<1, 2>> vs [1 |-> 1, 2 |-> 3]: differ at second value
    let tuple = Value::tuple([Value::int(1), Value::int(2)]);
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::int(1));
    fb.insert(Value::int(2), Value::int(3));
    let func = Value::Func(Arc::new(fb.build()));

    assert!(tuple < func, "<<1,2>> should be < [1|->1, 2|->3]");
    assert!(func > tuple, "antisymmetry");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_tuple_vs_func_different_length() {
    // <<1, 2>> vs [1 |-> 1, 2 |-> 2, 3 |-> 3]: shorter < longer
    let tuple = Value::tuple([Value::int(1), Value::int(2)]);
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::int(1));
    fb.insert(Value::int(2), Value::int(2));
    fb.insert(Value::int(3), Value::int(3));
    let func = Value::Func(Arc::new(fb.build()));

    assert!(tuple < func, "shorter tuple should be < longer func");
    assert!(func > tuple, "antisymmetry");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_seq_eq_func_same_mapping() {
    // Seq <<5, 6>> = [1 |-> 5, 2 |-> 6]
    let seq = Value::seq([Value::int(5), Value::int(6)]);
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::int(5));
    fb.insert(Value::int(2), Value::int(6));
    let func = Value::Func(Arc::new(fb.build()));

    assert_eq!(seq, func, "Seq and Func with same mapping should be equal");
    assert_eq!(seq.cmp(&func), Ordering::Equal);
    assert_eq!(func.cmp(&seq), Ordering::Equal);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_record_eq_func_same_mapping() {
    // [a |-> 1, b |-> 2] as Record = [a |-> 1, b |-> 2] as Func
    let record = Value::record([("a", Value::int(1)), ("b", Value::int(2))]);
    let mut fb = FuncBuilder::new();
    fb.insert(Value::string("a"), Value::int(1));
    fb.insert(Value::string("b"), Value::int(2));
    let func = Value::Func(Arc::new(fb.build()));

    assert_eq!(
        record, func,
        "Record and Func with same string-domain mapping should be equal"
    );
    assert_eq!(record.cmp(&func), Ordering::Equal);
    assert_eq!(func.cmp(&record), Ordering::Equal);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_record_vs_func_different_values() {
    // [a |-> 1] as Record vs [a |-> 2] as Func
    let record = Value::record([("a", Value::int(1))]);
    let mut fb = FuncBuilder::new();
    fb.insert(Value::string("a"), Value::int(2));
    let func = Value::Func(Arc::new(fb.build()));

    assert!(record < func, "[a|->1] should be < [a|->2]");
    assert!(func > record, "antisymmetry");
}

// === Empty tuple/seq/func/intfunc equality ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_empty_tuple_eq_empty_seq() {
    let tuple = Value::tuple(std::iter::empty::<Value>());
    let seq = Value::seq(std::iter::empty::<Value>());
    assert_eq!(tuple, seq, "Empty tuple and empty seq should be equal");
    assert_eq!(tuple.cmp(&seq), Ordering::Equal);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_empty_func_eq_empty_tuple() {
    // Empty tuple <<>> = empty function []
    let tuple = Value::tuple(std::iter::empty::<Value>());
    let func = Value::Func(Arc::new(FuncBuilder::new().build()));
    assert_eq!(tuple, func, "Empty tuple and empty func should be equal");
    assert_eq!(tuple.cmp(&func), Ordering::Equal);
}
