// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cross-representation Hash/Eq contract tests.
//! When two different Value representations compare equal, they must hash identically.

use super::super::super::*;
use super::hash_value;
use std::sync::Arc;

// === Hash/Eq contract: a == b implies hash(a) == hash(b) ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_eq_contract_smallint_bigint() {
    // SmallInt(n) == Int(BigInt::from(n)) => same hash
    for n in [0i64, 1, -1, 42, i64::MIN, i64::MAX] {
        let small = Value::SmallInt(n);
        let big = Value::Int(Arc::new(BigInt::from(n)));
        assert_eq!(small, big, "equality failed for {n}");
        assert_eq!(
            hash_value(&small),
            hash_value(&big),
            "hash mismatch for SmallInt({n}) vs Int(BigInt({n}))"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_eq_contract_tuple_seq() {
    // <<1, 2>> as tuple should hash the same as <<1, 2>> as seq
    let tuple = Value::tuple([Value::int(1), Value::int(2)]);
    let seq = Value::seq([Value::int(1), Value::int(2)]);
    assert_eq!(tuple, seq);
    assert_eq!(
        hash_value(&tuple),
        hash_value(&seq),
        "Tuple and Seq with same elements should have same hash"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_eq_contract_interval_set() {
    // 1..3 should hash the same as {1, 2, 3}
    let interval = Value::Interval(Arc::new(IntervalValue::new(
        BigInt::from(1),
        BigInt::from(3),
    )));
    let set = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    assert_eq!(interval, set);
    assert_eq!(
        hash_value(&interval),
        hash_value(&set),
        "Interval 1..3 and Set {{1,2,3}} should have same hash"
    );
}

// === Cross-type Hash/Eq contract: Tuple/Seq/Func/IntFunc ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_eq_contract_tuple_func() {
    // <<10, 20>> = [1 |-> 10, 2 |-> 20] => same hash
    let tuple = Value::tuple([Value::int(10), Value::int(20)]);
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::int(10));
    fb.insert(Value::int(2), Value::int(20));
    let func = Value::Func(Arc::new(fb.build()));

    assert_eq!(tuple, func);
    assert_eq!(
        hash_value(&tuple),
        hash_value(&func),
        "Tuple and equivalent Func should have same hash"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_eq_contract_seq_func() {
    // Seq <<5, 6>> = Func [1 |-> 5, 2 |-> 6] => same hash
    let seq = Value::seq([Value::int(5), Value::int(6)]);
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::int(5));
    fb.insert(Value::int(2), Value::int(6));
    let func = Value::Func(Arc::new(fb.build()));

    assert_eq!(seq, func);
    assert_eq!(
        hash_value(&seq),
        hash_value(&func),
        "Seq and equivalent Func should have same hash"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_eq_contract_tuple_intfunc() {
    // <<10, 20>> = IntFunc(1, 2, [10, 20]) => same hash
    let tuple = Value::tuple([Value::int(10), Value::int(20)]);
    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::int(10), Value::int(20)],
    )));

    assert_eq!(tuple, intfunc);
    assert_eq!(
        hash_value(&tuple),
        hash_value(&intfunc),
        "Tuple and equivalent IntFunc should have same hash"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_eq_contract_seq_intfunc() {
    // Seq <<5, 6, 7>> = IntFunc(1, 3, [5, 6, 7]) => same hash
    let seq = Value::seq([Value::int(5), Value::int(6), Value::int(7)]);
    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        3,
        vec![Value::int(5), Value::int(6), Value::int(7)],
    )));

    assert_eq!(seq, intfunc);
    assert_eq!(
        hash_value(&seq),
        hash_value(&intfunc),
        "Seq and equivalent IntFunc should have same hash"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_eq_contract_func_intfunc() {
    // Func [1 |-> "a", 2 |-> "b"] = IntFunc(1, 2, ["a", "b"]) => same hash
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::string("a"));
    fb.insert(Value::int(2), Value::string("b"));
    let func = Value::Func(Arc::new(fb.build()));
    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::string("a"), Value::string("b")],
    )));

    assert_eq!(func, intfunc);
    assert_eq!(
        hash_value(&func),
        hash_value(&intfunc),
        "Func and equivalent IntFunc should have same hash"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_eq_contract_record_func() {
    // Record [a |-> 1, b |-> 2] = Func [\"a\" |-> 1, \"b\" |-> 2] => same hash
    let record = Value::record([("a", Value::int(1)), ("b", Value::int(2))]);
    let mut fb = FuncBuilder::new();
    fb.insert(Value::string("a"), Value::int(1));
    fb.insert(Value::string("b"), Value::int(2));
    let func = Value::Func(Arc::new(fb.build()));

    assert_eq!(record, func);
    assert_eq!(
        hash_value(&record),
        hash_value(&func),
        "Record and equivalent Func should have same hash"
    );
}

// === Four-way hash consistency: Tuple, Seq, Func, IntFunc ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_four_way_consistency() {
    // All four representations of the same function should have identical hashes
    let tuple = Value::tuple([Value::int(1), Value::int(2)]);
    let seq = Value::seq([Value::int(1), Value::int(2)]);
    let intfunc = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        1,
        2,
        vec![Value::int(1), Value::int(2)],
    )));
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::int(1));
    fb.insert(Value::int(2), Value::int(2));
    let func = Value::Func(Arc::new(fb.build()));

    let h_tuple = hash_value(&tuple);
    let h_seq = hash_value(&seq);
    let h_intfunc = hash_value(&intfunc);
    let h_func = hash_value(&func);

    assert_eq!(h_tuple, h_seq, "Tuple vs Seq hash mismatch");
    assert_eq!(h_tuple, h_intfunc, "Tuple vs IntFunc hash mismatch");
    assert_eq!(h_tuple, h_func, "Tuple vs Func hash mismatch");
}

// === Empty function-like values ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_empty_func_like_values() {
    let empty_tuple = Value::tuple(std::iter::empty::<Value>());
    let empty_seq = Value::seq(std::iter::empty::<Value>());
    let empty_func = Value::Func(Arc::new(FuncBuilder::new().build()));

    assert_eq!(empty_tuple, empty_seq);
    assert_eq!(empty_tuple, empty_func);
    assert_eq!(
        hash_value(&empty_tuple),
        hash_value(&empty_seq),
        "Empty tuple and empty seq should hash the same"
    );
    assert_eq!(
        hash_value(&empty_tuple),
        hash_value(&empty_func),
        "Empty tuple and empty func should hash the same"
    );
}
