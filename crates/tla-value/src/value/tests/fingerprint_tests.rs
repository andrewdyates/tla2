// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FP64 fingerprint tests: value_fingerprint.rs behavior verification.
//!
//! Split from value_fingerprint.rs (#3006) to stay under the 500-line file limit.

use crate::fingerprint::{fp64_extend_i32, fp64_extend_i64, value_tags::*};
use crate::value::{FuncBuilder, IntIntervalFunc};
use crate::Value;
use std::sync::Arc;

#[test]
fn test_intfunc_fingerprint_normal_range() {
    let func = IntIntervalFunc::new(
        0,
        2,
        vec![
            Value::SmallInt(10),
            Value::SmallInt(20),
            Value::SmallInt(30),
        ],
    );
    let val = Value::IntFunc(Arc::new(func));
    let fp = val.fingerprint_extend(0).unwrap();
    assert_ne!(
        fp, 0,
        "fingerprint should be non-zero for non-empty IntFunc"
    );
}

#[test]
fn test_intfunc_fingerprint_near_i64_max_boundary() {
    let func = IntIntervalFunc::new(
        i64::MAX - 1,
        i64::MAX,
        vec![Value::SmallInt(1), Value::SmallInt(2)],
    );
    let val = Value::IntFunc(Arc::new(func));
    let fp = val.fingerprint_extend(0).unwrap();
    assert_ne!(fp, 0, "fingerprint should be non-zero for boundary IntFunc");
}

#[test]
fn test_intfunc_fingerprint_different_mins_produce_different_fps() {
    let func1 = IntIntervalFunc::new(0, 1, vec![Value::SmallInt(10), Value::SmallInt(20)]);
    let func2 = IntIntervalFunc::new(100, 101, vec![Value::SmallInt(10), Value::SmallInt(20)]);
    let fp1 = Value::IntFunc(Arc::new(func1))
        .fingerprint_extend(0)
        .unwrap();
    let fp2 = Value::IntFunc(Arc::new(func2))
        .fingerprint_extend(0)
        .unwrap();
    assert_ne!(
        fp1, fp2,
        "IntFuncs with different domains should have different fingerprints"
    );
}

// === #3006: Set fingerprint TLC ordering parity ===

#[test]
fn test_set_fingerprint_tlc_order_tuples_different_lengths() {
    // {<<2>>, <<1,2>>}: Value::Ord = [<<1,2>>, <<2>>] (lexicographic),
    // TLC compareTo = [<<2>>, <<1,2>>] (length-first).
    // The set fingerprint must use TLC order.
    let t_short = Value::tuple([Value::int(2)]);
    let t_long = Value::tuple([Value::int(1), Value::int(2)]);
    let set = Value::set([t_short.clone(), t_long.clone()]);

    let mut expected = fp64_extend_i64(0, SETENUMVALUE);
    expected = fp64_extend_i32(expected, 2); // cardinality
    expected = t_short.fingerprint_extend(expected).unwrap(); // <<2>> first (shorter)
    expected = t_long.fingerprint_extend(expected).unwrap(); // <<1,2>> second (longer)

    let actual = set.fingerprint_extend(0).unwrap();
    assert_eq!(
        actual, expected,
        "Set of tuples must fingerprint in TLC compareTo order (length-first)"
    );
}

#[test]
fn test_set_fingerprint_homogeneous_ints_unchanged() {
    // {3, 1, 2}: Value::Ord and tlc_cmp both agree for ints.
    // Fast path should apply — no re-sorting needed.
    let set = Value::set([Value::int(3), Value::int(1), Value::int(2)]);

    let mut expected = fp64_extend_i64(0, SETENUMVALUE);
    expected = fp64_extend_i32(expected, 3); // cardinality
    expected = Value::int(1).fingerprint_extend(expected).unwrap();
    expected = Value::int(2).fingerprint_extend(expected).unwrap();
    expected = Value::int(3).fingerprint_extend(expected).unwrap();

    assert_eq!(
        set.fingerprint_extend(0).unwrap(),
        expected,
        "Set of ints should fingerprint in natural order (fast path)"
    );
}

#[test]
fn test_set_fingerprint_nested_sets_different_cardinalities() {
    // {{1,2,3}, {4,5}}: TLC sorts by cardinality-first,
    // so {4,5} (card=2) < {1,2,3} (card=3).
    // Value::Ord compares element-by-element, so {1,2,3} < {4,5}.
    let small_set = Value::set([Value::int(4), Value::int(5)]);
    let big_set = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let outer = Value::set([small_set.clone(), big_set.clone()]);

    let mut expected = fp64_extend_i64(0, SETENUMVALUE);
    expected = fp64_extend_i32(expected, 2); // outer cardinality
                                             // TLC order: smaller cardinality first
    expected = small_set.fingerprint_extend(expected).unwrap(); // {4,5} card=2
    expected = big_set.fingerprint_extend(expected).unwrap(); // {1,2,3} card=3

    assert_eq!(
        outer.fingerprint_extend(0).unwrap(),
        expected,
        "Set of sets must fingerprint in TLC compareTo order (cardinality-first)"
    );
}

#[test]
fn test_set_fingerprint_empty_set() {
    // Empty set: no elements to order — should produce type tag + cardinality 0.
    let empty = Value::set(std::iter::empty::<Value>());

    let mut expected = fp64_extend_i64(0, SETENUMVALUE);
    expected = fp64_extend_i32(expected, 0);

    assert_eq!(
        empty.fingerprint_extend(0).unwrap(),
        expected,
        "Empty set fingerprint should be type tag + zero cardinality"
    );
}

#[test]
#[should_panic(expected = "Attempted to compare integer 1 with non-integer TRUE")]
fn test_set_fingerprint_mixed_bool_and_int_panics_like_tlc_normalization() {
    let mixed = Value::set([Value::Bool(true), Value::int(1)]);
    let _ = mixed.fingerprint_extend(0).unwrap();
}

// === #3006: Func fingerprint TLC ordering parity ===

#[test]
fn test_func_fingerprint_tlc_order_tuple_keys_different_lengths() {
    // Function [<<2>> |-> 10, <<1,2>> |-> 20] with tuple domain keys:
    // Value::Ord: <<1,2>> < <<2>> (lexicographic) → stored order: [(<<1,2>>,20), (<<2>>,10)]
    // TLC compareTo: <<2>> (len=1) < <<1,2>> (len=2) → fp order: [(<<2>>,10), (<<1,2>>,20)]
    // Fingerprint must use TLC order.
    let t_short = Value::tuple([Value::int(2)]);
    let t_long = Value::tuple([Value::int(1), Value::int(2)]);
    let mut fb = FuncBuilder::new();
    fb.insert(t_short.clone(), Value::int(10));
    fb.insert(t_long.clone(), Value::int(20));
    let func = Value::Func(Arc::new(fb.build()));

    // Expected: TLC order — shorter tuple first
    let mut expected = fp64_extend_i64(0, FCNRCDVALUE);
    expected = fp64_extend_i32(expected, 2); // domain size
    expected = t_short.fingerprint_extend(expected).unwrap(); // domain key <<2>>
    expected = Value::int(10).fingerprint_extend(expected).unwrap(); // value 10
    expected = t_long.fingerprint_extend(expected).unwrap(); // domain key <<1,2>>
    expected = Value::int(20).fingerprint_extend(expected).unwrap(); // value 20

    let actual = func.fingerprint_extend(0).unwrap();
    assert_eq!(
        actual, expected,
        "Function with tuple keys must fingerprint in TLC compareTo order (length-first)"
    );
}

#[test]
fn test_func_fingerprint_homogeneous_int_keys_unchanged() {
    // Function [1 |-> "a", 2 |-> "b", 3 |-> "c"]:
    // Int keys — Value::Ord and tlc_cmp agree. Fast path applies.
    let mut fb = FuncBuilder::new();
    fb.insert(Value::int(1), Value::string("a"));
    fb.insert(Value::int(2), Value::string("b"));
    fb.insert(Value::int(3), Value::string("c"));
    let func = Value::Func(Arc::new(fb.build()));

    let mut expected = fp64_extend_i64(0, FCNRCDVALUE);
    expected = fp64_extend_i32(expected, 3); // domain size
    expected = Value::int(1).fingerprint_extend(expected).unwrap();
    expected = Value::string("a").fingerprint_extend(expected).unwrap();
    expected = Value::int(2).fingerprint_extend(expected).unwrap();
    expected = Value::string("b").fingerprint_extend(expected).unwrap();
    expected = Value::int(3).fingerprint_extend(expected).unwrap();
    expected = Value::string("c").fingerprint_extend(expected).unwrap();

    assert_eq!(
        func.fingerprint_extend(0).unwrap(),
        expected,
        "Function with int keys should fingerprint in natural order (fast path)"
    );
}

#[test]
fn test_func_fingerprint_set_keys_different_cardinalities() {
    // Function [{4,5} |-> TRUE, {1,2,3} |-> FALSE]:
    // TLC compareTo: {4,5} (card=2) < {1,2,3} (card=3) (cardinality-first)
    // Value::Ord: {1,2,3} < {4,5} (element-by-element)
    let small_set = Value::set([Value::int(4), Value::int(5)]);
    let big_set = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let mut fb = FuncBuilder::new();
    fb.insert(small_set.clone(), Value::Bool(true));
    fb.insert(big_set.clone(), Value::Bool(false));
    let func = Value::Func(Arc::new(fb.build()));

    // TLC order: smaller cardinality first
    let mut expected = fp64_extend_i64(0, FCNRCDVALUE);
    expected = fp64_extend_i32(expected, 2); // domain size
    expected = small_set.fingerprint_extend(expected).unwrap(); // {4,5} card=2
    expected = Value::Bool(true).fingerprint_extend(expected).unwrap();
    expected = big_set.fingerprint_extend(expected).unwrap(); // {1,2,3} card=3
    expected = Value::Bool(false).fingerprint_extend(expected).unwrap();

    assert_eq!(
        func.fingerprint_extend(0).unwrap(),
        expected,
        "Function with set keys must fingerprint in TLC compareTo order (cardinality-first)"
    );
}

#[test]
fn test_func_fingerprint_empty_function() {
    // Empty function: type tag + domain size 0.
    let func = Value::Func(Arc::new(FuncBuilder::new().build()));

    let mut expected = fp64_extend_i64(0, FCNRCDVALUE);
    expected = fp64_extend_i32(expected, 0);

    assert_eq!(
        func.fingerprint_extend(0).unwrap(),
        expected,
        "Empty function fingerprint should be type tag + zero domain size"
    );
}
