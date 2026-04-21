// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::{IntervalValue, Value};
use num_bigint::BigInt;
use std::cmp::Ordering;
use std::sync::Arc;

// === Same-type ordering ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_bool_false_lt_true() {
    assert!(Value::bool(false) < Value::bool(true));
    assert_eq!(Value::bool(true).cmp(&Value::bool(true)), Ordering::Equal);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_int_basic() {
    assert!(Value::int(1) < Value::int(2));
    assert!(Value::int(-1) < Value::int(0));
    assert_eq!(Value::int(42).cmp(&Value::int(42)), Ordering::Equal);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_string_lexicographic() {
    assert!(Value::string("a") < Value::string("b"));
    assert!(Value::string("abc") < Value::string("abd"));
    assert!(Value::string("") < Value::string("a"));
    assert_eq!(
        Value::string("hello").cmp(&Value::string("hello")),
        Ordering::Equal
    );
}

// === Cross-type ordering ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_cross_type_bool_lt_int() {
    // Bool (type_order=0) < Int (type_order=1) < String (type_order=2)
    assert!(Value::bool(true) < Value::int(0));
    assert!(Value::int(999) < Value::string(""));
    assert!(Value::bool(false) < Value::string("z"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_smallint_equals_bigint() {
    // SmallInt(42) == Int(BigInt::from(42))
    let small = Value::int(42);
    let big = Value::Int(Arc::new(BigInt::from(42)));
    assert_eq!(small.cmp(&big), Ordering::Equal);
    assert_eq!(big.cmp(&small), Ordering::Equal);
    assert_eq!(small, big);
}

// === Set ordering ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_sets_by_cardinality_then_elements() {
    let s1 = Value::set([Value::int(1)]);
    let s2 = Value::set([Value::int(1), Value::int(2)]);
    // Smaller cardinality first
    assert!(s1 < s2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_sets_equal_cardinality_different_elements() {
    let s1 = Value::set([Value::int(1), Value::int(2)]);
    let s2 = Value::set([Value::int(1), Value::int(3)]);
    // Same cardinality, compare element-by-element
    assert_ne!(s1, s2);
    // {1, 2} < {1, 3} because 2 < 3
    assert!(s1 < s2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_empty_sets_equal() {
    let s1 = Value::set(std::iter::empty::<Value>());
    let s2 = Value::set(std::iter::empty::<Value>());
    assert_eq!(s1, s2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_interval_equal_to_equivalent_set() {
    // 1..3 should equal {1, 2, 3}
    let interval = Value::Interval(Arc::new(IntervalValue::new(
        BigInt::from(1),
        BigInt::from(3),
    )));
    let set = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    assert_eq!(interval, set);
}

// === SmallInt vs out-of-range BigInt ordering ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_smallint_vs_large_positive_bigint() {
    // Any SmallInt should be Less than a BigInt beyond i64::MAX
    let small = Value::int(i64::MAX);
    let big = Value::Int(Arc::new(BigInt::from(i64::MAX) + BigInt::from(1)));
    assert!(small < big, "i64::MAX should be < i64::MAX + 1 as BigInt");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_smallint_vs_large_negative_bigint() {
    // SmallInt should be Greater than a BigInt below i64::MIN
    let small = Value::int(i64::MIN);
    let big = Value::Int(Arc::new(BigInt::from(i64::MIN) - BigInt::from(1)));
    assert!(small > big, "i64::MIN should be > i64::MIN - 1 as BigInt");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_smallint_zero_vs_large_negative_bigint() {
    // SmallInt(0) should be Greater than any negative BigInt beyond i64 range
    let small = Value::int(0);
    let big = Value::Int(Arc::new(BigInt::from(i64::MIN) - BigInt::from(1)));
    assert!(small > big, "0 should be > large negative BigInt");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_smallint_zero_vs_large_positive_bigint() {
    let small = Value::int(0);
    let big = Value::Int(Arc::new(BigInt::from(i64::MAX) + BigInt::from(1)));
    assert!(small < big, "0 should be < large positive BigInt");
}

// === StringSet/AnySet ordering ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ordering_stringset_anyset() {
    assert_eq!(Value::StringSet.cmp(&Value::StringSet), Ordering::Equal);
    assert_eq!(Value::AnySet.cmp(&Value::AnySet), Ordering::Equal);
    assert!(
        Value::StringSet < Value::AnySet,
        "StringSet should be < AnySet"
    );
    assert!(Value::AnySet > Value::StringSet, "antisymmetry");
}
