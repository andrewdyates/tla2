// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Distinctness, stability, and order-independence smoke tests for Value hashing.

use super::super::super::*;
use super::hash_value;

// === Distinctness: unequal values should (usually) have different hashes ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_distinct_different_ints() {
    // Different integers should produce different hashes
    // (Not guaranteed but statistically near-certain)
    let h1 = hash_value(&Value::int(1));
    let h2 = hash_value(&Value::int(2));
    let h3 = hash_value(&Value::int(3));
    assert_ne!(h1, h2);
    assert_ne!(h2, h3);
    assert_ne!(h1, h3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_distinct_different_strings() {
    let h1 = hash_value(&Value::string("a"));
    let h2 = hash_value(&Value::string("b"));
    let h3 = hash_value(&Value::string("ab"));
    assert_ne!(h1, h2);
    assert_ne!(h1, h3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_distinct_different_types() {
    // Bool, Int, String with "similar" content should hash differently
    let bool_true = hash_value(&Value::bool(true));
    let int_one = hash_value(&Value::int(1));
    let string_one = hash_value(&Value::string("1"));
    assert_ne!(bool_true, int_one);
    assert_ne!(int_one, string_one);
    assert_ne!(bool_true, string_one);
}

// === Stability: same value always produces same hash ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_stability_same_value_twice() {
    let values = vec![
        Value::bool(true),
        Value::int(42),
        Value::string("hello"),
        Value::set([Value::int(1), Value::int(2)]),
        Value::tuple([Value::int(1)]),
        Value::record([("x", Value::int(1))]),
    ];

    for v in &values {
        let h1 = hash_value(v);
        let h2 = hash_value(v);
        assert_eq!(h1, h2, "Hash not stable for {v:?}");
    }
}

// === Edge cases ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_empty_set_and_empty_tuple() {
    // Empty set and empty tuple are NOT equal (different types)
    let empty_set = Value::set(std::iter::empty::<Value>());
    let empty_tuple = Value::tuple(std::iter::empty::<Value>());
    assert_ne!(empty_set, empty_tuple);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_set_order_independence() {
    // Sets constructed in different order should hash the same
    let s1 = Value::set([Value::int(3), Value::int(1), Value::int(2)]);
    let s2 = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    assert_eq!(s1, s2);
    assert_eq!(hash_value(&s1), hash_value(&s2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_record_field_order_independence() {
    // Records with same fields in different insertion order should hash the same
    let r1 = Value::record([("b", Value::int(2)), ("a", Value::int(1))]);
    let r2 = Value::record([("a", Value::int(1)), ("b", Value::int(2))]);
    assert_eq!(r1, r2);
    assert_eq!(hash_value(&r1), hash_value(&r2));
}
