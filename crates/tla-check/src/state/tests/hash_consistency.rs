// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Cross-implementation hash consistency tests.
//!
//! Part of #2037: validates that the three independent hashing implementations
//! (std Hash, FNV-1a, FP64 fingerprint) and the additive fingerprint maintain
//! the equality contract: if v1 == v2, then hash(v1) == hash(v2).
//!
//! Also validates determinism: calling the same hash function twice on the
//! same value produces the same result.

use super::helpers::fnv_hash;
use super::*;
use crate::fingerprint::FP64_INIT;
use crate::state::value_hash::value_fingerprint;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

fn std_hash(v: &Value) -> u64 {
    let mut hasher = DefaultHasher::new();
    v.hash(&mut hasher);
    hasher.finish()
}

fn fp64(v: &Value) -> Option<u64> {
    v.fingerprint_extend(FP64_INIT).ok()
}

/// Construct a representative set of concrete values covering all major types.
fn test_values() -> Vec<(&'static str, Value)> {
    vec![
        ("bool_true", Value::Bool(true)),
        ("bool_false", Value::Bool(false)),
        ("int_zero", Value::int(0)),
        ("int_positive", Value::int(42)),
        ("int_negative", Value::int(-7)),
        ("int_large", Value::int(i64::MAX)),
        ("string_hello", Value::string("hello")),
        ("string_empty", Value::string("")),
        ("set_empty", Value::empty_set()),
        (
            "set_ints",
            Value::set([Value::int(1), Value::int(2), Value::int(3)]),
        ),
        ("set_single", Value::set([Value::int(99)])),
        ("seq_empty", Value::seq(std::iter::empty())),
        ("seq_ints", Value::seq([Value::int(10), Value::int(20)])),
        (
            "tuple_pair",
            Value::Tuple(Arc::from(
                vec![Value::int(1), Value::Bool(true)].into_boxed_slice(),
            )),
        ),
        (
            "interval_1_5",
            Value::Interval(Arc::new(IntervalValue::new(1.into(), 5.into()))),
        ),
    ]
}

// ---- Determinism: same value hashes the same way twice ----

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_std_hash_determinism() {
    for (name, value) in test_values() {
        let h1 = std_hash(&value);
        let h2 = std_hash(&value);
        assert_eq!(h1, h2, "std Hash not deterministic for {name}");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fnv_hash_determinism() {
    for (name, value) in test_values() {
        let h1 = fnv_hash(&value);
        let h2 = fnv_hash(&value);
        assert_eq!(h1, h2, "FNV-1a hash not deterministic for {name}");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fp64_determinism() {
    for (name, value) in test_values() {
        let f1 = fp64(&value);
        let f2 = fp64(&value);
        assert_eq!(f1, f2, "FP64 fingerprint not deterministic for {name}");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_additive_fp_determinism() {
    for (name, value) in test_values() {
        let f1 = value_fingerprint(&value);
        let f2 = value_fingerprint(&value);
        assert_eq!(f1, f2, "Additive fingerprint not deterministic for {name}");
    }
}

// ---- Equality contract: equal values must hash equal ----

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_equal_values_same_std_hash() {
    let pairs: Vec<(&str, Value, Value)> = vec![
        (
            "set_order_independence",
            Value::set([Value::int(1), Value::int(2)]),
            Value::set([Value::int(2), Value::int(1)]),
        ),
        ("int_clone", Value::int(42), Value::int(42)),
        ("string_clone", Value::string("abc"), Value::string("abc")),
        ("bool_clone", Value::Bool(true), Value::Bool(true)),
    ];

    for (name, v1, v2) in &pairs {
        assert_eq!(v1, v2, "precondition: values should be equal for {name}");
        assert_eq!(
            std_hash(v1),
            std_hash(v2),
            "std Hash equality contract violated for {name}"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_equal_values_same_fnv_hash() {
    let pairs: Vec<(&str, Value, Value)> = vec![
        (
            "set_order_independence",
            Value::set([Value::int(1), Value::int(2)]),
            Value::set([Value::int(2), Value::int(1)]),
        ),
        ("int_clone", Value::int(42), Value::int(42)),
    ];

    for (name, v1, v2) in &pairs {
        assert_eq!(v1, v2, "precondition: values should be equal for {name}");
        assert_eq!(
            fnv_hash(v1),
            fnv_hash(v2),
            "FNV-1a equality contract violated for {name}"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_equal_values_same_fp64() {
    let pairs: Vec<(&str, Value, Value)> = vec![
        (
            "set_order_independence",
            Value::set([Value::int(1), Value::int(2)]),
            Value::set([Value::int(2), Value::int(1)]),
        ),
        ("int_clone", Value::int(42), Value::int(42)),
    ];

    for (name, v1, v2) in &pairs {
        assert_eq!(v1, v2, "precondition: values should be equal for {name}");
        assert_eq!(
            fp64(v1),
            fp64(v2),
            "FP64 equality contract violated for {name}"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_equal_values_same_additive_fp() {
    let pairs: Vec<(&str, Value, Value)> = vec![
        (
            "set_order_independence",
            Value::set([Value::int(1), Value::int(2)]),
            Value::set([Value::int(2), Value::int(1)]),
        ),
        ("int_clone", Value::int(42), Value::int(42)),
    ];

    for (name, v1, v2) in &pairs {
        assert_eq!(v1, v2, "precondition: values should be equal for {name}");
        assert_eq!(
            value_fingerprint(v1),
            value_fingerprint(v2),
            "Additive fingerprint equality contract violated for {name}"
        );
    }
}

// ---- Discrimination: different values should produce different hashes ----
// (Not guaranteed by hash functions, but highly likely for these small inputs)

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_different_values_different_hashes() {
    let values = test_values();
    let n = values.len();

    let mut std_collisions = 0;
    let mut fnv_collisions = 0;
    let mut fp64_collisions = 0;
    let mut additive_collisions = 0;

    for i in 0..n {
        for j in (i + 1)..n {
            let (_name_i, vi) = &values[i];
            let (_name_j, vj) = &values[j];

            if vi == vj {
                continue;
            }

            if std_hash(vi) == std_hash(vj) {
                std_collisions += 1;
            }
            if fnv_hash(vi) == fnv_hash(vj) {
                fnv_collisions += 1;
            }
            if fp64(vi).is_some() && fp64(vj).is_some() && fp64(vi) == fp64(vj) {
                fp64_collisions += 1;
            }
            if value_fingerprint(vi) == value_fingerprint(vj) {
                additive_collisions += 1;
            }
        }
    }

    let total_pairs = n * (n - 1) / 2;
    // Allow at most 1 collision in any implementation across all pairs
    assert!(
        std_collisions <= 1,
        "Too many std Hash collisions: {std_collisions}/{total_pairs}"
    );
    assert!(
        fnv_collisions <= 1,
        "Too many FNV-1a collisions: {fnv_collisions}/{total_pairs}"
    );
    assert!(
        fp64_collisions <= 1,
        "Too many FP64 collisions: {fp64_collisions}/{total_pairs}"
    );
    assert!(
        additive_collisions <= 1,
        "Too many additive FP collisions: {additive_collisions}/{total_pairs}"
    );
}

// ---- Cross-implementation self-consistency ----
// For primitive types that use FP64 in all paths, the additive fingerprint
// and FP64 fingerprint should agree.

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_primitive_additive_fp_equals_fp64() {
    let primitives: Vec<(&str, Value)> = vec![
        ("bool_true", Value::Bool(true)),
        ("bool_false", Value::Bool(false)),
        ("int_zero", Value::int(0)),
        ("int_positive", Value::int(42)),
        ("int_negative", Value::int(-7)),
        ("string_hello", Value::string("hello")),
    ];

    for (name, value) in &primitives {
        let additive = value_fingerprint(value);
        let fp = fp64(value).expect("primitive should not overflow FP64");
        assert_eq!(
            additive, fp,
            "Additive FP diverges from FP64 for primitive {name}: additive={additive:#x}, fp64={fp:#x}"
        );
    }
}
