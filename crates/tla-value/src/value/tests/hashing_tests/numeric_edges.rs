// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integer-hashing boundary regressions for hash_i64_as_bigint.

use super::super::super::*;
use super::hash_value;
use std::sync::Arc;

// === hash_i64_as_bigint edge cases ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_i64_min_matches_bigint() {
    // i64::MIN is a special case in hash_i64_as_bigint (cannot negate directly)
    let small = Value::SmallInt(i64::MIN);
    let big = Value::Int(Arc::new(BigInt::from(i64::MIN)));
    assert_eq!(small, big);
    assert_eq!(
        hash_value(&small),
        hash_value(&big),
        "SmallInt(i64::MIN) and Int(BigInt(i64::MIN)) must hash identically"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_negative_integers_match_bigint() {
    // Negative values use Sign::Minus path in hash_i64_as_bigint
    for n in [-1i64, -42, -128, -256, -65536, i64::MIN + 1] {
        let small = Value::SmallInt(n);
        let big = Value::Int(Arc::new(BigInt::from(n)));
        assert_eq!(small, big, "equality for {n}");
        assert_eq!(
            hash_value(&small),
            hash_value(&big),
            "hash mismatch for SmallInt({n}) vs Int(BigInt({n}))"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_hash_boundary_integers() {
    // Test values at byte boundaries where leading_zeros changes
    let boundary_values: Vec<i64> = vec![
        0,
        1,
        -1,
        127,
        128,
        255,
        256,
        32767,
        32768,
        65535,
        65536,
        i64::MAX,
        i64::MIN,
    ];
    for n in boundary_values {
        let small = Value::SmallInt(n);
        let big = Value::Int(Arc::new(BigInt::from(n)));
        assert_eq!(
            hash_value(&small),
            hash_value(&big),
            "hash mismatch at byte boundary for {n}"
        );
    }
}
