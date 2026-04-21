// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for SortedSet::equals_integer_interval and
//! SortedSet::equals_sequence_domain.
//!
//! Part of #3073: these helpers replaced OrdSet-based domain comparison
//! in eval_membership.rs and eval_sets.rs. They had no direct unit tests;
//! only indirect coverage through the evaluator.

use crate::value::sorted_set::SortedSet;
use crate::value::Value;
use num_bigint::BigInt;
use std::sync::Arc;

// === equals_integer_interval ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interval_empty_when_max_lt_min() {
    // max < min → expected length is 0, so only the empty set matches.
    let empty = SortedSet::new();
    assert!(empty.equals_integer_interval(5, 3));
    // Non-empty set should NOT match an empty interval.
    let nonempty = SortedSet::from_sorted_vec(vec![Value::SmallInt(1)]);
    assert!(!nonempty.equals_integer_interval(5, 3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interval_single_element() {
    // min == max → interval is {min}
    let set = SortedSet::from_sorted_vec(vec![Value::SmallInt(42)]);
    assert!(set.equals_integer_interval(42, 42));
    // Wrong value should not match.
    let wrong = SortedSet::from_sorted_vec(vec![Value::SmallInt(43)]);
    assert!(!wrong.equals_integer_interval(42, 42));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interval_standard_range() {
    // {1, 2, 3} == interval [1, 3]
    let set = SortedSet::from_sorted_vec(vec![
        Value::SmallInt(1),
        Value::SmallInt(2),
        Value::SmallInt(3),
    ]);
    assert!(set.equals_integer_interval(1, 3));
    // Wrong interval bounds should fail.
    assert!(!set.equals_integer_interval(1, 2));
    assert!(!set.equals_integer_interval(0, 3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interval_negative_range() {
    // {-2, -1, 0} == interval [-2, 0]
    let set = SortedSet::from_sorted_vec(vec![
        Value::SmallInt(-2),
        Value::SmallInt(-1),
        Value::SmallInt(0),
    ]);
    assert!(set.equals_integer_interval(-2, 0));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interval_with_bigint_values() {
    // BigInt values that fit in i64 should be matched correctly.
    let set = SortedSet::from_sorted_vec(vec![
        Value::Int(Arc::new(BigInt::from(1))),
        Value::Int(Arc::new(BigInt::from(2))),
        Value::Int(Arc::new(BigInt::from(3))),
    ]);
    assert!(set.equals_integer_interval(1, 3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interval_mixed_smallint_and_bigint() {
    // Mixed SmallInt and BigInt — as_i64() handles both.
    let set = SortedSet::from_sorted_vec(vec![
        Value::SmallInt(1),
        Value::Int(Arc::new(BigInt::from(2))),
        Value::SmallInt(3),
    ]);
    assert!(set.equals_integer_interval(1, 3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interval_non_integer_values_fail() {
    // A set with non-integer values should not match any interval.
    let set = SortedSet::from_sorted_vec(vec![Value::Bool(true)]);
    assert!(!set.equals_integer_interval(0, 0));
    assert!(!set.equals_integer_interval(1, 1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interval_wrong_length_rejects_early() {
    // {1, 2} != [1, 3] — length mismatch rejects before element check.
    let set = SortedSet::from_sorted_vec(vec![Value::SmallInt(1), Value::SmallInt(2)]);
    assert!(!set.equals_integer_interval(1, 3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interval_empty_set_matches_empty_interval() {
    let empty = SortedSet::new();
    assert!(empty.equals_integer_interval(1, 0)); // max < min → empty
    assert!(empty.equals_integer_interval(0, -1)); // max < min → empty
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interval_overflow_bounds() {
    // i64::MAX as min with max = i64::MAX should be a single-element interval.
    let set = SortedSet::from_sorted_vec(vec![Value::SmallInt(i64::MAX)]);
    assert!(set.equals_integer_interval(i64::MAX, i64::MAX));
    // Interval [0, i64::MAX] has length i64::MAX+1 which overflows checked_add.
    // Should return false (overflow in length calculation).
    let small = SortedSet::from_sorted_vec(vec![Value::SmallInt(0)]);
    assert!(!small.equals_integer_interval(0, i64::MAX));
}

// === equals_sequence_domain ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_domain_empty() {
    let empty = SortedSet::new();
    assert!(empty.equals_sequence_domain(0));
    // Non-empty set does not match len=0.
    let nonempty = SortedSet::from_sorted_vec(vec![Value::SmallInt(1)]);
    assert!(!nonempty.equals_sequence_domain(0));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_domain_single() {
    // len=1 → {1}
    let set = SortedSet::from_sorted_vec(vec![Value::SmallInt(1)]);
    assert!(set.equals_sequence_domain(1));
    // {0} should NOT match len=1 (sequences are 1-indexed in TLA+).
    let zero_based = SortedSet::from_sorted_vec(vec![Value::SmallInt(0)]);
    assert!(!zero_based.equals_sequence_domain(1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_domain_three() {
    // len=3 → {1, 2, 3}
    let set = SortedSet::from_sorted_vec(vec![
        Value::SmallInt(1),
        Value::SmallInt(2),
        Value::SmallInt(3),
    ]);
    assert!(set.equals_sequence_domain(3));
    assert!(!set.equals_sequence_domain(2));
    assert!(!set.equals_sequence_domain(4));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_domain_empty_does_not_match_nonzero() {
    let empty = SortedSet::new();
    assert!(!empty.equals_sequence_domain(1));
    assert!(!empty.equals_sequence_domain(100));
}
