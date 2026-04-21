// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scalar and iteration ordering tests for `iter_set_tlc_normalized`.

use super::super::super::*;
use super::tlc_normalized;
use std::sync::Arc;

// === Integer sets ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_normalized_int_set_sorted() {
    let s = Value::set([Value::int(3), Value::int(1), Value::int(2)]);
    let result = tlc_normalized(&s);
    assert_eq!(result, vec![Value::int(1), Value::int(2), Value::int(3)]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_normalized_int_set_with_negatives() {
    let s = Value::set([Value::int(1), Value::int(-1), Value::int(0)]);
    let result = tlc_normalized(&s);
    assert_eq!(result, vec![Value::int(-1), Value::int(0), Value::int(1)]);
}

// === String sets ===

/// Part of #3193: TLC sorts strings by intern-token order (first-seen/parse
/// order), not lexical order. This test uses unique strings and controls
/// registration order to verify the TLC-normalized iteration reflects token
/// order rather than lexical order.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_normalized_string_set_token_order() {
    use super::super::super::strings::{clear_tlc_string_tokens, tlc_string_token};

    // Clear token registry to control assignment order
    clear_tlc_string_tokens();

    // Register strings in specific order: zulu first, then alpha, then mike.
    // TLC would do this if "zulu" appeared first in the spec source.
    let s_zulu = Arc::from("__tlc_test_zulu");
    let s_alpha = Arc::from("__tlc_test_alpha");
    let s_mike = Arc::from("__tlc_test_mike");

    let tok_zulu = tlc_string_token(&s_zulu);
    let tok_alpha = tlc_string_token(&s_alpha);
    let tok_mike = tlc_string_token(&s_mike);

    assert!(
        tok_zulu < tok_alpha,
        "zulu registered first, gets lower token"
    );
    assert!(tok_alpha < tok_mike, "alpha registered second, mike third");

    // Create a set — stored in lexical order by Value::cmp
    let s = Value::set([
        Value::String(s_alpha.clone()),
        Value::String(s_mike.clone()),
        Value::String(s_zulu.clone()),
    ]);

    // TLC-normalized iteration should yield token order: zulu, alpha, mike
    let result = tlc_normalized(&s);
    assert_eq!(
        result,
        vec![
            Value::String(s_zulu),
            Value::String(s_alpha),
            Value::String(s_mike),
        ],
        "TLC-normalized string set must iterate in intern-token order, not lexical"
    );

    // Clean up
    clear_tlc_string_tokens();
}

// === Boolean sets ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_normalized_boolean_set() {
    let s = Value::set([Value::bool(true), Value::bool(false)]);
    let result = tlc_normalized(&s);
    // TLC orders FALSE before TRUE
    assert_eq!(result, vec![Value::bool(false), Value::bool(true)]);
}

// === Interval ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_normalized_interval_in_order() {
    let iv = Value::Interval(Arc::new(IntervalValue::new(
        BigInt::from(1),
        BigInt::from(5),
    )));
    let result = tlc_normalized(&iv);
    assert_eq!(
        result,
        vec![
            Value::int(1),
            Value::int(2),
            Value::int(3),
            Value::int(4),
            Value::int(5)
        ]
    );
}

// === Deduplication ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_normalized_deduplication() {
    // Sets shouldn't have duplicates, but the sort function should handle it
    let s = Value::set([Value::int(1), Value::int(2)]);
    let result = tlc_normalized(&s);
    assert_eq!(result.len(), 2);
    assert_eq!(result, vec![Value::int(1), Value::int(2)]);
}

// === Empty set ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_normalized_empty_set() {
    let s = Value::set(std::iter::empty::<Value>());
    let result = tlc_normalized(&s);
    assert!(result.is_empty());
}

// === Singleton set ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_normalized_singleton() {
    let s = Value::set([Value::int(42)]);
    let result = tlc_normalized(&s);
    assert_eq!(result, vec![Value::int(42)]);
}
