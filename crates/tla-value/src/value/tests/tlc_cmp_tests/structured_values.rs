// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structured-value (tuple/set) ordering tests for `tlc_cmp`.

use super::super::super::*;
use super::tlc_normalized;

// === Tuple sets (sorted by length then element-by-element) ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_normalized_tuple_set() {
    let s = Value::set([
        Value::tuple([Value::int(2), Value::int(1)]),
        Value::tuple([Value::int(1), Value::int(2)]),
        Value::tuple([Value::int(1), Value::int(1)]),
    ]);
    let result = tlc_normalized(&s);
    // TLC sorts tuples by length, then element-by-element
    assert_eq!(result.len(), 3);
    assert_eq!(result[0], Value::tuple([Value::int(1), Value::int(1)]));
    assert_eq!(result[1], Value::tuple([Value::int(1), Value::int(2)]));
    assert_eq!(result[2], Value::tuple([Value::int(2), Value::int(1)]));
}

// === Mixed-length tuples (CRITICAL: length-first ordering) ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_normalized_mixed_length_tuples() {
    // tlc_cmp orders tuples by LENGTH FIRST, then element-by-element.
    // Value::cmp uses LEXICOGRAPHIC ordering (element-first).
    // For {<<2>>, <<1, 1>>}:
    //   tlc_cmp: <<2>> < <<1, 1>> (length 1 < length 2)
    //   Value::cmp: <<1, 1>> < <<2>> (element 1 < element 2)
    // The normalized order MUST use tlc_cmp ordering.
    let s = Value::set([
        Value::tuple([Value::int(2)]),
        Value::tuple([Value::int(1), Value::int(1)]),
    ]);
    let result = tlc_normalized(&s);
    assert_eq!(result.len(), 2);
    assert_eq!(result[0], Value::tuple([Value::int(2)]));
    assert_eq!(result[1], Value::tuple([Value::int(1), Value::int(1)]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_first_element_mixed_length_tuples() {
    // tlc_first_element must return the tlc_cmp minimum, not the Value::cmp minimum.
    // For {<<2>>, <<1, 1>>}: TLC minimum is <<2>> (shorter = smaller).
    let s = Value::set([
        Value::tuple([Value::int(2)]),
        Value::tuple([Value::int(1), Value::int(1)]),
    ]);
    let result = s.tlc_first_element().unwrap();
    assert_eq!(result, Some(Value::tuple([Value::int(2)])));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_normalized_mixed_cardinality_set_elements() {
    // Sets-as-elements: tlc_cmp compares by cardinality first.
    // {2} (cardinality 1) < {1, 2} (cardinality 2) in TLC order.
    let s = Value::set([
        Value::set([Value::int(1), Value::int(2)]),
        Value::set([Value::int(2)]),
    ]);
    let result = tlc_normalized(&s);
    assert_eq!(result.len(), 2);
    assert_eq!(result[0], Value::set([Value::int(2)]));
    assert_eq!(result[1], Value::set([Value::int(1), Value::int(2)]));
}
