// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `builtin_bags` module — Bags standard library operators.

use super::eval_str;
use crate::Value;

#[test]
fn test_empty_bag_is_a_bag() {
    // EmptyBag is a zero-arity builtin returning the empty function
    let v = eval_str("IsABag(EmptyBag)").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_is_a_bag_tuple_positive_ints() {
    // A tuple of positive integers is a valid bag (function from 1..n to positive ints)
    let v = eval_str("IsABag(<<1, 2, 3>>)").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_is_a_bag_tuple_with_zero_is_not_bag() {
    // Zero is not a positive integer, so not a valid bag
    let v = eval_str("IsABag(<<1, 0, 3>>)").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_is_a_bag_non_integer_values() {
    // String values are not positive integers
    let v = eval_str("IsABag(<<\"a\", \"b\">>)").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_is_a_bag_boolean_not_bag() {
    let v = eval_str("IsABag(TRUE)").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_set_to_bag_and_bag_to_set_roundtrip() {
    // SetToBag assigns count 1 to each element; BagToSet returns domain
    let v = eval_str("BagToSet(SetToBag({1, 2, 3})) = {1, 2, 3}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_bag_in_present() {
    let v = eval_str("BagIn(2, SetToBag({1, 2, 3}))").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_bag_in_absent() {
    let v = eval_str("BagIn(4, SetToBag({1, 2, 3}))").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_copies_in_present() {
    // SetToBag gives each element count 1
    let v = eval_str("CopiesIn(2, SetToBag({1, 2, 3}))").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_copies_in_absent() {
    let v = eval_str("CopiesIn(4, SetToBag({1, 2, 3}))").unwrap();
    assert_eq!(v, Value::SmallInt(0));
}

#[test]
fn test_bag_cardinality() {
    // SetToBag({1,2,3}) gives each element count 1, total = 3
    let v = eval_str("BagCardinality(SetToBag({1, 2, 3}))").unwrap();
    assert_eq!(v, Value::SmallInt(3));
}

#[test]
fn test_bag_cup_adds_counts() {
    // BagCup(B1, B2) adds counts for overlapping elements
    // SetToBag({1,2}) = (1->1, 2->1), SetToBag({2,3}) = (2->1, 3->1)
    // Cup: 1->1, 2->2, 3->1 => cardinality = 4
    let v = eval_str("BagCardinality(BagCup(SetToBag({1, 2}), SetToBag({2, 3})))").unwrap();
    assert_eq!(v, Value::SmallInt(4));
}

#[test]
fn test_bag_diff_subtracts_counts() {
    // BagDiff removes overlapping elements; keeps only positive remainders
    // SetToBag({1,2,3}) = (1->1, 2->1, 3->1)
    // SetToBag({2,3,4}) = (2->1, 3->1, 4->1)
    // Diff: 1->1 (only element with positive difference)
    let v = eval_str("BagToSet(BagDiff(SetToBag({1, 2, 3}), SetToBag({2, 3, 4}))) = {1}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_bag_union_set_of_bags() {
    // BagUnion takes a set of bags and unions them
    let v = eval_str("BagCardinality(BagUnion({SetToBag({1, 2}), SetToBag({2, 3})}))").unwrap();
    assert_eq!(v, Value::SmallInt(4));
}

#[test]
fn test_sq_subseteq_true() {
    // SetToBag({1}) \sqsubseteq SetToBag({1,2}) — {1} is a subbag of {1,2}
    let v = eval_str("SqSubseteq(SetToBag({1}), SetToBag({1, 2}))").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_sq_subseteq_false() {
    // SetToBag({1,2,3}) is NOT a subbag of SetToBag({1,2})
    let v = eval_str("SqSubseteq(SetToBag({1, 2, 3}), SetToBag({1, 2}))").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_sq_subseteq_same_bag() {
    let v = eval_str("SqSubseteq(SetToBag({1, 2}), SetToBag({1, 2}))").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_sub_bag_empty_bag() {
    // SubBag of empty bag is {{}} (set containing only the empty bag)
    let v = eval_str("Cardinality(SubBag(EmptyBag))").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_sub_bag_single_element() {
    // SubBag of a bag with one element (count 1): {EmptyBag, that bag}
    let v = eval_str("Cardinality(SubBag(SetToBag({1})))").unwrap();
    assert_eq!(v, Value::SmallInt(2));
}

#[test]
fn test_bag_of_all_maps_elements() {
    // BagOfAll(F, B) applies F to each element, preserving counts
    // Use a lambda to double each element
    let v = eval_str("BagCardinality(BagOfAll(LAMBDA x: x * 2, SetToBag({1, 2, 3})))").unwrap();
    assert_eq!(v, Value::SmallInt(3));
}
