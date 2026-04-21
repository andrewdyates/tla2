// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for `builtin_bagsext` module — BagAdd, BagRemove, FoldBag, SumBag, ProductBag.

use super::{eval_str, eval_with_ops};
use crate::Value;

#[test]
fn test_bag_add_new_element() {
    // BagAdd to empty bag creates single-element bag
    let v = eval_str("BagCardinality(BagAdd(EmptyBag, 1))").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_bag_add_existing_element() {
    // BagAdd increases count by 1
    // SetToBag({1}) = (1->1), BagAdd gives (1->2), cardinality = 2
    let v = eval_str("BagCardinality(BagAdd(SetToBag({1}), 1))").unwrap();
    assert_eq!(v, Value::SmallInt(2));
}

#[test]
fn test_bag_add_multiple() {
    // Add 1 twice to SetToBag({1}): count goes from 1 to 3
    let v = eval_str("CopiesIn(1, BagAdd(BagAdd(SetToBag({1}), 1), 1))").unwrap();
    assert_eq!(v, Value::SmallInt(3));
}

#[test]
fn test_bag_remove_existing() {
    // BagRemove decrements count; with count 1, element is removed
    let v = eval_str("BagIn(1, BagRemove(SetToBag({1, 2}), 1))").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_bag_remove_preserves_other_elements() {
    let v = eval_str("BagIn(2, BagRemove(SetToBag({1, 2}), 1))").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_bag_remove_all() {
    // BagRemoveAll completely removes the element regardless of count
    let v = eval_str("BagIn(1, BagRemoveAll(BagAdd(SetToBag({1, 2}), 1), 1))").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_bag_remove_all_preserves_others() {
    let v = eval_str("BagIn(2, BagRemoveAll(SetToBag({1, 2}), 1))").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_fold_bag_sum() {
    // FoldBag(Add, 0, SetToBag({1,2,3})) = 0+1+2+3 = 6
    let v = eval_with_ops("Add(a, b) == a + b", "FoldBag(Add, 0, SetToBag({1, 2, 3}))").unwrap();
    assert_eq!(v, Value::SmallInt(6));
}

#[test]
fn test_fold_bag_repeated_elements() {
    // BagCup doubles counts: 1->2, 2->2
    // FoldBag(Add, 0, B) with 1*2 + 2*2 = 2+4 = 6
    let v = eval_with_ops(
        "Add(a, b) == a + b",
        "FoldBag(Add, 0, BagCup(SetToBag({1, 2}), SetToBag({1, 2})))",
    )
    .unwrap();
    assert_eq!(v, Value::SmallInt(6));
}

#[test]
fn test_sum_bag() {
    // SumBag: sum of element * count
    // SetToBag({1,2,3}): each has count 1, so 1*1 + 2*1 + 3*1 = 6
    let v = eval_str("SumBag(SetToBag({1, 2, 3}))").unwrap();
    assert_eq!(v, Value::SmallInt(6));
}

#[test]
fn test_sum_bag_with_multiplied_counts() {
    // BagCup doubles counts: 1*2 + 2*2 + 3*2 = 12
    let v = eval_str("SumBag(BagCup(SetToBag({1, 2, 3}), SetToBag({1, 2, 3})))").unwrap();
    assert_eq!(v, Value::SmallInt(12));
}

#[test]
fn test_product_bag() {
    // ProductBag: product of element^count
    // SetToBag({2,3}): 2^1 * 3^1 = 6
    let v = eval_str("ProductBag(SetToBag({2, 3}))").unwrap();
    assert_eq!(v, Value::SmallInt(6));
}

#[test]
fn test_product_bag_with_doubled_counts() {
    // BagCup doubles counts: 2^2 * 3^2 = 4 * 9 = 36
    let v = eval_str("ProductBag(BagCup(SetToBag({2, 3}), SetToBag({2, 3})))").unwrap();
    assert_eq!(v, Value::SmallInt(36));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bag_add_accepts_empty_sequence_variant() {
    // Sequences are functions in TLA+, so <<>> should behave like an empty bag.
    // Ported from tla-check eval tests during #2034 consolidation.
    let v = eval_str("BagCardinality(BagAdd(<<>>, 1))").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bag_add_survives_set_intern_variant_substitution() {
    // Prime the set intern table with <<>> first, then read EmptyBag from a singleton set.
    // If EmptyBag is substituted to Seq([]), BagAdd must still accept it.
    // Ported from tla-check eval tests during #2034 consolidation.
    crate::value::clear_set_intern_table();
    let v = eval_str(
        r#"LET prime == CHOOSE x \in {<<>>} : TRUE
               bag == CHOOSE x \in {EmptyBag} : TRUE
           IN IF prime = prime THEN BagCardinality(BagAdd(bag, 1)) ELSE 0"#,
    )
    .unwrap();
    assert_eq!(v, Value::SmallInt(1));
    crate::value::clear_set_intern_table();
}
