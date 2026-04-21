// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Randomization module tests — RandomSubset, RandomSetOfSubsets,
//! RandomSubsetSet.
//!
//! Extracted from property_tests.rs lines 3414-3498.
//! Part of #1371.

use tla_check::Value;
use tla_value::SortedSet;

use super::helpers::eval_str;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_random_subset_basic() {
    // RandomSubset(2, {1, 2, 3, 4}) returns a 2-element subset
    let result = eval_str(r#"RandomSubset(2, {1, 2, 3, 4})"#).unwrap();
    let set = result.as_set().expect("Expected set");
    assert_eq!(set.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_random_subset_full_set() {
    // RandomSubset(4, {1, 2, 3, 4}) returns the full set
    let result = eval_str(r#"RandomSubset(4, {1, 2, 3, 4})"#).unwrap();
    let expected = eval_str(r#"{1, 2, 3, 4}"#).unwrap();
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_random_subset_empty() {
    // RandomSubset(0, {1, 2, 3}) returns empty set
    let result = eval_str(r#"RandomSubset(0, {1, 2, 3})"#).unwrap();
    assert_eq!(result, Value::Set(Arc::new(SortedSet::new())));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_random_subset_singleton() {
    // RandomSubset(1, {42}) returns {42}
    let result = eval_str(r#"RandomSubset(1, {42})"#).unwrap();
    let expected = eval_str(r#"{42}"#).unwrap();
    assert_eq!(result, expected);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_random_set_of_subsets_basic() {
    // RandomSetOfSubsets(3, 2, {1, 2, 3, 4}) returns a set of subsets
    let result = eval_str(r#"RandomSetOfSubsets(3, 2, {1, 2, 3, 4})"#).unwrap();
    let set = result.as_set().expect("Expected set of sets");
    // Should have at most 3 subsets (may have fewer due to dedup)
    assert!(set.len() <= 3);
    // Each should be a subset of {1, 2, 3, 4}
    for subset in set {
        let sub = subset.as_set().expect("Expected inner set");
        assert!(sub.len() <= 4);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_random_set_of_subsets_empty_base() {
    // RandomSetOfSubsets with empty set returns {{}}
    let result = eval_str(r#"RandomSetOfSubsets(3, 0, {})"#).unwrap();
    let set = result.as_set().expect("Expected set");
    // Should contain only the empty set
    assert_eq!(set.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_random_subset_set_basic() {
    // RandomSubsetSet(3, "0.5", {1, 2, 3, 4}) returns a set of subsets
    let result = eval_str(r#"RandomSubsetSet(3, "0.5", {1, 2, 3, 4})"#).unwrap();
    let set = result.as_set().expect("Expected set of sets");
    assert!(set.len() <= 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_random_subset_set_zero_prob() {
    // RandomSubsetSet with 0.0 probability returns set of empty sets
    let result = eval_str(r#"RandomSubsetSet(2, "0.0", {1, 2, 3})"#).unwrap();
    let set = result.as_set().expect("Expected set");
    // Each subset should be empty
    for subset in set {
        let sub = subset.as_set().expect("Expected inner set");
        assert!(sub.is_empty());
    }
}
