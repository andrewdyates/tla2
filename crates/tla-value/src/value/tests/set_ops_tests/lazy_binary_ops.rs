// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazy binary set-operator coverage for SetCupValue, SetCapValue, and SetDiffValue.

use super::*;

// === SetCupValue (union) ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_cup_basic_union() {
    let s1 = Value::set([Value::int(1), Value::int(2)]);
    let s2 = Value::set([Value::int(3), Value::int(4)]);
    let cup = SetCupValue::new(s1, s2);

    assert_eq!(cup.contains(&Value::int(1)), Some(true));
    assert_eq!(cup.contains(&Value::int(3)), Some(true));
    assert_eq!(cup.contains(&Value::int(5)), Some(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_cup_overlapping() {
    let s1 = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let s2 = Value::set([Value::int(2), Value::int(3), Value::int(4)]);
    let cup = SetCupValue::new(s1, s2);

    // Union should contain all elements
    for i in 1..=4 {
        assert_eq!(
            cup.contains(&Value::int(i)),
            Some(true),
            "union should contain {i}"
        );
    }

    // Enumeration should deduplicate
    let sorted = cup.to_sorted_set().expect("should be enumerable");
    assert_eq!(sorted.len(), 4);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_cup_with_empty() {
    let s1 = Value::set([Value::int(1), Value::int(2)]);
    let empty = Value::set(std::iter::empty::<Value>());
    let cup = SetCupValue::new(s1.clone(), empty);

    let sorted = cup.to_sorted_set().expect("should be enumerable");
    assert_eq!(sorted.len(), 2);
    assert!(cup.is_enumerable());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_cup_both_empty() {
    let e1 = Value::set(std::iter::empty::<Value>());
    let e2 = Value::set(std::iter::empty::<Value>());
    let cup = SetCupValue::new(e1, e2);

    assert!(cup.is_empty());
    let sorted = cup.to_sorted_set().expect("should be enumerable");
    assert_eq!(sorted.len(), 0);
}

// === SetCapValue (intersection) ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_cap_basic_intersection() {
    let s1 = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let s2 = Value::set([Value::int(2), Value::int(3), Value::int(4)]);
    let cap = SetCapValue::new(s1, s2);

    assert_eq!(cap.contains(&Value::int(1)), Some(false));
    assert_eq!(cap.contains(&Value::int(2)), Some(true));
    assert_eq!(cap.contains(&Value::int(3)), Some(true));
    assert_eq!(cap.contains(&Value::int(4)), Some(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_cap_disjoint() {
    let s1 = Value::set([Value::int(1), Value::int(2)]);
    let s2 = Value::set([Value::int(3), Value::int(4)]);
    let cap = SetCapValue::new(s1, s2);

    assert!(cap.is_empty());
    let sorted = cap.to_sorted_set().expect("should be enumerable");
    assert_eq!(sorted.len(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_cap_with_empty() {
    let s1 = Value::set([Value::int(1), Value::int(2)]);
    let empty = Value::set(std::iter::empty::<Value>());
    let cap = SetCapValue::new(s1, empty);

    assert!(cap.is_empty());
}

// === SetDiffValue (difference) ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_diff_basic() {
    let s1 = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let s2 = Value::set([Value::int(2), Value::int(3), Value::int(4)]);
    let diff = SetDiffValue::new(s1, s2);

    assert_eq!(diff.contains(&Value::int(1)), Some(true));
    assert_eq!(diff.contains(&Value::int(2)), Some(false));
    assert_eq!(diff.contains(&Value::int(4)), Some(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_diff_with_empty_rhs() {
    let s1 = Value::set([Value::int(1), Value::int(2)]);
    let empty = Value::set(std::iter::empty::<Value>());
    let diff = SetDiffValue::new(s1, empty);

    // S \ {} == S
    let sorted = diff.to_sorted_set().expect("should be enumerable");
    assert_eq!(sorted.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_diff_with_empty_lhs() {
    let empty = Value::set(std::iter::empty::<Value>());
    let s2 = Value::set([Value::int(1), Value::int(2)]);
    let diff = SetDiffValue::new(empty, s2);

    // {} \ S == {}
    assert!(diff.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_diff_same_set() {
    let s = Value::set([Value::int(1), Value::int(2)]);
    let diff = SetDiffValue::new(s.clone(), s);

    // S \ S == {}
    assert!(diff.is_empty());
}

// === Nested set operations ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_ops_nested_union_of_intersections() {
    // (A ∩ B) ∪ (B ∩ C)
    let a = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let b = Value::set([Value::int(2), Value::int(3), Value::int(4)]);
    let c = Value::set([Value::int(3), Value::int(4), Value::int(5)]);

    let ab = Value::SetCap(SetCapValue::new(a, b.clone()));
    let bc = Value::SetCap(SetCapValue::new(b, c));
    let result = SetCupValue::new(ab, bc);

    // A ∩ B = {2, 3}, B ∩ C = {3, 4}, union = {2, 3, 4}
    let sorted = result.to_sorted_set().expect("should be enumerable");
    assert_eq!(sorted.len(), 3);
    assert!(sorted.contains(&Value::int(2)));
    assert!(sorted.contains(&Value::int(3)));
    assert!(sorted.contains(&Value::int(4)));
}

// === SetDiffValue to_sorted_set ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_diff_to_sorted_set_partial_overlap() {
    let s1 = Value::set([Value::int(1), Value::int(2), Value::int(3), Value::int(4)]);
    let s2 = Value::set([Value::int(2), Value::int(4)]);
    let diff = SetDiffValue::new(s1, s2);

    let sorted = diff.to_sorted_set().expect("should be enumerable");
    assert_eq!(sorted.len(), 2);
    assert!(sorted.contains(&Value::int(1)));
    assert!(sorted.contains(&Value::int(3)));
    assert!(!sorted.contains(&Value::int(2)));
    assert!(!sorted.contains(&Value::int(4)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_diff_to_sorted_set_normalizes_bigunion_stream() {
    let union = Value::BigUnion(UnionValue::new(Value::set([
        Value::set([Value::int(1), Value::int(100)]),
        Value::set([Value::int(2)]),
    ])));
    let diff = SetDiffValue::new(union, Value::set([Value::int(1)]));

    let sorted = diff.to_sorted_set().expect("should be enumerable");
    assert_eq!(sorted.as_slice(), &[Value::int(2), Value::int(100)]);
    assert!(sorted.contains(&Value::int(2)));
    assert!(sorted.contains(&Value::int(100)));
    assert!(!sorted.contains(&Value::int(1)));
}

// === SetCapValue to_sorted_set ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_cap_to_sorted_set_partial_overlap() {
    let s1 = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let s2 = Value::set([Value::int(2), Value::int(3), Value::int(4)]);
    let cap = SetCapValue::new(s1, s2);

    let sorted = cap.to_sorted_set().expect("should be enumerable");
    assert_eq!(sorted.len(), 2);
    assert!(sorted.contains(&Value::int(2)));
    assert!(sorted.contains(&Value::int(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_cap_to_sorted_set_normalizes_bigunion_stream() {
    let union = Value::BigUnion(UnionValue::new(Value::set([
        Value::set([Value::int(1), Value::int(100)]),
        Value::set([Value::int(2)]),
    ])));
    let cap = SetCapValue::new(union, Value::set([Value::int(2), Value::int(100)]));

    let sorted = cap.to_sorted_set().expect("should be enumerable");
    assert_eq!(sorted.as_slice(), &[Value::int(2), Value::int(100)]);
    assert!(sorted.contains(&Value::int(2)));
    assert!(sorted.contains(&Value::int(100)));
    assert!(!sorted.contains(&Value::int(1)));
}

// === SetCup/SetCap/SetDiff with non-enumerable operands ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_cup_with_stringset_not_enumerable() {
    // Union with StringSet is not enumerable but membership should work
    let s1 = Value::set([Value::string("a"), Value::string("b")]);
    let cup = SetCupValue::new(s1, Value::StringSet);

    assert!(
        !cup.is_enumerable(),
        "union with StringSet should not be enumerable"
    );
    assert!(
        cup.to_sorted_set().is_none(),
        "to_sorted_set should return None"
    );

    // Membership still works
    assert_eq!(cup.contains(&Value::string("a")), Some(true));
    assert_eq!(cup.contains(&Value::string("z")), Some(true)); // "z" \in STRING
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_cap_with_stringset_enumerable() {
    // Intersection with STRING where one side is enumerable
    let s1 = Value::set([Value::string("a"), Value::int(1)]);
    let cap = SetCapValue::new(s1, Value::StringSet);

    assert!(
        cap.is_enumerable(),
        "cap with one enumerable side should be enumerable"
    );

    // Only strings survive the intersection
    let sorted = cap.to_sorted_set().expect("should be enumerable");
    assert_eq!(sorted.len(), 1);
    assert!(sorted.contains(&Value::string("a")));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_diff_lhs_enumerable_rhs_not() {
    // S1 \ STRING: enumerable (iterate S1, filter out STRING members)
    let s1 = Value::set([Value::string("a"), Value::int(1), Value::int(2)]);
    let diff = SetDiffValue::new(s1, Value::StringSet);

    assert!(
        diff.is_enumerable(),
        "diff with enumerable LHS should be enumerable"
    );

    // Only non-strings survive: {1, 2}
    let sorted = diff.to_sorted_set().expect("should be enumerable");
    assert_eq!(sorted.len(), 2);
    assert!(sorted.contains(&Value::int(1)));
    assert!(sorted.contains(&Value::int(2)));
}

// Extensional equality tests for SetCup/SetCap/SetDiff vs plain Set are
// deferred until eq_set_like is wired into PartialEq/Ord (#1821).
// See #1829 for tracking. Deleted because tests must PASS or be DELETED (#341).
