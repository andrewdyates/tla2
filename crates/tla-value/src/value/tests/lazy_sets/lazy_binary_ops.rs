// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazy binary set operation (SetCup, SetCap, SetDiff) membership and Value dispatch tests.

use super::super::super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setcup_enumerable() {
    // Two enumerable sets -> can convert to SortedSet
    let s1 = Value::set([Value::int(1), Value::int(2)]);
    let s2 = Value::set([Value::int(2), Value::int(3)]);
    let cup = SetCupValue::new(s1, s2);

    // Membership tests
    assert!(cup.contains(&Value::int(1)).unwrap());
    assert!(cup.contains(&Value::int(2)).unwrap());
    assert!(cup.contains(&Value::int(3)).unwrap());
    assert!(!cup.contains(&Value::int(4)).unwrap());

    // Should be enumerable
    assert!(cup.is_enumerable());
    let set = cup.to_sorted_set().unwrap();
    assert_eq!(set.len(), 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setcup_with_stringset() {
    // STRING \cup {1, 2} -> non-enumerable union (STRING is infinite)
    let s1 = Value::StringSet;
    let s2 = Value::set([Value::int(1), Value::int(2)]);
    let cup = SetCupValue::new(s1, s2);

    // Membership: strings are in STRING, ints are in the finite set
    assert!(cup.contains(&Value::string("hello")).unwrap());
    assert!(cup.contains(&Value::int(1)).unwrap());
    assert!(cup.contains(&Value::int(2)).unwrap());
    assert!(!cup.contains(&Value::int(3)).unwrap());

    // Not enumerable (STRING is infinite)
    assert!(!cup.is_enumerable());
    assert!(cup.to_sorted_set().is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setcup_with_anyset() {
    // ANY \cup {1, 2} -> non-enumerable union (ANY is universal)
    let s1 = Value::AnySet;
    let s2 = Value::set([Value::int(1), Value::int(2)]);
    let cup = SetCupValue::new(s1, s2);

    // Any value should be in the union (ANY contains everything)
    assert!(cup.contains(&Value::string("hello")).unwrap());
    assert!(cup.contains(&Value::int(42)).unwrap());
    assert!(cup.contains(&Value::bool(true)).unwrap());

    // Not enumerable (ANY is infinite/universal)
    assert!(!cup.is_enumerable());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setcap_enumerable() {
    // Two enumerable sets -> intersection
    let s1 = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let s2 = Value::set([Value::int(2), Value::int(3), Value::int(4)]);
    let cap = SetCapValue::new(s1, s2);

    // Membership tests
    assert!(!cap.contains(&Value::int(1)).unwrap());
    assert!(cap.contains(&Value::int(2)).unwrap());
    assert!(cap.contains(&Value::int(3)).unwrap());
    assert!(!cap.contains(&Value::int(4)).unwrap());

    // Should be enumerable
    assert!(cap.is_enumerable());
    let set = cap.to_sorted_set().unwrap();
    assert_eq!(set.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setcap_with_stringset() {
    // STRING \cap {"a", "b", 1, 2} -> only strings pass both membership checks
    let s1 = Value::StringSet;
    let s2 = Value::set([
        Value::string("a"),
        Value::string("b"),
        Value::int(1),
        Value::int(2),
    ]);
    let cap = SetCapValue::new(s1, s2);

    // Membership: only strings in s2 are in the intersection
    assert!(cap.contains(&Value::string("a")).unwrap());
    assert!(cap.contains(&Value::string("b")).unwrap());
    assert!(!cap.contains(&Value::int(1)).unwrap()); // INT not in STRING
    assert!(!cap.contains(&Value::int(2)).unwrap());
    assert!(!cap.contains(&Value::string("c")).unwrap()); // not in s2

    // Enumerable because s2 is finite
    assert!(cap.is_enumerable());
    let set = cap.to_sorted_set().unwrap();
    assert_eq!(set.len(), 2); // "a" and "b"
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setdiff_enumerable() {
    // {1, 2, 3} \ {2, 3, 4} -> {1}
    let s1 = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let s2 = Value::set([Value::int(2), Value::int(3), Value::int(4)]);
    let diff = SetDiffValue::new(s1, s2);

    // Membership tests
    assert!(diff.contains(&Value::int(1)).unwrap());
    assert!(!diff.contains(&Value::int(2)).unwrap());
    assert!(!diff.contains(&Value::int(3)).unwrap());
    assert!(!diff.contains(&Value::int(4)).unwrap());

    // Should be enumerable
    assert!(diff.is_enumerable());
    let set = diff.to_sorted_set().unwrap();
    assert_eq!(set.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setdiff_with_stringset_rhs() {
    // {1, "a", 2, "b"} \ STRING -> {1, 2} (strings removed)
    let s1 = Value::set([
        Value::int(1),
        Value::string("a"),
        Value::int(2),
        Value::string("b"),
    ]);
    let s2 = Value::StringSet;
    let diff = SetDiffValue::new(s1, s2);

    // Membership: only non-strings remain
    assert!(diff.contains(&Value::int(1)).unwrap());
    assert!(diff.contains(&Value::int(2)).unwrap());
    assert!(!diff.contains(&Value::string("a")).unwrap());
    assert!(!diff.contains(&Value::string("b")).unwrap());

    // Enumerable because LHS is finite
    assert!(diff.is_enumerable());
    let set = diff.to_sorted_set().unwrap();
    assert_eq!(set.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setdiff_with_anyset_rhs() {
    // {1, 2, 3} \ ANY -> {} (everything removed)
    let s1 = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let s2 = Value::AnySet;
    let diff = SetDiffValue::new(s1, s2);

    // Membership: nothing remains (ANY contains everything)
    assert!(!diff.contains(&Value::int(1)).unwrap());
    assert!(!diff.contains(&Value::int(2)).unwrap());
    assert!(!diff.contains(&Value::int(3)).unwrap());

    // Enumerable because LHS is finite
    assert!(diff.is_enumerable());
    let set = diff.to_sorted_set().unwrap();
    assert!(set.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_lazy_set_ops_value_enum() {
    // Test that Value enum variants work correctly
    let s1 = Value::set([Value::int(1), Value::int(2)]);
    let s2 = Value::set([Value::int(2), Value::int(3)]);

    // Create lazy set operation values
    let cup = Value::SetCup(SetCupValue::new(s1.clone(), s2.clone()));
    let cap = Value::SetCap(SetCapValue::new(s1.clone(), s2.clone()));
    let diff = Value::SetDiff(SetDiffValue::new(s1.clone(), s2.clone()));

    // All should be considered sets
    assert!(cup.is_set());
    assert!(cap.is_set());
    assert!(diff.is_set());

    // All should support set_contains
    assert!(cup.set_contains(&Value::int(1)).unwrap());
    assert!(cap.set_contains(&Value::int(2)).unwrap());
    assert!(diff.set_contains(&Value::int(1)).unwrap());

    // All should support to_sorted_set
    assert!(cup.to_sorted_set().is_some());
    assert!(cap.to_sorted_set().is_some());
    assert!(diff.to_sorted_set().is_some());
}
