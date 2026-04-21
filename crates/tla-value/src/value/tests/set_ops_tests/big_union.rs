// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! UnionValue (BigUnion / UNION S) coverage — outer-set traversal,
//! emptiness, and deduplicating materialization.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_union_contains_element_from_inner_set() {
    // UNION {{1, 2}, {3, 4}} = {1, 2, 3, 4}
    let inner1 = Value::set([Value::int(1), Value::int(2)]);
    let inner2 = Value::set([Value::int(3), Value::int(4)]);
    let outer = Value::set([inner1, inner2]);
    let union = UnionValue::new(outer);

    assert_eq!(union.contains(&Value::int(1)), Some(true));
    assert_eq!(union.contains(&Value::int(3)), Some(true));
    assert_eq!(union.contains(&Value::int(5)), Some(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_union_is_empty_all_inner_empty() {
    let inner1 = Value::set(std::iter::empty::<Value>());
    let inner2 = Value::set(std::iter::empty::<Value>());
    let outer = Value::set([inner1, inner2]);
    let union = UnionValue::new(outer);

    assert!(union.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_union_to_sorted_set_deduplicates() {
    // UNION {{1, 2}, {2, 3}} should give {1, 2, 3}
    let inner1 = Value::set([Value::int(1), Value::int(2)]);
    let inner2 = Value::set([Value::int(2), Value::int(3)]);
    let outer = Value::set([inner1, inner2]);
    let union = UnionValue::new(outer);

    let sorted = union.to_sorted_set().expect("should be enumerable");
    assert_eq!(sorted.len(), 3);

    // Verify actual element contents, not just length
    assert!(
        sorted.contains(&Value::int(1)),
        "UNION result should contain 1"
    );
    assert!(
        sorted.contains(&Value::int(2)),
        "UNION result should contain 2"
    );
    assert!(
        sorted.contains(&Value::int(3)),
        "UNION result should contain 3"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_union_to_sorted_set_full_overlap() {
    // UNION {{1, 2}, {1, 2}} should give {1, 2}
    let inner1 = Value::set([Value::int(1), Value::int(2)]);
    let inner2 = Value::set([Value::int(1), Value::int(2)]);
    let outer = Value::set([inner1, inner2]);
    let union = UnionValue::new(outer);

    let sorted = union.to_sorted_set().expect("should be enumerable");
    assert_eq!(
        sorted.len(),
        2,
        "UNION of identical sets should deduplicate"
    );
    assert!(sorted.contains(&Value::int(1)));
    assert!(sorted.contains(&Value::int(2)));
}
