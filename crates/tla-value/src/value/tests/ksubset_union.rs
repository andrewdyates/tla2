// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for KSubsetValue (k-element subsets) and UnionValue (UNION).

use super::super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_basic() {
    // Ksubsets({1, 2, 3}, 2) should have C(3,2) = 3 elements
    let base = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let ksv = KSubsetValue::new(base, 2);

    // Cardinality
    assert_eq!(ksv.len().unwrap(), BigInt::from(3));

    // Enumerable
    assert!(ksv.is_enumerable());

    // Convert to set
    let set = ksv.to_sorted_set().unwrap();
    assert_eq!(set.len(), 3);

    // Each element should be a 2-element set
    for elem in &set {
        let inner = elem.to_sorted_set().unwrap();
        assert_eq!(inner.len(), 2);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_membership() {
    let base = Value::set([Value::int(1), Value::int(2), Value::int(3)]);
    let ksv = KSubsetValue::new(base, 2);

    // Valid 2-element subset
    assert!(ksv
        .contains(&Value::set([Value::int(1), Value::int(2)]))
        .unwrap());
    assert!(ksv
        .contains(&Value::set([Value::int(1), Value::int(3)]))
        .unwrap());
    assert!(ksv
        .contains(&Value::set([Value::int(2), Value::int(3)]))
        .unwrap());

    // Invalid: wrong size
    assert!(!ksv.contains(&Value::set([Value::int(1)])).unwrap());
    assert!(!ksv
        .contains(&Value::set([Value::int(1), Value::int(2), Value::int(3)]))
        .unwrap());

    // Invalid: not a subset of base
    assert!(!ksv
        .contains(&Value::set([Value::int(1), Value::int(4)]))
        .unwrap());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_edge_cases() {
    let base = Value::set([Value::int(1), Value::int(2), Value::int(3)]);

    // k = 0: returns set containing empty set
    let ksv0 = KSubsetValue::new(base.clone(), 0);
    assert_eq!(ksv0.len().unwrap(), BigInt::from(1));
    let set0 = ksv0.to_sorted_set().unwrap();
    assert_eq!(set0.len(), 1);
    assert!(set0.contains(&Value::set(vec![])));
    assert!(ksv0.contains(&Value::set(vec![])).unwrap());

    // k > n: returns empty set
    let ksv5 = KSubsetValue::new(base.clone(), 5);
    assert_eq!(ksv5.len().unwrap(), BigInt::from(0));
    assert!(ksv5.is_empty());
    let set5 = ksv5.to_sorted_set().unwrap();
    assert!(set5.is_empty());

    // k = n: returns set containing the full base set
    let ksv3 = KSubsetValue::new(base.clone(), 3);
    assert_eq!(ksv3.len().unwrap(), BigInt::from(1));
    let set3 = ksv3.to_sorted_set().unwrap();
    assert_eq!(set3.len(), 1);
    assert!(set3.contains(&base));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_value_variant() {
    let base = Value::set([Value::int(1), Value::int(2)]);
    let val = Value::KSubset(KSubsetValue::new(base, 1));

    // Should be recognized as a set
    assert!(val.is_set());

    // set_contains should work
    assert!(val.set_contains(&Value::set([Value::int(1)])).unwrap());
    assert!(val.set_contains(&Value::set([Value::int(2)])).unwrap());
    assert!(!val.set_contains(&Value::set([Value::int(3)])).unwrap());

    // iter_set should work
    let iter_values: Vec<_> = val.iter_set().unwrap().collect();
    assert_eq!(iter_values.len(), 2);
    assert!(iter_values.contains(&Value::set([Value::int(1)])));
    assert!(iter_values.contains(&Value::set([Value::int(2)])));
    assert!(!iter_values.contains(&Value::set([Value::int(1), Value::int(2)])));

    // to_sorted_set should work
    let set = val.to_sorted_set().unwrap();
    assert_eq!(set.len(), 2);
    assert!(set.contains(&Value::set([Value::int(1)])));
    assert!(set.contains(&Value::set([Value::int(2)])));
    assert!(!set.contains(&Value::set([Value::int(1), Value::int(2)])));
}

// === UnionValue Tests ===

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_union_basic() {
    // UNION {{1, 2}, {2, 3}} = {1, 2, 3}
    let set_of_sets = Value::set([
        Value::set([Value::int(1), Value::int(2)]),
        Value::set([Value::int(2), Value::int(3)]),
    ]);
    let uv = UnionValue::new(set_of_sets);

    // Enumerable
    assert!(uv.is_enumerable());

    // Convert to set
    let set = uv.to_sorted_set().unwrap();
    assert_eq!(set.len(), 3);
    assert!(set.contains(&Value::int(1)));
    assert!(set.contains(&Value::int(2)));
    assert!(set.contains(&Value::int(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_union_membership() {
    let set_of_sets = Value::set([
        Value::set([Value::int(1), Value::int(2)]),
        Value::set([Value::int(3), Value::int(4)]),
    ]);
    let uv = UnionValue::new(set_of_sets);

    // Elements in any inner set
    assert!(uv.contains(&Value::int(1)).unwrap());
    assert!(uv.contains(&Value::int(2)).unwrap());
    assert!(uv.contains(&Value::int(3)).unwrap());
    assert!(uv.contains(&Value::int(4)).unwrap());

    // Elements not in any inner set
    assert!(!uv.contains(&Value::int(5)).unwrap());
    assert!(!uv.contains(&Value::int(0)).unwrap());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_union_empty_cases() {
    // UNION {} = {}
    let empty = Value::set(vec![]);
    let uv_empty = UnionValue::new(empty);
    assert!(uv_empty.is_empty());
    let set = uv_empty.to_sorted_set().unwrap();
    assert!(set.is_empty());

    // UNION {{}} = {}
    let set_of_empty = Value::set([Value::set(vec![])]);
    let uv_single_empty = UnionValue::new(set_of_empty);
    assert!(uv_single_empty.is_empty());
    let set2 = uv_single_empty.to_sorted_set().unwrap();
    assert!(set2.is_empty());

    // UNION {{1}, {}} = {1}
    let mixed = Value::set([Value::set([Value::int(1)]), Value::set(vec![])]);
    let uv_mixed = UnionValue::new(mixed);
    assert!(!uv_mixed.is_empty());
    let set3 = uv_mixed.to_sorted_set().unwrap();
    assert_eq!(set3.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_union_value_variant() {
    let set_of_sets = Value::set([Value::set([Value::int(1), Value::int(2)])]);
    let val = Value::BigUnion(UnionValue::new(set_of_sets));

    // Should be recognized as a set
    assert!(val.is_set());

    // set_contains should work
    assert!(val.set_contains(&Value::int(1)).unwrap());
    assert!(val.set_contains(&Value::int(2)).unwrap());
    assert!(!val.set_contains(&Value::int(3)).unwrap());

    // iter_set should work and produce correct values
    let iter_values: Vec<_> = val.iter_set().unwrap().collect();
    assert_eq!(iter_values.len(), 2);
    assert!(iter_values.contains(&Value::int(1)));
    assert!(iter_values.contains(&Value::int(2)));
    assert!(!iter_values.contains(&Value::int(3)));

    // to_sorted_set should work and contain correct values
    let set = val.to_sorted_set().unwrap();
    assert_eq!(set.len(), 2);
    assert!(set.contains(&Value::int(1)));
    assert!(set.contains(&Value::int(2)));
    assert!(!set.contains(&Value::int(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_binomial() {
    // Test binomial coefficient function
    assert_eq!(binomial(5, 0), BigInt::from(1));
    assert_eq!(binomial(5, 1), BigInt::from(5));
    assert_eq!(binomial(5, 2), BigInt::from(10));
    assert_eq!(binomial(5, 3), BigInt::from(10));
    assert_eq!(binomial(5, 4), BigInt::from(5));
    assert_eq!(binomial(5, 5), BigInt::from(1));
    assert_eq!(binomial(5, 6), BigInt::from(0)); // k > n

    // Larger values
    assert_eq!(binomial(10, 5), BigInt::from(252));
    assert_eq!(binomial(20, 10), BigInt::from(184756));
}
