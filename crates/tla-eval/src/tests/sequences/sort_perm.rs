// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_sortseq() {
    // SortSeq(s, Op) - sort sequence using comparator
    // Ascending order
    assert_eq!(
        eval_with_ops(
            "LessThan(a, b) == a < b",
            "SortSeq(<<3, 1, 4, 1, 5>>, LessThan)"
        )
        .unwrap(),
        Value::seq([
            Value::int(1),
            Value::int(1),
            Value::int(3),
            Value::int(4),
            Value::int(5)
        ])
    );

    // Built-in operator reference
    assert_eq!(
        eval_str("SortSeq(<<3, 1, 4, 1, 5>>, <)").unwrap(),
        Value::seq([
            Value::int(1),
            Value::int(1),
            Value::int(3),
            Value::int(4),
            Value::int(5)
        ])
    );
    assert_eq!(
        eval_str("SortSeq(<<3, 1, 4, 1, 5>>, \\leq)").unwrap(),
        Value::seq([
            Value::int(1),
            Value::int(1),
            Value::int(3),
            Value::int(4),
            Value::int(5)
        ])
    );
    // Descending order
    assert_eq!(
        eval_with_ops(
            "GreaterThan(a, b) == a > b",
            "SortSeq(<<3, 1, 4, 1, 5>>, GreaterThan)"
        )
        .unwrap(),
        Value::seq([
            Value::int(5),
            Value::int(4),
            Value::int(3),
            Value::int(1),
            Value::int(1)
        ])
    );

    // Empty sequence
    assert_eq!(
        eval_with_ops("LessThan(a, b) == a < b", "SortSeq(<<>>, LessThan)").unwrap(),
        Value::seq([])
    );

    // Single element
    assert_eq!(
        eval_with_ops("LessThan(a, b) == a < b", "SortSeq(<<42>>, LessThan)").unwrap(),
        Value::seq([Value::int(42)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_settosortseq() {
    // SetToSortSeq(S, Op) - sort set into a sequence using comparator
    assert_eq!(
        eval_with_ops(
            "LessThan(a, b) == a < b",
            "SetToSortSeq({3, 1, 4, 2}, LessThan)"
        )
        .unwrap(),
        Value::seq([Value::int(1), Value::int(2), Value::int(3), Value::int(4)])
    );

    // Built-in operator reference
    assert_eq!(
        eval_str("SetToSortSeq({3, 1, 4, 2}, <)").unwrap(),
        Value::seq([Value::int(1), Value::int(2), Value::int(3), Value::int(4)])
    );
    assert_eq!(
        eval_str("SetToSortSeq({3, 1, 4, 2}, \\leq)").unwrap(),
        Value::seq([Value::int(1), Value::int(2), Value::int(3), Value::int(4)])
    );
    assert_eq!(
        eval_str("SetToSortSeq({3, 1, 4, 2}, >)").unwrap(),
        Value::seq([Value::int(4), Value::int(3), Value::int(2), Value::int(1)])
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_permutations() {
    // Permutations of empty set: just the empty function
    let empty_perms = eval_str("Permutations({})").unwrap();
    let empty_set = empty_perms.as_set().unwrap();
    assert_eq!(empty_set.len(), 1);
    // Check it contains the empty function
    for v in empty_set.iter() {
        assert!(v.as_func().is_some());
        let f = v.as_func().unwrap();
        assert!(f.domain_is_empty());
    }

    // Permutations of single element: identity function only
    let single_perms = eval_str("Permutations({1})").unwrap();
    let single_set = single_perms.as_set().unwrap();
    assert_eq!(single_set.len(), 1);
    // Check the function maps 1 |-> 1
    for v in single_set.iter() {
        let f = v.as_func().unwrap();
        assert_eq!(f.mapping_get(&Value::int(1)), Some(&Value::int(1)));
    }

    // Permutations of two elements: {1, 2} -> 2! = 2 permutation functions
    // [1 |-> 1, 2 |-> 2] (identity) and [1 |-> 2, 2 |-> 1] (swap)
    let two_perms = eval_str("Permutations({1, 2})").unwrap();
    let two_set = two_perms.as_set().unwrap();
    assert_eq!(two_set.len(), 2);
    // Verify both mappings are valid bijections on {1,2}
    let mut two_mappings: Vec<(i64, i64)> = two_set
        .iter()
        .map(|v| {
            let f = v.as_func().unwrap();
            let a = f.mapping_get(&Value::int(1)).unwrap().as_i64().unwrap();
            let b = f.mapping_get(&Value::int(2)).unwrap().as_i64().unwrap();
            (a, b)
        })
        .collect();
    two_mappings.sort();
    assert_eq!(
        two_mappings,
        vec![(1, 2), (2, 1)],
        "expected identity and swap"
    );

    // Permutations of three elements: 3! = 6 permutation functions
    let three_perms = eval_str("Permutations({1, 2, 3})").unwrap();
    let three_set = three_perms.as_set().unwrap();
    assert_eq!(three_set.len(), 6);
    // All should be bijections [S -> S] with distinct mappings
    let mut three_mappings: Vec<(i64, i64, i64)> = three_set
        .iter()
        .map(|v| {
            let f = v.as_func().unwrap();
            assert_eq!(f.domain_len(), 3);
            let a = f.mapping_get(&Value::int(1)).unwrap().as_i64().unwrap();
            let b = f.mapping_get(&Value::int(2)).unwrap().as_i64().unwrap();
            let c = f.mapping_get(&Value::int(3)).unwrap().as_i64().unwrap();
            // Each must map onto {1,2,3} (bijection)
            let mut vals = vec![a, b, c];
            vals.sort();
            assert_eq!(vals, vec![1, 2, 3], "not a bijection: ({a},{b},{c})");
            (a, b, c)
        })
        .collect();
    three_mappings.sort();
    let expected = vec![
        (1, 2, 3),
        (1, 3, 2),
        (2, 1, 3),
        (2, 3, 1),
        (3, 1, 2),
        (3, 2, 1),
    ];
    assert_eq!(
        three_mappings, expected,
        "wrong set of 3-element permutations"
    );
}
