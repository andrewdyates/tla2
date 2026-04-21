// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for `FuncValue::compose_perm`.

use super::super::*;

fn int_func(entries: &[(i64, i64)]) -> FuncValue {
    FuncValue::from_sorted_entries(
        entries
            .iter()
            .map(|(key, value)| (Value::int(*key), Value::int(*value)))
            .collect(),
    )
}

fn collected_entries(func: &FuncValue) -> Vec<(Value, Value)> {
    func.iter()
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect()
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compose_perm_merges_overlapping_sorted_domains() {
    let left = int_func(&[(0, 0), (1, 2), (2, 1), (5, 5)]);
    let right = int_func(&[(1, 2), (2, 3), (3, 1)]);

    let composed = left.compose_perm(&right);
    let expected = int_func(&[(0, 0), (1, 1), (2, 3), (3, 2), (5, 5)]);

    assert_eq!(collected_entries(&composed), collected_entries(&expected));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_compose_perm_unions_disjoint_domains() {
    let left = int_func(&[(1, 2), (2, 1)]);
    let right = int_func(&[(3, 4), (4, 3)]);

    let composed = left.compose_perm(&right);
    let expected = int_func(&[(1, 2), (2, 1), (3, 4), (4, 3)]);

    assert_eq!(collected_entries(&composed), collected_entries(&expected));
}
