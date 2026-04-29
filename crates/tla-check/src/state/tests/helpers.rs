// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn create_swap_permutation(a: &str, b: &str) -> FuncValue {
    let mut entries = vec![
        (
            Value::try_model_value(a).unwrap(),
            Value::try_model_value(b).unwrap(),
        ),
        (
            Value::try_model_value(b).unwrap(),
            Value::try_model_value(a).unwrap(),
        ),
    ];
    entries.sort_by(|(ka, _), (kb, _)| ka.cmp(kb));
    FuncValue::from_sorted_entries(entries)
}

pub(super) fn create_cycle_permutation(a: &str, b: &str, c: &str) -> FuncValue {
    let mut entries = vec![
        (
            Value::try_model_value(a).unwrap(),
            Value::try_model_value(b).unwrap(),
        ),
        (
            Value::try_model_value(b).unwrap(),
            Value::try_model_value(c).unwrap(),
        ),
        (
            Value::try_model_value(c).unwrap(),
            Value::try_model_value(a).unwrap(),
        ),
    ];
    entries.sort_by(|(ka, _), (kb, _)| ka.cmp(kb));
    FuncValue::from_sorted_entries(entries)
}

pub(super) fn fnv_hash(value: &Value) -> u64 {
    hash_value(FNV_OFFSET, value)
}
