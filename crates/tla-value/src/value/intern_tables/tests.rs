// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::int_funcs::{int_func_intern_table_entry_count, intern_int_func_array};
use super::sets::{intern_set_array, set_intern_table_entry_count};
use super::shared::MAX_INTERN_TABLE_ENTRIES;
use super::{clear_int_func_intern_table, clear_set_intern_table};
use crate::value::{lock_intern_state, Value};

/// Verify that set intern table clears when it exceeds MAX_INTERN_TABLE_ENTRIES.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn set_intern_table_respects_size_cap() {
    let _lock = lock_intern_state();
    clear_set_intern_table();

    for i in 0..=MAX_INTERN_TABLE_ENTRIES {
        let elements = vec![
            Value::SmallInt(i as i64),
            Value::SmallInt((i + 100_000) as i64),
        ];
        intern_set_array(elements);
    }

    let after = set_intern_table_entry_count();
    assert_eq!(
        after, 1,
        "Table should have reset to the boundary insert: got {after} entries"
    );

    intern_set_array(vec![Value::SmallInt(-1), Value::SmallInt(-2)]);
    assert_eq!(
        set_intern_table_entry_count(),
        2,
        "Table should keep accepting inserts after the reset"
    );

    clear_set_intern_table();
}

/// Verify that int func intern table clears when it exceeds MAX_INTERN_TABLE_ENTRIES.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn int_func_intern_table_respects_size_cap() {
    let _lock = lock_intern_state();
    clear_int_func_intern_table();

    for i in 0..=MAX_INTERN_TABLE_ENTRIES {
        let values = vec![
            Value::SmallInt(i as i64),
            Value::SmallInt((i + 10_000) as i64),
        ];
        intern_int_func_array(0, 1, values);
    }

    let after = int_func_intern_table_entry_count();
    assert_eq!(
        after, 1,
        "Table should have reset to the boundary insert: got {after} entries"
    );

    intern_int_func_array(0, 1, vec![Value::SmallInt(-1), Value::SmallInt(-2)]);
    assert_eq!(
        int_func_intern_table_entry_count(),
        2,
        "Table should keep accepting inserts after the reset"
    );

    clear_int_func_intern_table();
}
