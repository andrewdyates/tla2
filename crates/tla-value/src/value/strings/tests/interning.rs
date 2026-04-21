// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::intern::{string_intern_table_entry_count, MAX_STRING_INTERN_ENTRIES};
use super::super::{clear_string_intern_table, intern_string};
use std::sync::Arc;

/// Verify that STRING_INTERN_TABLE clears when it exceeds MAX_STRING_INTERN_ENTRIES.
/// Part of #1331: memory safety audit -- unbounded intern tables.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn string_intern_table_respects_size_cap() {
    let _lock = crate::value::lock_intern_state();
    clear_string_intern_table();

    // Insert one more than the cap. The boundary insert should clear the
    // table and leave only the newly inserted string behind.
    for i in 0..=MAX_STRING_INTERN_ENTRIES {
        intern_string(&format!("test_cap_string_{i}"));
    }

    let after = string_intern_table_entry_count();
    assert_eq!(
        after, 1,
        "Table should have reset to the boundary insert: got {after} entries"
    );

    let _ = intern_string("test_cap_string_after_reset");
    assert_eq!(
        string_intern_table_entry_count(),
        2,
        "Table should keep accepting inserts after the reset"
    );

    clear_string_intern_table();
}

/// Verify that clearing the string intern table does not break equality.
/// After clearing, interning the same string should produce content-equal
/// values even though Arc pointers differ.
#[test]
fn string_intern_clear_preserves_equality() {
    let _lock = crate::value::lock_intern_state();
    clear_string_intern_table();

    let before = intern_string("hello");
    clear_string_intern_table();
    let after = intern_string("hello");

    // Arc pointers should differ (cleared table -> new allocation)
    assert!(!Arc::ptr_eq(&before, &after));
    // Content equality must still hold
    assert_eq!(*before, *after);

    clear_string_intern_table();
}
