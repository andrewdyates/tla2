// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for record EXCEPT/update fast paths.
//!
//! Part of #3063: record-field updates should preserve storage on no-op updates
//! and use the owned `Arc::make_mut` fast path when the record is uniquely owned.

use tla_core::intern_name;

use crate::value::{RecordValue, Value};

fn sample_record() -> RecordValue {
    RecordValue::from_sorted_entries(vec![
        (intern_name("a"), Value::SmallInt(1)),
        (intern_name("b"), Value::SmallInt(2)),
    ])
}

#[test]
fn test_record_update_existing_field_id_same_value_reuses_storage() {
    let record = sample_record();

    let result = record
        .clone()
        .update_existing_field_id(intern_name("a"), Value::SmallInt(1));

    assert!(result.ptr_eq(&record));
    assert_eq!(
        result.get_by_id(intern_name("a")),
        Some(&Value::SmallInt(1))
    );
}

#[test]
fn test_record_update_existing_field_id_changed_value_reuses_unique_buffer() {
    let record = sample_record();
    let b_id = intern_name("b");
    let before_ptr = record
        .get_by_id(b_id)
        .expect("field b should exist before update") as *const Value;

    let result = record.update_existing_field_id(intern_name("a"), Value::SmallInt(99));
    let after_ptr = result
        .get_by_id(b_id)
        .expect("field b should exist after update") as *const Value;

    assert_eq!(
        after_ptr, before_ptr,
        "unique-owner update should keep the existing record buffer"
    );
    assert_eq!(
        result.get_by_id(intern_name("a")),
        Some(&Value::SmallInt(99))
    );
}

#[test]
fn test_record_update_existing_field_id_clones_when_storage_is_shared() {
    let record = sample_record();
    let shared = record.clone();

    let result = record.update_existing_field_id(intern_name("a"), Value::SmallInt(99));

    assert!(!result.ptr_eq(&shared));
    assert_eq!(
        shared.get_by_id(intern_name("a")),
        Some(&Value::SmallInt(1))
    );
    assert_eq!(
        result.get_by_id(intern_name("a")),
        Some(&Value::SmallInt(99))
    );
}

#[test]
fn test_record_update_existing_field_id_missing_field_is_noop() {
    let record = sample_record();

    let result = record
        .clone()
        .update_existing_field_id(intern_name("missing"), Value::SmallInt(99));

    assert!(result.ptr_eq(&record));
    assert_eq!(
        result.get_by_id(intern_name("a")),
        Some(&Value::SmallInt(1))
    );
    assert_eq!(
        result.get_by_id(intern_name("b")),
        Some(&Value::SmallInt(2))
    );
    assert_eq!(result.get_by_id(intern_name("missing")), None);
}
