// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Record additive fingerprint cache preservation tests (Part of #3221).
//!
//! Verifies that record update operations (update_existing_field_id,
//! take/restore, insert) correctly preserve the additive fingerprint cache.

use crate::RecordValue;
use crate::Value;
use std::sync::Arc;
use tla_core::intern_name;

use super::state_value_fingerprint_unwrap;

// ---------------------------------------------------------------------------
// Record additive fingerprint tests (Part of #3221)
// ---------------------------------------------------------------------------

fn sample_record() -> RecordValue {
    RecordValue::from_sorted_entries(vec![
        (intern_name("color"), Value::String(Arc::from("black"))),
        (intern_name("q"), Value::SmallInt(0)),
        (intern_name("type"), Value::String(Arc::from("tok"))),
    ])
}

fn cache_record_state_fp(rec: &RecordValue) -> u64 {
    let fp = state_value_fingerprint_unwrap(&Value::Record(rec.clone()));
    rec.cache_additive_fp(fp);
    fp
}

/// Part of #3221: update_existing_field_id preserves additive cache via delta.
#[test]
fn test_record_update_preserves_additive_cache() {
    let record = sample_record();
    cache_record_state_fp(&record);

    let updated = record
        .clone()
        .update_existing_field_id(intern_name("q"), Value::SmallInt(42));

    // The updated record should have an additive cache (not None)
    assert!(
        updated.get_additive_fp().is_some(),
        "additive cache should be preserved after update_existing_field_id"
    );

    // Verify it matches a fresh computation
    let expected =
        state_value_fingerprint_unwrap(&Value::Record(RecordValue::from_sorted_entries(vec![
            (intern_name("color"), Value::String(Arc::from("black"))),
            (intern_name("q"), Value::SmallInt(42)),
            (intern_name("type"), Value::String(Arc::from("tok"))),
        ])));
    assert_eq!(
        updated.get_additive_fp(),
        Some(expected),
        "preserved additive cache should match fresh computation"
    );
}

/// Part of #3221: take/restore preserves additive cache via old_entry_hash delta.
#[test]
fn test_record_take_restore_preserves_additive_cache() {
    let mut record = sample_record();
    cache_record_state_fp(&record);

    let field_id = intern_name("q");
    let (old_val, pos, old_entry_hash) = record
        .take_at_field_id(field_id)
        .expect("field q should exist");
    assert_eq!(old_val, Value::SmallInt(0));
    assert!(
        old_entry_hash.is_some(),
        "old_entry_hash should be Some when additive cache exists"
    );

    record.restore_at(pos, old_entry_hash, Value::SmallInt(42));

    let expected =
        state_value_fingerprint_unwrap(&Value::Record(RecordValue::from_sorted_entries(vec![
            (intern_name("color"), Value::String(Arc::from("black"))),
            (intern_name("q"), Value::SmallInt(42)),
            (intern_name("type"), Value::String(Arc::from("tok"))),
        ])));
    assert_eq!(
        record.get_additive_fp(),
        Some(expected),
        "take/restore should produce correct additive fingerprint"
    );
}

/// Part of #3221: insert (replace existing) preserves additive cache.
#[test]
fn test_record_insert_replace_preserves_additive_cache() {
    let record = sample_record();
    cache_record_state_fp(&record);

    let updated = record.insert(intern_name("q"), Value::SmallInt(99));

    assert!(
        updated.get_additive_fp().is_some(),
        "additive cache should be preserved after insert-replace"
    );

    let expected =
        state_value_fingerprint_unwrap(&Value::Record(RecordValue::from_sorted_entries(vec![
            (intern_name("color"), Value::String(Arc::from("black"))),
            (intern_name("q"), Value::SmallInt(99)),
            (intern_name("type"), Value::String(Arc::from("tok"))),
        ])));
    assert_eq!(updated.get_additive_fp(), Some(expected));
}

/// Part of #3221: insert (new field) preserves additive cache with length adjustment.
#[test]
fn test_record_insert_new_field_preserves_additive_cache() {
    let record = sample_record();
    cache_record_state_fp(&record);

    let updated = record.insert(intern_name("active"), Value::Bool(true));

    assert!(
        updated.get_additive_fp().is_some(),
        "additive cache should be preserved after insert-new-field"
    );

    let expected =
        state_value_fingerprint_unwrap(&Value::Record(RecordValue::from_sorted_entries(vec![
            (intern_name("active"), Value::Bool(true)),
            (intern_name("color"), Value::String(Arc::from("black"))),
            (intern_name("q"), Value::SmallInt(0)),
            (intern_name("type"), Value::String(Arc::from("tok"))),
        ])));
    assert_eq!(updated.get_additive_fp(), Some(expected));
}

/// Part of #3221 + #3285: FP64 and additive produce different results for records.
/// FP64 no longer cached per #3285; additive still cached.
#[test]
fn test_record_fp64_and_additive_produce_different_results() {
    use crate::fingerprint::value_fingerprint;

    let rec_val = Value::Record(sample_record());

    let fp64 = value_fingerprint(&rec_val).unwrap();
    let additive = state_value_fingerprint_unwrap(&rec_val);

    let Value::Record(ref record) = rec_val else {
        unreachable!()
    };
    // Additive is cached; FP64 is recomputed on demand
    assert_eq!(record.get_additive_fp(), Some(additive));

    // The two must differ (different algorithms)
    assert_ne!(
        fp64, additive,
        "FP64 and additive fingerprints should differ for non-trivial records"
    );
}

/// Part of #3221 + #3285: same-value update preserves additive cache (clone path).
/// FP64 cache removed per #3285.
#[test]
fn test_record_same_value_update_preserves_additive_cache() {
    let record = sample_record();
    cache_record_state_fp(&record);

    let result = record
        .clone()
        .update_existing_field_id(intern_name("q"), Value::SmallInt(0));

    assert!(result.ptr_eq(&record));
    assert!(result.get_additive_fp().is_some());
}
