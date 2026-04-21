// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::value::Value;
use crate::var_index::VarIndex;

#[test]
fn test_merge_from_propagates_instance_lazy_read() {
    let mut base = OpEvalDeps::default();
    assert!(!base.instance_lazy_read);

    let mut tainted = OpEvalDeps::default();
    tainted.instance_lazy_read = true;

    base.merge_from(&tainted);
    assert!(
        base.instance_lazy_read,
        "merge_from must propagate instance_lazy_read taint"
    );
}

#[test]
fn test_merge_from_preserves_existing_taint() {
    let mut base = OpEvalDeps::default();
    base.instance_lazy_read = true;

    let clean = OpEvalDeps::default();
    base.merge_from(&clean);
    assert!(
        base.instance_lazy_read,
        "merging clean deps must not clear existing taint"
    );
}

#[test]
fn test_default_has_no_taint() {
    let deps = OpEvalDeps::default();
    assert!(!deps.instance_lazy_read);
}

// Fix #2414: VarDepMap tests

#[test]
fn test_var_dep_map_record_and_lookup() {
    let mut map = VarDepMap::default();
    assert!(map.is_empty());
    assert_eq!(map.len(), 0);

    // First record: no conflict
    let conflict = map.record(VarIndex::new(3), &Value::int(42));
    assert!(!conflict);
    assert_eq!(map.len(), 1);
    assert!(!map.is_empty());
    assert!(map.contains_key(&VarIndex::new(3)));
    assert!(!map.contains_key(&VarIndex::new(0)));
}

#[test]
fn test_var_dep_map_duplicate_same_value() {
    let mut map = VarDepMap::default();
    map.record(VarIndex::new(2), &Value::int(10));
    // Re-recording same value: no conflict
    let conflict = map.record(VarIndex::new(2), &Value::int(10));
    assert!(!conflict);
    assert_eq!(map.len(), 1); // count unchanged
}

#[test]
fn test_var_dep_map_duplicate_different_value() {
    let mut map = VarDepMap::default();
    map.record(VarIndex::new(2), &Value::int(10));
    // Re-recording different value: conflict
    let conflict = map.record(VarIndex::new(2), &Value::int(99));
    assert!(conflict);
    assert_eq!(map.len(), 1); // count unchanged
}

#[test]
fn test_var_dep_map_iter() {
    let mut map = VarDepMap::default();
    map.record(VarIndex::new(0), &Value::int(1));
    map.record(VarIndex::new(5), &Value::int(2));
    map.record(VarIndex::new(2), &Value::int(3));

    let entries: Vec<_> = map.iter().collect();
    assert_eq!(entries.len(), 3);
    // Iteration is in index order; yields CompactValue references.
    let cv = |v: i64| tla_value::CompactValue::from(v);
    assert_eq!(entries[0], (VarIndex::new(0), &cv(1)));
    assert_eq!(entries[1], (VarIndex::new(2), &cv(3)));
    assert_eq!(entries[2], (VarIndex::new(5), &cv(2)));
}

#[test]
fn test_var_dep_map_from_entries() {
    let map = VarDepMap::from_entries(&[
        (VarIndex::new(1), Value::int(10)),
        (VarIndex::new(3), Value::int(30)),
    ]);
    assert_eq!(map.len(), 2);
    assert!(map.contains_key(&VarIndex::new(1)));
    assert!(map.contains_key(&VarIndex::new(3)));
    assert!(!map.contains_key(&VarIndex::new(2)));
}

#[test]
fn test_merge_from_state_uses_var_dep_map() {
    let mut base = OpEvalDeps::default();
    base.record_state(VarIndex::new(0), &Value::int(1));

    let mut other = OpEvalDeps::default();
    other.record_state(VarIndex::new(1), &Value::int(2));

    base.merge_from(&other);
    assert_eq!(base.state.len(), 2);
    assert!(base.state.contains_key(&VarIndex::new(0)));
    assert!(base.state.contains_key(&VarIndex::new(1)));
}

#[test]
fn test_merge_from_detects_state_inconsistency() {
    let mut base = OpEvalDeps::default();
    base.record_state(VarIndex::new(0), &Value::int(1));

    let mut other = OpEvalDeps::default();
    other.record_state(VarIndex::new(0), &Value::int(99));

    base.merge_from(&other);
    assert!(base.inconsistent);
    assert!(base.state_next_inconsistent);
}
