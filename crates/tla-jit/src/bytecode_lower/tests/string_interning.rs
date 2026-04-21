// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the JIT string interning table.

use crate::bytecode_lower::string_intern::StringInternTable;
use std::sync::Arc;

#[test]
fn test_intern_returns_positive_id() {
    let mut table = StringInternTable::new();
    let s: Arc<str> = Arc::from("hello");
    let id = table.get_or_intern(&s);
    assert!(id > 0, "interned ID must be positive, got {id}");
}

#[test]
fn test_same_string_same_id() {
    let mut table = StringInternTable::new();
    let s: Arc<str> = Arc::from("hello");
    let id1 = table.get_or_intern(&s);
    let id2 = table.get_or_intern(&s);
    assert_eq!(
        id1, id2,
        "interning the same string twice must return the same ID"
    );
}

#[test]
fn test_different_strings_different_ids() {
    let mut table = StringInternTable::new();
    let a: Arc<str> = Arc::from("alice");
    let b: Arc<str> = Arc::from("bob");
    let id_a = table.get_or_intern(&a);
    let id_b = table.get_or_intern(&b);
    assert_ne!(id_a, id_b, "distinct strings must get distinct IDs");
}

#[test]
fn test_get_id_existing() {
    let mut table = StringInternTable::new();
    let s: Arc<str> = Arc::from("present");
    let id = table.get_or_intern(&s);
    assert_eq!(table.get_id("present"), Some(id));
}

#[test]
fn test_get_id_missing() {
    let table = StringInternTable::new();
    assert_eq!(table.get_id("absent"), None);
}

#[test]
fn test_roundtrip() {
    let mut table = StringInternTable::new();
    let s: Arc<str> = Arc::from("roundtrip");
    let id = table.get_or_intern(&s);
    let recovered = table
        .get_str(id)
        .expect("get_str should return the interned string");
    assert_eq!(&**recovered, "roundtrip");
}

#[test]
fn test_empty_string() {
    let mut table = StringInternTable::new();
    let s: Arc<str> = Arc::from("");
    let id = table.get_or_intern(&s);
    assert!(id > 0, "empty string ID must be positive, got {id}");
    let recovered = table
        .get_str(id)
        .expect("get_str should return the empty string");
    assert_eq!(&**recovered, "");
}

#[test]
fn test_len_and_is_empty() {
    let mut table = StringInternTable::new();
    assert!(table.is_empty());
    assert_eq!(table.len(), 0);

    let s: Arc<str> = Arc::from("x");
    table.get_or_intern(&s);
    assert!(!table.is_empty());
    assert_eq!(table.len(), 1);

    // Re-interning does not increase length
    table.get_or_intern(&s);
    assert_eq!(table.len(), 1);
}

#[test]
fn test_get_str_reserved_zero() {
    let table = StringInternTable::new();
    assert!(
        table.get_str(0).is_none(),
        "ID 0 is reserved and must return None"
    );
}

#[test]
fn test_get_str_negative_id() {
    let table = StringInternTable::new();
    assert!(table.get_str(-1).is_none(), "negative IDs must return None");
}
