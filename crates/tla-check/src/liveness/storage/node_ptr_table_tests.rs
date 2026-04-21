// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for [`NodePtrTable`].

#![allow(clippy::float_cmp)] // load_factor returns exact rational results (e.g. 3/4 = 0.75)

use super::*;

fn make_fp(v: u64) -> Fingerprint {
    Fingerprint(v)
}

#[test]
fn test_insert_and_get_single() {
    let mut table = NodePtrTable::new(64, None).unwrap();
    assert!(table.is_empty());

    let result = table.insert(make_fp(42), 0, 100).unwrap();
    assert!(result); // newly inserted
    assert_eq!(table.len(), 1);
    assert_eq!(table.get(make_fp(42), 0), Some(100));
}

#[test]
fn test_update_existing_key() {
    let mut table = NodePtrTable::new(64, None).unwrap();

    assert!(table.insert(make_fp(42), 0, 100).unwrap());
    assert!(!table.insert(make_fp(42), 0, 200).unwrap()); // update
    assert_eq!(table.len(), 1);
    assert_eq!(table.get(make_fp(42), 0), Some(200));
}

#[test]
fn test_same_fp_different_tidx() {
    let mut table = NodePtrTable::new(64, None).unwrap();

    assert!(table.insert(make_fp(42), 0, 100).unwrap());
    assert!(table.insert(make_fp(42), 1, 200).unwrap());
    assert!(table.insert(make_fp(42), 2, 300).unwrap());

    assert_eq!(table.len(), 3);
    assert_eq!(table.get(make_fp(42), 0), Some(100));
    assert_eq!(table.get(make_fp(42), 1), Some(200));
    assert_eq!(table.get(make_fp(42), 2), Some(300));
}

#[test]
fn test_different_fp_same_tidx() {
    let mut table = NodePtrTable::new(64, None).unwrap();

    assert!(table.insert(make_fp(10), 0, 100).unwrap());
    assert!(table.insert(make_fp(20), 0, 200).unwrap());
    assert!(table.insert(make_fp(30), 0, 300).unwrap());

    assert_eq!(table.get(make_fp(10), 0), Some(100));
    assert_eq!(table.get(make_fp(20), 0), Some(200));
    assert_eq!(table.get(make_fp(30), 0), Some(300));
}

#[test]
fn test_missing_key_returns_none() {
    let mut table = NodePtrTable::new(64, None).unwrap();
    table.insert(make_fp(42), 0, 100).unwrap();

    assert_eq!(table.get(make_fp(42), 1), None); // wrong tidx
    assert_eq!(table.get(make_fp(99), 0), None); // wrong fp
    assert_eq!(table.get(make_fp(99), 1), None); // both wrong
}

#[test]
fn test_contains() {
    let mut table = NodePtrTable::new(64, None).unwrap();
    table.insert(make_fp(42), 0, 100).unwrap();

    assert!(table.contains(make_fp(42), 0));
    assert!(!table.contains(make_fp(42), 1));
    assert!(!table.contains(make_fp(99), 0));
}

#[test]
fn test_zero_fingerprint() {
    let mut table = NodePtrTable::new(64, None).unwrap();

    // FP(0) goes through the side-channel.
    assert!(table.insert(make_fp(0), 0, 100).unwrap());
    assert!(table.insert(make_fp(0), 1, 200).unwrap());
    assert_eq!(table.len(), 2);

    assert_eq!(table.get(make_fp(0), 0), Some(100));
    assert_eq!(table.get(make_fp(0), 1), Some(200));
    assert_eq!(table.get(make_fp(0), 2), None);
}

#[test]
fn test_zero_fingerprint_update() {
    let mut table = NodePtrTable::new(64, None).unwrap();

    assert!(table.insert(make_fp(0), 0, 100).unwrap());
    assert!(!table.insert(make_fp(0), 0, 999).unwrap()); // update
    assert_eq!(table.len(), 1);
    assert_eq!(table.get(make_fp(0), 0), Some(999));
}

#[test]
fn test_zero_fingerprint_entries_do_not_consume_hash_table_capacity() {
    let mut table = NodePtrTable::new(4, None).unwrap();

    assert!(table.insert(make_fp(0), 0, 100).unwrap());
    assert!(table.insert(make_fp(0), 1, 200).unwrap());
    assert_eq!(table.load_factor(), 0.0);

    assert!(table.insert(make_fp(1), 0, 10).unwrap());
    assert!(table.insert(make_fp(2), 0, 20).unwrap());
    assert!(table.insert(make_fp(3), 0, 30).unwrap());
    assert_eq!(table.load_factor(), 0.75);
    assert_eq!(table.len(), 5);

    let result = table.insert(make_fp(4), 0, 40);
    assert!(result.is_err());
}

#[test]
fn test_hash_collision_probe_chain() {
    // With a small capacity, hash collisions are guaranteed.
    let mut table = NodePtrTable::new(8, None).unwrap();

    // Insert several entries that will collide.
    for i in 1u64..=5 {
        table.insert(make_fp(i), 0, i * 10).unwrap();
    }

    assert_eq!(table.len(), 5);
    for i in 1u64..=5 {
        assert_eq!(table.get(make_fp(i), 0), Some(i * 10));
    }
}

#[test]
fn test_load_factor_enforcement() {
    let mut table = NodePtrTable::new(4, None).unwrap();

    // With capacity 4 and load factor 0.75, we can insert 3 entries.
    assert!(table.insert(make_fp(1), 0, 10).unwrap());
    assert!(table.insert(make_fp(2), 0, 20).unwrap());
    assert!(table.insert(make_fp(3), 0, 30).unwrap());

    // The 4th should fail (3/4 = 0.75, at the threshold).
    let result = table.insert(make_fp(4), 0, 40);
    assert!(result.is_err());
}

#[test]
fn test_update_existing_key_at_load_factor_threshold() {
    let mut table = NodePtrTable::new(4, None).unwrap();

    assert!(table.insert(make_fp(1), 0, 10).unwrap());
    assert!(table.insert(make_fp(2), 0, 20).unwrap());
    assert!(table.insert(make_fp(3), 0, 30).unwrap());

    // Rewrites must succeed even after the table is full for new inserts.
    assert!(!table.insert(make_fp(2), 0, 99).unwrap());
    assert_eq!(table.get(make_fp(2), 0), Some(99));
    assert_eq!(table.len(), 3);
}

#[test]
fn test_mixed_fp_and_tidx() {
    let mut table = NodePtrTable::new(128, None).unwrap();

    // Simulate a small liveness graph: 10 states × 3 tableau nodes.
    for state in 1u64..=10 {
        for tidx in 0..3 {
            let offset = state * 1000 + tidx as u64;
            table.insert(make_fp(state), tidx, offset).unwrap();
        }
    }

    assert_eq!(table.len(), 30);

    for state in 1u64..=10 {
        for tidx in 0..3 {
            let expected = state * 1000 + tidx as u64;
            assert_eq!(table.get(make_fp(state), tidx), Some(expected));
        }
    }
}

#[test]
fn test_file_backed_mapping() {
    let dir = tempfile::tempdir().unwrap();
    let mut table = NodePtrTable::new(64, Some(dir.path().to_path_buf())).unwrap();

    table.insert(make_fp(42), 0, 100).unwrap();
    table.insert(make_fp(42), 1, 200).unwrap();
    table.flush().unwrap();

    assert_eq!(table.get(make_fp(42), 0), Some(100));
    assert_eq!(table.get(make_fp(42), 1), Some(200));
}

#[test]
fn test_load_factor_metric() {
    let mut table = NodePtrTable::new(100, None).unwrap();
    assert_eq!(table.load_factor(), 0.0);

    for i in 1u64..=10 {
        table.insert(make_fp(i), 0, i).unwrap();
    }
    let lf = table.load_factor();
    assert!((lf - 0.10).abs() < 0.001);
}

#[test]
fn test_large_tableau_index() {
    let mut table = NodePtrTable::new(64, None).unwrap();

    // Tableau indices can be large in theory (though typically small).
    table.insert(make_fp(1), 10_000, 999).unwrap();
    assert_eq!(table.get(make_fp(1), 10_000), Some(999));
    assert_eq!(table.get(make_fp(1), 0), None);
}
