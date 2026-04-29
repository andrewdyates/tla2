// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `collect_fingerprints` on all production backends.
//! Part of #2893.

use super::fp;
use super::*;

use std::collections::HashSet;

fn collected_u64s(fps: &[Fingerprint]) -> HashSet<u64> {
    fps.iter().map(|f| f.0).collect()
}

fn assert_checkpoint_collect_contains_full_range(collected: &HashSet<u64>, context: &str) {
    let swapped_one = 1u64.swap_bytes();
    assert_eq!(
        collected.len(),
        80,
        "{context}: checkpoint collect changed cardinality; swapped fp {swapped_one} present={}",
        collected.contains(&swapped_one)
    );
    assert!(
        collected.contains(&1),
        "{context}: missing fp 1 after checkpoint collect; swapped fp {swapped_one} present={}",
        collected.contains(&swapped_one)
    );
    for value in 1u64..=80 {
        assert!(
            collected.contains(&value),
            "{context}: missing fp {value} after checkpoint collect"
        );
    }
}

// ========== InMemory (via FingerprintStorage) ==========

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_fingerprints_in_memory_empty() {
    let storage = FingerprintStorage::in_memory();
    let fps = storage.collect_fingerprints().expect("in-memory collect");
    assert!(fps.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_fingerprints_in_memory_returns_all() {
    let storage = FingerprintStorage::in_memory();
    storage.insert_checked(fp(100));
    storage.insert_checked(fp(200));
    storage.insert_checked(fp(300));

    let fps = storage.collect_fingerprints().expect("in-memory collect");
    assert_eq!(collected_u64s(&fps), HashSet::from([100, 200, 300]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_fingerprints_in_memory_no_duplicates_after_double_insert() {
    let storage = FingerprintStorage::in_memory();
    storage.insert_checked(fp(42));
    storage.insert_checked(fp(42)); // duplicate

    let fps = storage.collect_fingerprints().expect("in-memory collect");
    assert_eq!(fps.len(), 1);
    assert_eq!(fps[0], fp(42));
}

// ========== MmapFingerprintSet ==========

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_fingerprints_mmap_empty() {
    let set = MmapFingerprintSet::new(100, None).expect("mmap new");
    let fps = FingerprintSet::collect_fingerprints(&set).expect("mmap collect");
    assert!(fps.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_fingerprints_mmap_returns_all() {
    let set = MmapFingerprintSet::new(100, None).expect("mmap new");
    set.insert(fp(10)).expect("insert 10");
    set.insert(fp(20)).expect("insert 20");
    set.insert(fp(30)).expect("insert 30");

    let fps = FingerprintSet::collect_fingerprints(&set).expect("mmap collect");
    assert_eq!(collected_u64s(&fps), HashSet::from([10, 20, 30]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_fingerprints_mmap_includes_zero() {
    let set = MmapFingerprintSet::new(100, None).expect("mmap new");
    set.insert(fp(0)).expect("insert 0");
    set.insert(fp(1)).expect("insert 1");

    let fps = FingerprintSet::collect_fingerprints(&set).expect("mmap collect");
    let collected = collected_u64s(&fps);
    assert!(collected.contains(&0), "FP(0) must be included");
    assert!(collected.contains(&1));
    assert_eq!(collected.len(), 2);
}

// ========== FingerprintStorage::Mmap (trait delegation) ==========

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_fingerprints_storage_mmap_delegation() {
    let storage = FingerprintStorage::mmap(100, None).expect("storage mmap new");
    storage.insert_checked(fp(42));
    storage.insert_checked(fp(43));

    let fps = FingerprintSet::collect_fingerprints(&storage).expect("mmap collect");
    assert_eq!(collected_u64s(&fps), HashSet::from([42, 43]));
}

// ========== ShardedFingerprintSet (in-memory shards) ==========

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_fingerprints_sharded_empty() {
    let set = ShardedFingerprintSet::new(4);
    let fps = FingerprintSet::collect_fingerprints(&set).expect("sharded collect");
    assert!(fps.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_fingerprints_sharded_returns_all() {
    let set = ShardedFingerprintSet::new(4);
    for i in 0..100 {
        set.insert_checked(fp(i));
    }

    let fps = FingerprintSet::collect_fingerprints(&set).expect("sharded collect");
    let collected = collected_u64s(&fps);
    assert_eq!(collected.len(), 100);
    for i in 0..100 {
        assert!(collected.contains(&i), "missing fp {i}");
    }
}

// ========== DiskFingerprintSet (primary only, no eviction) ==========

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_fingerprints_disk_primary_only() {
    let dir = tempfile::tempdir().expect("tempdir");
    let set = DiskFingerprintSet::new(1000, dir.path()).expect("disk new");

    set.insert_checked(fp(10));
    set.insert_checked(fp(20));
    set.insert_checked(fp(30));

    let fps = FingerprintSet::collect_fingerprints(&set).expect("disk collect");
    assert_eq!(collected_u64s(&fps), HashSet::from([10, 20, 30]));
}

// ========== FingerprintStorage::Disk (trait delegation) ==========

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_fingerprints_storage_disk_delegation() {
    let dir = tempfile::tempdir().expect("tempdir");
    let storage = FingerprintStorage::disk(1000, dir.path()).expect("disk new");
    storage.insert_checked(fp(7));
    storage.insert_checked(fp(8));

    let fps = FingerprintSet::collect_fingerprints(&storage).expect("disk collect");
    assert_eq!(collected_u64s(&fps), HashSet::from([7, 8]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_fingerprints_disk_includes_evicted_and_primary_entries() {
    let dir = tempfile::tempdir().expect("tempdir");
    let set = DiskFingerprintSet::new(100, dir.path()).expect("disk new");

    for value in 1u64..=80 {
        assert_eq!(set.insert_checked(fp(value)), InsertOutcome::Inserted);
    }
    assert!(set.eviction_count() >= 1, "test must trigger disk eviction");

    FingerprintSet::begin_checkpoint(&set).expect("disk begin checkpoint");
    let fps = FingerprintSet::collect_fingerprints(&set).expect("disk collect");
    let collected = collected_u64s(&fps);

    assert_checkpoint_collect_contains_full_range(&collected, "disk+primary collect");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_fingerprints_storage_disk_delegation_after_eviction() {
    let dir = tempfile::tempdir().expect("tempdir");
    let storage = FingerprintStorage::disk(100, dir.path()).expect("disk new");

    for value in 1u64..=80 {
        assert_eq!(storage.insert_checked(fp(value)), InsertOutcome::Inserted);
    }
    assert!(
        storage.stats().eviction_count >= 1,
        "test must trigger disk eviction through FingerprintStorage"
    );

    FingerprintSet::begin_checkpoint(&storage).expect("storage begin checkpoint");
    let fps = FingerprintSet::collect_fingerprints(&storage).expect("disk collect");
    let collected = collected_u64s(&fps);

    assert_checkpoint_collect_contains_full_range(&collected, "storage dispatch collect");
}

// ========== Default trait implementation returns error ==========

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_collect_fingerprints_default_returns_error() {
    // DashSet adapter uses the default (unimplemented) collect_fingerprints
    let set = dashmap::DashSet::<Fingerprint>::new();
    let result = FingerprintSet::collect_fingerprints(&set);
    assert!(result.is_err());
}
