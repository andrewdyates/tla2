// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::storage::cas_fpset::PartitionedCasFingerprintSet;
use tla_mc_core::FingerprintSet as McFingerprintSet;

use super::fp;
use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_recreate_empty_preserves_huge_page_request() {
    let set = MmapFingerprintSet::new_with_huge_pages(128, None).expect("mmap should initialize");
    assert!(set.huge_pages_requested());

    let fresh = set
        .recreate_empty()
        .expect("recreate_empty should preserve mmap config");

    assert!(fresh.huge_pages_requested());
    assert_eq!(fresh.len(), 0);
    assert!(fresh.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_recreate_empty_preserves_load_factor() {
    let set = MmapFingerprintSet::with_load_factor(100, None, 0.5).expect("mmap should initialize");
    let fresh = set
        .recreate_empty()
        .expect("recreate_empty should preserve load factor");

    for i in 1..=50 {
        assert!(
            fresh
                .insert(fp(i))
                .expect("insert under preserved threshold"),
            "insert {i} should be new"
        );
    }

    match fresh.insert(fp(1000)) {
        Err(MmapError::TableFull { count, capacity }) => {
            assert_eq!(count, 50);
            assert_eq!(capacity, 100);
        }
        other => panic!("expected preserved load-factor limit, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_storage_fresh_empty_clone_in_memory_resets_contents() {
    let storage = FingerprintStorage::in_memory();
    assert_eq!(storage.insert_checked(fp(1)), InsertOutcome::Inserted);
    assert_eq!(storage.insert_checked(fp(2)), InsertOutcome::Inserted);

    let fresh = FingerprintSet::fresh_empty_clone(&storage).expect("clone should succeed");

    assert_eq!(fresh.len(), 0);
    assert_eq!(fresh.contains_checked(fp(1)), LookupOutcome::Absent);
    assert_eq!(fresh.insert_checked(fp(1)), InsertOutcome::Inserted);
    assert_eq!(storage.contains_checked(fp(1)), LookupOutcome::Present);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_storage_fresh_empty_clone_mmap_resets_contents() {
    let storage = FingerprintStorage::mmap(128, None).expect("mmap storage should initialize");
    assert_eq!(storage.insert_checked(fp(11)), InsertOutcome::Inserted);
    assert_eq!(storage.insert_checked(fp(22)), InsertOutcome::Inserted);

    let fresh = FingerprintSet::fresh_empty_clone(&storage).expect("clone should succeed");

    assert_eq!(fresh.len(), 0);
    assert_eq!(fresh.contains_checked(fp(11)), LookupOutcome::Absent);
    assert_eq!(fresh.insert_checked(fp(11)), InsertOutcome::Inserted);
    assert_eq!(storage.contains_checked(fp(11)), LookupOutcome::Present);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_storage_fresh_empty_clone_disk_is_logically_empty() {
    let dir = tempfile::tempdir().expect("tempdir");
    let storage = FingerprintStorage::disk(8, dir.path()).expect("disk storage should initialize");
    for i in 1..=32 {
        assert!(matches!(
            storage.insert_checked(fp(i)),
            InsertOutcome::Inserted | InsertOutcome::AlreadyPresent
        ));
    }
    assert_eq!(storage.contains_checked(fp(1)), LookupOutcome::Present);

    let fresh = FingerprintSet::fresh_empty_clone(&storage).expect("clone should succeed");

    assert_eq!(fresh.len(), 0);
    assert_eq!(fresh.contains_checked(fp(1)), LookupOutcome::Absent);
    assert_eq!(fresh.insert_checked(fp(1001)), InsertOutcome::Inserted);
    assert_eq!(storage.contains_checked(fp(1)), LookupOutcome::Present);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_storage_fresh_empty_clone_disk_isolated_after_clone_eviction() {
    let dir = tempfile::tempdir().expect("tempdir");
    let storage = FingerprintStorage::disk(8, dir.path()).expect("disk storage should initialize");
    for i in 1..=32 {
        assert!(matches!(
            storage.insert_checked(fp(i)),
            InsertOutcome::Inserted | InsertOutcome::AlreadyPresent
        ));
    }

    let fresh = FingerprintSet::fresh_empty_clone(&storage).expect("clone should succeed");
    for i in 1001..=1032 {
        assert!(matches!(
            fresh.insert_checked(fp(i)),
            InsertOutcome::Inserted | InsertOutcome::AlreadyPresent
        ));
    }

    let original_fps = FingerprintSet::collect_fingerprints(&storage).expect("collect original");
    assert!(
        original_fps.contains(&fp(1)),
        "clone eviction must not delete evicted fingerprints from the original disk storage"
    );
    assert!(
        !original_fps.contains(&fp(1001)),
        "clone eviction must not leak clone fingerprints into the original disk storage"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_partitioned_cas_fresh_empty_clone_resets_contents() {
    let storage = PartitionedCasFingerprintSet::new(2, 4096);
    assert_eq!(
        McFingerprintSet::insert_checked(&storage, fp(7)),
        InsertOutcome::Inserted
    );
    assert_eq!(
        McFingerprintSet::insert_checked(&storage, fp(8)),
        InsertOutcome::Inserted
    );

    let fresh = FingerprintSet::fresh_empty_clone(&storage).expect("clone should succeed");

    assert_eq!(fresh.len(), 0);
    assert_eq!(fresh.contains_checked(fp(7)), LookupOutcome::Absent);
    assert_eq!(fresh.insert_checked(fp(7)), InsertOutcome::Inserted);
    assert_eq!(
        McFingerprintSet::contains_checked(&storage, fp(7)),
        LookupOutcome::Present
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sharded_in_memory_fresh_empty_clone_resets_contents() {
    let storage = ShardedFingerprintSet::new_with_capacity(2, 1024);
    assert_eq!(storage.insert_checked(fp(21)), InsertOutcome::Inserted);
    assert_eq!(storage.insert_checked(fp(22)), InsertOutcome::Inserted);

    let fresh = FingerprintSet::fresh_empty_clone(&storage).expect("clone should succeed");

    assert_eq!(fresh.len(), 0);
    assert_eq!(fresh.contains_checked(fp(21)), LookupOutcome::Absent);
    assert_eq!(fresh.insert_checked(fp(21)), InsertOutcome::Inserted);
    assert_eq!(storage.contains_checked(fp(21)), LookupOutcome::Present);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sharded_disk_fresh_empty_clone_resets_contents() {
    let dir = tempfile::tempdir().expect("tempdir");
    let storage =
        ShardedFingerprintSet::new_disk(1, 16, dir.path()).expect("disk shards should initialize");
    for i in 1..=32 {
        assert!(matches!(
            storage.insert_checked(fp(i)),
            InsertOutcome::Inserted | InsertOutcome::AlreadyPresent
        ));
    }

    let fresh = FingerprintSet::fresh_empty_clone(&storage).expect("clone should succeed");

    assert_eq!(fresh.len(), 0);
    assert_eq!(fresh.contains_checked(fp(1)), LookupOutcome::Absent);
    assert_eq!(fresh.insert_checked(fp(1001)), InsertOutcome::Inserted);
    assert_eq!(storage.contains_checked(fp(1)), LookupOutcome::Present);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sharded_disk_fresh_empty_clone_isolated_after_clone_eviction() {
    let dir = tempfile::tempdir().expect("tempdir");
    let storage =
        ShardedFingerprintSet::new_disk(1, 16, dir.path()).expect("disk shards should initialize");
    for i in 1..=64 {
        assert!(matches!(
            storage.insert_checked(fp(i)),
            InsertOutcome::Inserted | InsertOutcome::AlreadyPresent
        ));
    }

    let fresh = FingerprintSet::fresh_empty_clone(&storage).expect("clone should succeed");
    for i in 1001..=1064 {
        assert!(matches!(
            fresh.insert_checked(fp(i)),
            InsertOutcome::Inserted | InsertOutcome::AlreadyPresent
        ));
    }

    let original_fps = FingerprintSet::collect_fingerprints(&storage).expect("collect original");
    assert!(
        original_fps.contains(&fp(1)),
        "clone eviction must not delete evicted fingerprints from the original shard"
    );
    assert!(
        !original_fps.contains(&fp(1001)),
        "clone eviction must not overwrite the original shard's disk file"
    );
}
