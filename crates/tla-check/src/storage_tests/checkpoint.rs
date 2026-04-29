// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::fp;
use super::*;

// ============================================================================
// Checkpoint lifecycle tests (Part of #2656)
// ============================================================================

/// Verify that the in-memory checkpoint lifecycle preserves all data.
/// InMemory checkpoint methods are no-ops, so the key invariant is that
/// calling begin/commit/recover does not corrupt or lose inserted entries.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_lifecycle_in_memory_preserves_data() {
    let storage = FingerprintStorage::in_memory();

    // Insert entries before checkpoint.
    for i in 1..=20 {
        storage.insert_checked(fp(i));
    }
    assert_eq!(storage.len(), 20);

    // Run full checkpoint lifecycle through dyn FingerprintSet trait.
    let fps: &dyn FingerprintSet = &storage;
    fps.begin_checkpoint().expect("in-memory begin_checkpoint");
    fps.commit_checkpoint()
        .expect("in-memory commit_checkpoint");
    fps.recover_checkpoint()
        .expect("in-memory recover_checkpoint");

    // All entries must survive the checkpoint cycle.
    assert_eq!(storage.len(), 20, "len must be unchanged after checkpoint");
    for i in 1..=20 {
        assert_eq!(
            storage.contains_checked(fp(i)),
            LookupOutcome::Present,
            "fp({}) lost after in-memory checkpoint cycle",
            i
        );
    }

    // New inserts must still work after checkpoint.
    storage.insert_checked(fp(100));
    assert_eq!(storage.contains_checked(fp(100)), LookupOutcome::Present);
    assert_eq!(storage.len(), 21);
}

/// Verify that mmap begin_checkpoint actually flushes data to the backing file.
/// Uses a file-backed mmap so we can read raw bytes from disk after flush.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_lifecycle_mmap_flushes_to_disk() {
    let tmp_dir = tempfile::tempdir().unwrap();
    let capacity = 1000;
    let set = MmapFingerprintSet::new(capacity, Some(tmp_dir.path().to_path_buf())).unwrap();

    // Insert entries.
    for i in 1..=10 {
        assert!(set.insert(fp(i)).unwrap());
    }
    assert_eq!(set.len(), 10);

    // Call begin_checkpoint via trait (the path used during liveness checkpointing).
    let fps: &dyn FingerprintSet = &set;
    fps.begin_checkpoint()
        .expect("mmap begin_checkpoint (flush) should succeed");

    // Verify the backing file has non-zero bytes — the flush wrote data.
    // The backing file is in tmp_dir; find it.
    let entries: Vec<_> = std::fs::read_dir(tmp_dir.path())
        .unwrap()
        .filter_map(std::result::Result::ok)
        .collect();
    assert_eq!(entries.len(), 1, "should have exactly one backing file");
    let file_bytes = std::fs::read(entries[0].path()).unwrap();

    // File size should be capacity * 8 bytes.
    assert_eq!(
        file_bytes.len(),
        capacity * 8,
        "backing file should be capacity * 8 bytes"
    );

    // Decode on-disk slots to verify the EXACT fingerprints were flushed.
    // Each slot is a native-endian u64. Non-zero slots contain encoded FPs
    // (lower 63 bits = fingerprint value, bit 63 = flushed flag).
    use crate::storage::open_addressing::{decode_fingerprint, EMPTY};
    let mut on_disk_fps: std::collections::HashSet<u64> = std::collections::HashSet::new();
    for chunk in file_bytes.chunks_exact(8) {
        let slot = u64::from_ne_bytes(chunk.try_into().unwrap());
        if slot != EMPTY {
            on_disk_fps.insert(decode_fingerprint(slot));
        }
    }

    // Every inserted fingerprint must be present in the decoded on-disk data.
    for i in 1..=10u64 {
        assert!(
            on_disk_fps.contains(&i),
            "fp({}) not found in on-disk slots after flush — durability failure",
            i
        );
    }
    assert!(
        on_disk_fps.len() >= 10,
        "expected at least 10 distinct FPs on disk, got {}",
        on_disk_fps.len()
    );

    // Data remains accessible via API after full checkpoint lifecycle.
    fps.commit_checkpoint()
        .expect("commit_checkpoint should succeed");
    fps.recover_checkpoint()
        .expect("recover_checkpoint should succeed");
    for i in 1..=10 {
        assert!(
            set.contains(fp(i)),
            "fp({}) must be accessible after checkpoint lifecycle",
            i
        );
    }
}

/// Verify that checkpoint methods delegate through FingerprintStorage::Disk
/// to DiskFingerprintSet (where begin_checkpoint flushes the primary mmap).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_checkpoint_lifecycle_disk_delegates_through_enum() {
    let tmp_dir = tempfile::tempdir().unwrap();
    let storage = FingerprintStorage::disk(100, tmp_dir.path()).unwrap();

    storage.insert_checked(fp(100));
    storage.insert_checked(fp(200));
    assert_eq!(storage.len(), 2);

    let fps: &dyn FingerprintSet = &storage;
    assert!(
        fps.begin_checkpoint().is_ok(),
        "disk begin_checkpoint should flush primary"
    );
    assert!(fps.commit_checkpoint().is_ok());
    assert!(fps.recover_checkpoint().is_ok());

    assert_eq!(storage.contains_checked(fp(100)), LookupOutcome::Present);
    assert_eq!(storage.contains_checked(fp(200)), LookupOutcome::Present);
}
