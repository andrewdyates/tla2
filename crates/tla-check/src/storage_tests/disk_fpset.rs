// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::fp;
use super::*;

// ========== DiskFingerprintSet tests ==========

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_basic_operations() {
    let tmp_dir = tempfile::tempdir().unwrap();
    let set = DiskFingerprintSet::new(1000, tmp_dir.path()).unwrap();

    // Initially empty
    assert!(set.is_empty());
    assert_eq!(set.len(), 0);

    // Insert new fingerprint
    assert_eq!(set.insert_checked(fp(12345)), InsertOutcome::Inserted);
    assert_eq!(set.len(), 1);
    assert_eq!(set.contains_checked(fp(12345)), LookupOutcome::Present);

    // Insert same fingerprint again
    assert_eq!(set.insert_checked(fp(12345)), InsertOutcome::AlreadyPresent);
    assert_eq!(set.len(), 1);

    // Insert different fingerprint
    assert_eq!(set.insert_checked(fp(67890)), InsertOutcome::Inserted);
    assert_eq!(set.len(), 2);
    assert_eq!(set.contains_checked(fp(67890)), LookupOutcome::Present);

    // Check non-existent
    assert_eq!(set.contains_checked(fp(99999)), LookupOutcome::Absent);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_fingerprint_zero() {
    let tmp_dir = tempfile::tempdir().unwrap();
    let set = DiskFingerprintSet::new(100, tmp_dir.path()).unwrap();

    assert_eq!(set.contains_checked(fp(0)), LookupOutcome::Absent);
    assert_eq!(set.insert_checked(fp(0)), InsertOutcome::Inserted);
    assert_eq!(set.contains_checked(fp(0)), LookupOutcome::Present);
    assert_eq!(set.insert_checked(fp(0)), InsertOutcome::AlreadyPresent);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_many_fingerprints() {
    let tmp_dir = tempfile::tempdir().unwrap();
    let set = DiskFingerprintSet::new(10000, tmp_dir.path()).unwrap();

    // Insert 5000 fingerprints
    for i in 0..5000u64 {
        let v = i.wrapping_mul(0x12345678_9ABCDEF0);
        assert_eq!(
            set.insert_checked(fp(v)),
            InsertOutcome::Inserted,
            "failed to insert fp {}",
            i
        );
    }

    assert_eq!(set.len(), 5000);

    // Verify all present
    for i in 0..5000u64 {
        let v = i.wrapping_mul(0x12345678_9ABCDEF0);
        assert_eq!(
            set.contains_checked(fp(v)),
            LookupOutcome::Present,
            "missing fp {}",
            i
        );
    }

    // Verify non-present
    for i in 5000..5100u64 {
        let v = i.wrapping_mul(0x12345678_9ABCDEF0);
        assert_eq!(
            set.contains_checked(fp(v)),
            LookupOutcome::Absent,
            "unexpected fp {}",
            i
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_trait_impl() {
    let tmp_dir = tempfile::tempdir().unwrap();
    let set: Box<dyn FingerprintSet> =
        Box::new(DiskFingerprintSet::new(1000, tmp_dir.path()).unwrap());

    assert_eq!(set.insert_checked(fp(12345)), InsertOutcome::Inserted);
    assert_eq!(set.contains_checked(fp(12345)), LookupOutcome::Present);
    assert_eq!(set.len(), 1);

    // Disk storage should report Normal capacity (unlimited)
    assert_eq!(set.capacity_status(), CapacityStatus::Normal);
    assert!(!set.has_errors());
    assert_eq!(set.dropped_count(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_statistics() {
    let tmp_dir = tempfile::tempdir().unwrap();
    let set = DiskFingerprintSet::new(100, tmp_dir.path()).unwrap();

    // Insert some fingerprints
    for i in 1..=50 {
        set.insert_checked(fp(i));
    }

    // Check statistics
    assert_eq!(set.len(), 50);
    assert_eq!(set.disk_count(), 0); // Nothing evicted yet
    assert_eq!(set.eviction_count(), 0);

    let (lookups, hits) = set.disk_stats();
    // Disk stats should be 0 since we haven't triggered disk lookup
    assert_eq!(lookups, 0);
    assert_eq!(hits, 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_eviction() {
    let tmp_dir = tempfile::tempdir().unwrap();
    // Use a small primary capacity to trigger eviction quickly
    // Load factor is 0.75, so 100 capacity means eviction at ~75 entries
    let set = DiskFingerprintSet::new(100, tmp_dir.path()).unwrap();

    // Insert enough to trigger eviction (>75 entries)
    let num_entries = 150;
    for i in 1..=num_entries {
        set.insert_checked(fp(i));
    }

    // Verify eviction occurred
    assert!(
        set.eviction_count() >= 1,
        "Expected at least 1 eviction, got {}",
        set.eviction_count()
    );
    assert!(
        set.disk_count() > 0,
        "Expected some entries on disk after eviction"
    );
    assert_eq!(
        set.len(),
        num_entries as usize,
        "Total count should include all entries"
    );

    // Verify all entries can still be found (either in primary or on disk)
    for i in 1..=num_entries {
        assert_eq!(
            set.contains_checked(fp(i)),
            LookupOutcome::Present,
            "Fingerprint {} not found after eviction",
            i
        );
    }

    // Verify disk lookups are happening for evicted entries
    let (lookups, _hits) = set.disk_stats();
    assert!(
        lookups > 0,
        "Expected disk lookups when checking contains after eviction"
    );
}

/// Regression test for #1702: disk lookup I/O failures must not be silent.
///
/// Removes the on-disk fingerprint file after eviction and verifies that
/// `DiskFingerprintSet` surfaces an error via `has_errors()/dropped_count()`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_disk_lookup_io_error_sets_error_flag() {
    let tmp_dir = tempfile::tempdir().unwrap();
    let set = DiskFingerprintSet::new(100, tmp_dir.path()).unwrap();

    for i in 1..=150 {
        set.insert_checked(fp(i));
    }
    assert!(
        set.eviction_count() >= 1,
        "expected eviction to populate disk"
    );
    assert!(set.disk_count() > 0, "expected entries on disk");

    let disk_file = tmp_dir.path().join("fingerprints.fp");
    std::fs::remove_file(&disk_file).expect("failed to remove fingerprints file");
    // Invalidate cached file descriptors in the reader pool.  On Unix,
    // open FDs survive unlink so the pool would still read the deleted
    // file through stale handles.  Advancing the epoch forces reopen,
    // which fails because the file no longer exists.
    set.invalidate_disk_readers_for_test();

    // fp(50) is in the evicted region (fp(1)..fp(100) evicted to disk).
    // Use fp(50) instead of fp(1) because fp(1) is the page boundary entry
    // in the in-memory page index, and disk_lookup short-circuits to true
    // for exact page boundary matches without reading the file.
    let checked = set.contains_checked(fp(50));
    assert!(
        matches!(checked, LookupOutcome::StorageFault(_)),
        "contains_checked should surface disk I/O faults explicitly, got {checked:?}"
    );
    assert_ne!(set.contains_checked(fp(50)), LookupOutcome::Present);
    assert!(
        set.has_errors(),
        "disk lookup I/O error should set error flag"
    );
    assert!(
        set.dropped_count() >= 1,
        "error count should increase after disk lookup failure"
    );

    let trait_obj: &dyn FingerprintSet = &set;
    assert!(
        trait_obj.has_errors(),
        "FingerprintSet trait view should surface disk lookup errors"
    );
    assert!(
        trait_obj.dropped_count() >= 1,
        "FingerprintSet trait view should expose disk lookup error count"
    );
}

/// Regression test for #1779: aligned tail pages must be fully readable.
///
/// Builds a synthetic disk file with one full page plus a single fingerprint
/// tail entry, then verifies `search_disk_page` can find that last entry.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_search_disk_page_reads_aligned_partial_tail() {
    use std::io::Write;

    let tmp_dir = tempfile::tempdir().unwrap();
    let set = DiskFingerprintSet::new(16, tmp_dir.path()).unwrap();
    let disk_file = tmp_dir.path().join("fingerprints.fp");

    let mut writer = std::io::BufWriter::new(std::fs::File::create(&disk_file).unwrap());
    for value in 1..=(FPS_PER_PAGE as u64 + 1) {
        writer.write_all(&value.to_le_bytes()).unwrap();
    }
    writer.flush().unwrap();

    *set.page_index.write() = vec![1, FPS_PER_PAGE as u64 + 1];
    set.disk_count.store(FPS_PER_PAGE + 1, Ordering::Relaxed);
    // search_disk_page reads from the cached disk_file_len atomic,
    // not the filesystem — we must sync after external file creation.
    let file_bytes = (FPS_PER_PAGE + 1) * FINGERPRINT_BYTES;
    set.disk_file_len
        .store(file_bytes as u64, Ordering::Release);

    assert!(
        set.search_disk_page(1, fp(FPS_PER_PAGE as u64 + 1))
            .unwrap(),
        "aligned tail page lookup should find the last fingerprint"
    );
    assert!(
        !set.search_disk_page(1, fp(FPS_PER_PAGE as u64 + 2))
            .unwrap(),
        "aligned tail page lookup should still return false for absent fingerprints"
    );
}

/// Regression test for #1779: truncated disk pages must surface as errors.
///
/// Truncates the on-disk fingerprint file by one byte and verifies lookups
/// record an error instead of silently treating the page as valid data.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_truncated_disk_file_sets_error_flag() {
    let tmp_dir = tempfile::tempdir().unwrap();
    let set = DiskFingerprintSet::new(100, tmp_dir.path()).unwrap();

    for i in 1..=150 {
        set.insert_checked(fp(i));
    }
    assert!(
        set.eviction_count() >= 1,
        "expected eviction to populate disk"
    );
    assert!(set.disk_count() > 0, "expected entries on disk");

    let disk_file = tmp_dir.path().join("fingerprints.fp");
    let original_len = std::fs::metadata(&disk_file).unwrap().len();
    assert!(original_len > 0, "disk file must be non-empty");
    assert_eq!(
        original_len % FINGERPRINT_BYTES as u64,
        0,
        "eviction writes aligned fingerprint files"
    );
    std::fs::OpenOptions::new()
        .write(true)
        .open(&disk_file)
        .unwrap()
        .set_len(original_len - 1)
        .expect("truncate should succeed");

    // fp(50) avoids page-boundary short-circuit in the page index path.
    assert_ne!(set.contains_checked(fp(50)), LookupOutcome::Present);
    assert!(
        set.has_errors(),
        "truncated disk page should set the disk error flag"
    );
    assert!(
        set.dropped_count() >= 1,
        "truncated disk page should increment disk error count"
    );
}

/// Regression test for #1777: eviction merge must reject truncated trailing entries.
///
/// Corrupts an existing disk file by one byte, then forces another eviction so
/// `streaming_merge` reads the corrupted file. The merge must surface an error
/// (insert returns false + error counters), not silently treat the truncation as EOF.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_streaming_merge_truncated_entry_sets_error_flag() {
    let tmp_dir = tempfile::tempdir().unwrap();
    let set = DiskFingerprintSet::new(16, tmp_dir.path()).unwrap();

    // Populate enough entries to ensure we have an on-disk file.
    for i in 1..=40 {
        set.insert_checked(fp(i));
    }
    assert!(
        set.eviction_count() >= 1,
        "expected at least one eviction before corruption"
    );

    let disk_file = tmp_dir.path().join("fingerprints.fp");
    let original_len = std::fs::metadata(&disk_file).unwrap().len();
    assert!(
        original_len > FINGERPRINT_BYTES as u64,
        "disk file should contain at least one full fingerprint entry"
    );
    assert_eq!(
        original_len % FINGERPRINT_BYTES as u64,
        0,
        "eviction writes aligned fingerprint files"
    );
    std::fs::OpenOptions::new()
        .write(true)
        .open(&disk_file)
        .unwrap()
        .set_len(original_len - 1)
        .expect("truncate should succeed");

    // Clear the in-memory page_index so disk_lookup_checked returns Absent
    // instead of StorageFault. Without this, the typed-outcome API (#1841)
    // short-circuits insert_checked on the alignment error before primary
    // fills up, preventing eviction. With an empty index, inserts bypass
    // disk lookup and fill primary normally, triggering eviction which calls
    // streaming_merge() — where read_next_fp() encounters the truncation.
    *set.page_index.write() = Vec::new();

    let evictions_before = set.eviction_count();
    let mut saw_insert_failure = false;
    for i in 41..=200 {
        if set.insert_checked(fp(i)) != InsertOutcome::Inserted {
            saw_insert_failure = true;
            break;
        }
    }

    assert!(
        set.eviction_count() > evictions_before,
        "test must force another eviction to exercise streaming merge"
    );
    assert!(
        saw_insert_failure,
        "truncated disk entry should cause merge failure, not silent EOF"
    );
    assert!(
        set.has_errors(),
        "truncated streaming merge should set the disk error flag"
    );
    assert!(
        set.dropped_count() >= 1,
        "truncated streaming merge should increment disk error count"
    );
}

/// Regression test for #1779: stale page-index entries must surface as errors.
///
/// Simulates a stale in-memory page index after disk shrink and verifies that a
/// lookup into a non-existent page records an error.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_page_index_beyond_file_sets_error_flag() {
    use std::io::Write;

    let tmp_dir = tempfile::tempdir().unwrap();
    let set = DiskFingerprintSet::new(16, tmp_dir.path()).unwrap();
    let disk_file = tmp_dir.path().join("fingerprints.fp");

    let mut writer = std::io::BufWriter::new(std::fs::File::create(&disk_file).unwrap());
    writer.write_all(&1u64.to_le_bytes()).unwrap();
    writer.flush().unwrap();

    // Page 1 does not exist in this 8-byte file.
    *set.page_index.write() = vec![1, 2];
    set.disk_count.store(1, Ordering::Relaxed);

    assert_ne!(
        set.contains_checked(fp(3)),
        LookupOutcome::Present,
        "stale page-index lookup should degrade to false at public API"
    );
    assert!(
        set.has_errors(),
        "stale page-index lookup should record an error"
    );
    assert!(
        set.dropped_count() >= 1,
        "stale page-index lookup should increment error count"
    );
}
