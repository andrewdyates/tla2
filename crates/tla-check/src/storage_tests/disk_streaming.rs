// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::fp;
use super::*;

/// Regression test for #1784/#1777: streaming merge correctness.
///
/// Verifies that multiple eviction cycles produce correct merged disk state
/// without loading the entire disk file into memory. Tests:
/// 1. Two evictions produce correct union of all fingerprints
/// 2. Overlapping (duplicate) fingerprints between primary and disk are deduped
/// 3. All fingerprints are retrievable after multi-eviction merge
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_streaming_merge_correctness() {
    let tmp_dir = tempfile::tempdir().unwrap();
    // Small primary: eviction triggers at ~75 entries (100 * 0.75 load factor)
    let set = DiskFingerprintSet::new(100, tmp_dir.path()).unwrap();

    // Phase 1: Insert 100 unique fingerprints to trigger first eviction
    for i in 1..=100u64 {
        set.insert_checked(fp(i));
    }
    assert!(
        set.eviction_count() >= 1,
        "Expected eviction after 100 inserts into 100-slot primary"
    );
    let evictions_after_phase1 = set.eviction_count();

    // Phase 2: Insert 100 more, including 20 duplicates from phase 1.
    // This exercises the streaming merge dedup path.
    for i in 81..=180u64 {
        set.insert_checked(fp(i));
    }
    assert!(
        set.eviction_count() > evictions_after_phase1,
        "Expected additional eviction in phase 2"
    );

    // Verify ALL unique fingerprints are retrievable (1..=180 = 180 unique)
    let mut missing = Vec::new();
    for i in 1..=180u64 {
        if set.contains_checked(fp(i)) != LookupOutcome::Present {
            missing.push(i);
        }
    }
    assert!(
        missing.is_empty(),
        "Missing {} fingerprints after streaming merge: {:?}",
        missing.len(),
        &missing[..missing.len().min(20)]
    );

    // Verify total count matches unique count (duplicates deduped)
    // Note: len() returns total_count which includes primary + disk.
    // The 20 duplicates (81..=100) should NOT be double-counted.
    assert_eq!(
        set.len(),
        180,
        "Total count should be 180 unique fingerprints, not more"
    );

    // Verify negative lookups still work
    assert_eq!(
        set.contains_checked(fp(0)),
        LookupOutcome::Absent,
        "fp(0) was never inserted"
    );
    assert_eq!(
        set.contains_checked(fp(181)),
        LookupOutcome::Absent,
        "fp(181) was never inserted"
    );
}

/// Regression test for #1784: streaming merge preserves page index correctness.
///
/// Forces enough entries to span multiple disk pages (FPS_PER_PAGE = 1024),
/// then verifies all entries are findable via disk_lookup which depends on
/// the page index being correct.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_disk_fpset_streaming_merge_multi_page() {
    let tmp_dir = tempfile::tempdir().unwrap();
    // Small primary to force many evictions
    let set = DiskFingerprintSet::new(500, tmp_dir.path()).unwrap();

    // Insert 3000 entries to fill >2 disk pages (FPS_PER_PAGE = 1024)
    for i in 1..=3000u64 {
        set.insert_checked(fp(i));
    }

    assert!(
        set.eviction_count() >= 2,
        "Expected at least 2 evictions for 3000 entries in 500-slot primary, got {}",
        set.eviction_count()
    );
    assert!(
        set.disk_count() > 1024,
        "Expected >1 page of disk entries, got {}",
        set.disk_count()
    );

    // Verify all entries are findable (tests page index correctness)
    let mut missing = Vec::new();
    for i in 1..=3000u64 {
        if set.contains_checked(fp(i)) != LookupOutcome::Present {
            missing.push(i);
        }
    }
    assert!(
        missing.is_empty(),
        "Missing {} fingerprints after multi-page merge: first 10 = {:?}",
        missing.len(),
        &missing[..missing.len().min(10)]
    );
}

/// Regression test for #1777: clean EOF at entry boundary returns None.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_read_next_fp_clean_eof_returns_none() {
    let mut reader = std::io::Cursor::new(Vec::<u8>::new());

    let fp = read_next_fp(&mut reader).expect("clean EOF should not error");
    assert!(
        fp.is_none(),
        "clean EOF at fingerprint boundary should return None"
    );
}

/// Regression test for #1777: truncated trailing bytes are a hard error.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_read_next_fp_partial_entry_returns_unexpected_eof() {
    let mut reader = std::io::Cursor::new(vec![1u8, 2, 3, 4, 5]);

    let err = read_next_fp(&mut reader).expect_err("truncated entry must error");
    assert_eq!(
        err.kind(),
        std::io::ErrorKind::UnexpectedEof,
        "partial fingerprint entry should be surfaced as UnexpectedEof"
    );
    assert!(
        err.to_string().contains("truncated fingerprint entry"),
        "error should identify truncated fingerprint entry"
    );
}

/// Regression test for #1777: non-EOF read errors must propagate.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_read_next_fp_propagates_non_eof_error() {
    struct FailingReader;

    impl std::io::Read for FailingReader {
        fn read(&mut self, _buf: &mut [u8]) -> std::io::Result<usize> {
            Err(std::io::Error::other("simulated read failure"))
        }
    }

    let mut reader = FailingReader;
    let err = read_next_fp(&mut reader).expect_err("non-EOF read error must propagate");
    assert_eq!(
        err.kind(),
        std::io::ErrorKind::Other,
        "read_next_fp should not coerce non-EOF errors to EOF"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_trait_stats_include_disk_counters() {
    let tmp_dir = tempfile::tempdir().expect("tempdir should initialize");
    let set: Box<dyn FingerprintSet> =
        Box::new(DiskFingerprintSet::new(100, tmp_dir.path()).expect("disk set should initialize"));

    for i in 1..=150 {
        assert_eq!(set.insert_checked(fp(i)), InsertOutcome::Inserted);
    }
    assert_eq!(set.contains_checked(fp(50)), LookupOutcome::Present);

    let stats = FingerprintSet::stats(&*set);
    assert!(
        stats.disk_count > 0,
        "trait stats should expose disk residency"
    );
    assert!(
        stats.disk_lookups > 0,
        "trait stats should expose disk lookups"
    );
    assert!(stats.disk_hits > 0, "trait stats should expose disk hits");
    assert!(
        stats.eviction_count > 0,
        "trait stats should expose eviction count"
    );
    assert_eq!(
        stats.memory_count + stats.disk_count,
        set.len(),
        "resident + disk counts should match total fingerprint count"
    );
    assert_eq!(stats.memory_bytes, 100 * std::mem::size_of::<u64>());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_storage_disk_stats_delegate_through_dispatch_enum() {
    let tmp_dir = tempfile::tempdir().expect("tempdir should initialize");
    let storage =
        FingerprintStorage::disk(100, tmp_dir.path()).expect("disk storage should initialize");

    for i in 1..=150 {
        assert_eq!(storage.insert_checked(fp(i)), InsertOutcome::Inserted);
    }
    assert_eq!(storage.contains_checked(fp(50)), LookupOutcome::Present);

    let stats = storage.stats();
    assert!(
        stats.disk_count > 0,
        "dispatch enum should surface disk stats"
    );
    assert!(
        stats.disk_lookups > 0,
        "dispatch enum should surface lookups"
    );
    assert!(stats.disk_hits > 0, "dispatch enum should surface hits");
    assert!(
        stats.eviction_count > 0,
        "dispatch enum should surface evictions"
    );
    assert_eq!(stats.memory_count + stats.disk_count, storage.len());
}
