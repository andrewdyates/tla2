// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::fp;
use super::*;
use rustc_hash::FxHashSet;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_collect_all() {
    // Test the collect_all method used during eviction
    let set = MmapFingerprintSet::new(100, None).unwrap();

    // Empty set should return empty
    assert!(set.collect_all().is_empty());

    // Insert some fingerprints
    let entries: Vec<u64> = vec![1, 42, 100, 12345];
    for &v in &entries {
        set.insert(fp(v)).unwrap();
    }

    // Collect and verify all are present
    let collected: FxHashSet<u64> = set.collect_all().into_iter().collect();
    assert_eq!(collected.len(), entries.len());
    for &v in &entries {
        assert!(collected.contains(&v), "Missing fingerprint {}", v);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_collect_all_with_fp_zero() {
    // Test that fingerprint 0 is correctly collected
    let set = MmapFingerprintSet::new(100, None).unwrap();

    set.insert(fp(0)).unwrap(); // Fingerprint zero (stored via has_zero flag)
    set.insert(fp(1)).unwrap();
    set.insert(fp(42)).unwrap();

    let collected: FxHashSet<u64> = set.collect_all().into_iter().collect();
    assert_eq!(collected.len(), 3);
    assert!(collected.contains(&0), "Missing fingerprint 0");
    assert!(collected.contains(&1), "Missing fingerprint 1");
    assert!(collected.contains(&42), "Missing fingerprint 42");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_clear() {
    let set = MmapFingerprintSet::new(100, None).unwrap();

    // Insert some entries including fp(0) which uses the has_zero flag path
    assert!(set.insert(fp(0)).expect("invariant: insert fp(0)"));
    for i in 1..=50 {
        set.insert(fp(i)).expect("invariant: insert fp");
    }
    assert_eq!(set.len(), 51);
    assert!(set.contains(fp(0)));

    // Clear the set
    set.clear();

    // Verify it's empty — including fp(0) via has_zero flag
    assert_eq!(set.len(), 0);
    assert!(set.collect_all().is_empty());
    assert!(
        !set.contains(fp(0)),
        "fp(0) should not be present after clear (has_zero flag must be reset)"
    );

    // Verify previous entries are no longer found
    for i in 1..=50 {
        assert!(
            !set.contains(fp(i)),
            "Fingerprint {} should not be present after clear",
            i
        );
    }

    // Verify we can re-insert fp(0) after clear
    assert!(
        set.insert(fp(0)).expect("invariant: re-insert fp(0)"),
        "fp(0) re-insert after clear should return true (new entry)"
    );
    set.insert(fp(1)).expect("invariant: re-insert fp(1)");
    assert_eq!(set.len(), 2);
    assert!(set.contains(fp(0)));
    assert!(set.contains(fp(1)));
}

/// Verify that `mark_all_flushed` marks entries as flushed and that
/// `contains()` still returns true for flushed entries.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_flushed_entries_found_by_contains() {
    let set = MmapFingerprintSet::new(1000, None).unwrap();

    // Insert some entries
    for i in 1..=50 {
        assert!(set.insert(fp(i)).unwrap());
    }
    assert_eq!(set.len(), 50);

    // Mark all as flushed
    set.mark_all_flushed();

    // Count should be reset to 0 (only unflushed entries count toward load factor)
    assert_eq!(set.len(), 0);

    // But contains() must still return true for flushed entries
    for i in 1..=50 {
        assert!(
            set.contains(fp(i)),
            "Flushed fingerprint {} not found by contains()",
            i
        );
    }

    // Non-existent entries should still return false
    assert!(!set.contains(fp(999)));
}

/// Verify that `collect_all()` skips flushed entries — only unflushed
/// entries should be collected for eviction to disk.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_collect_all_skips_flushed_entries() {
    let set = MmapFingerprintSet::new(1000, None).unwrap();

    // Insert entries
    for i in 1..=30 {
        assert!(set.insert(fp(i)).unwrap());
    }
    assert_eq!(set.collect_all().len(), 30);

    // Mark all as flushed
    set.mark_all_flushed();

    // collect_all should return empty — all entries are flushed (on disk)
    let collected = set.collect_all();
    assert!(
        collected.is_empty(),
        "collect_all() should skip flushed entries, got {} entries",
        collected.len()
    );

    // Now insert new (unflushed) entries
    for i in 100..=110 {
        assert!(set.insert(fp(i)).unwrap());
    }

    // collect_all should only return the new unflushed entries
    let collected = set.collect_all();
    assert_eq!(
        collected.len(),
        11,
        "collect_all() should return only 11 unflushed entries, got {}",
        collected.len()
    );

    // Verify all collected entries are from the new batch
    for &val in &collected {
        assert!(
            (100..=110).contains(&val),
            "Collected entry {} should be in range 100..=110 (unflushed)",
            val
        );
    }
}

/// Verify that new inserts overwrite flushed slots, and that non-overwritten
/// flushed entries remain discoverable via contains().
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_insert_overwrites_flushed_slots() {
    // Use a small capacity to force probe sequences to overlap with flushed slots.
    let set = MmapFingerprintSet::new(100, None).unwrap();

    // Fill to 40% with entries.
    for i in 1..=40 {
        assert!(set.insert(fp(i)).unwrap());
    }
    assert_eq!(set.len(), 40);

    // Mark all as flushed.
    set.mark_all_flushed();
    assert_eq!(set.len(), 0);

    // Insert new entries — these should overwrite flushed slots.
    for i in 1000..=1040 {
        assert!(
            set.insert(fp(i)).unwrap(),
            "Insert of fp({}) should succeed by overwriting flushed slot",
            i
        );
    }
    assert_eq!(set.len(), 41);

    // All new entries must be found.
    for i in 1000..=1040 {
        assert!(set.contains(fp(i)), "new entry fp({}) must be found", i);
    }

    // Count how many original flushed entries survive (their slots were not
    // overwritten by new entries). With 40 originals and 41 new entries in a
    // 100-slot table, hash distribution means some originals will be
    // overwritten and some will survive.
    let surviving = (1..=40).filter(|&i| set.contains(fp(i))).count();
    let overwritten = 40 - surviving;

    // At least some flushed entries must have been overwritten (proving the
    // overwrite mechanism works). With 41 new entries landing in 100 slots
    // that had 40 flushed entries, collisions are inevitable.
    assert!(
        overwritten > 0,
        "expected some flushed slots to be overwritten, but all {} survived",
        surviving
    );

    // At least some flushed entries should survive in non-overwritten slots.
    assert!(
        surviving > 0,
        "expected some flushed entries to survive, but all 40 were overwritten"
    );
}

/// Verify that re-inserting an already-flushed fingerprint returns false
/// (already present), maintaining correctness of the duplicate check.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_reinsert_flushed_entry_returns_already_present() {
    let set = MmapFingerprintSet::new(1000, None).unwrap();

    // Insert entries
    for i in 1..=20 {
        assert!(set.insert(fp(i)).unwrap());
    }

    // Mark all as flushed
    set.mark_all_flushed();
    assert_eq!(set.len(), 0);

    // Re-inserting flushed entries should return false (already present)
    // because the flushed variant of the same fingerprint is recognized
    for i in 1..=20 {
        assert!(
            !set.insert(fp(i)).unwrap(),
            "Re-insert of flushed fp({}) should return false (already present)",
            i
        );
    }

    // Count should remain 0 — no new entries were added
    assert_eq!(set.len(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_reinsert_flushed_entry_after_different_flushed_collision_is_already_present() {
    let set = MmapFingerprintSet::new(8, None).unwrap();

    // With the table's odd hash multiplier, fp(1) and fp(9) share the same
    // probe chain in an 8-slot table. fp(1) lands before fp(9).
    assert!(set.insert(fp(1)).unwrap());
    assert!(set.insert(fp(9)).unwrap());
    assert_eq!(set.len(), 2);

    set.mark_all_flushed();
    assert_eq!(set.len(), 0);

    assert!(
        !set.insert(fp(9)).unwrap(),
        "reinsert must keep probing past a different flushed slot and find the duplicate"
    );
    assert_eq!(
        set.len(),
        0,
        "already-present flushed duplicate must not become a new resident entry"
    );
}

/// Verify that after DiskFingerprintSet eviction, looking up previously-evicted
/// fingerprints does NOT trigger disk lookups because flushed entries in the
/// primary mmap act as a lookup cache.
///
/// This is the key correctness property of #2657: flushed entries prevent
/// O(N*M) unnecessary disk I/O.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_flushed_entries_prevent_disk_lookups() {
    let tmp_dir = tempfile::tempdir().unwrap();
    // 100 capacity, 0.75 load factor → eviction triggers at ~75 entries
    let set = DiskFingerprintSet::new(100, tmp_dir.path()).unwrap();

    // Phase 1: Insert entries until eviction occurs
    for i in 1..=80u64 {
        set.insert_checked(fp(i));
    }
    assert!(
        set.eviction_count() >= 1,
        "Expected at least 1 eviction after inserting 80 entries"
    );

    // Record disk stats after eviction
    let (lookups_before, _) = set.disk_stats();

    // Phase 2: Look up the entries that were in primary BEFORE eviction.
    // These should be flushed entries in the primary mmap. Looking them up
    // should NOT trigger disk lookups because primary.contains() returns true
    // for flushed entries.
    //
    // We look up entries 1..=50 which were likely in the first batch that
    // was evicted to disk and marked as flushed in primary.
    for i in 1..=50u64 {
        let outcome = set.contains_checked(fp(i));
        assert!(
            matches!(outcome, LookupOutcome::Present),
            "Evicted fp({}) should be found, got {:?}",
            i,
            outcome
        );
    }

    // Verify: disk lookups should NOT have increased (or increased minimally)
    // for entries that are still in the flushed primary cache.
    let (lookups_after, _) = set.disk_stats();
    let new_disk_lookups = lookups_after - lookups_before;

    // With the flushed-bit approach, entries that were in the primary before
    // eviction remain as flushed entries. Lookups for these hit the primary
    // first and return Present without touching disk.
    //
    // Some disk lookups may occur for entries that weren't in primary at
    // eviction time (they were inserted after the primary filled and went
    // directly to disk via a second eviction). But the count should be
    // significantly less than 50 (the number we looked up).
    assert!(
        new_disk_lookups < 50,
        "Expected flushed primary cache to prevent most disk lookups. \
         Got {} new disk lookups for 50 contains() calls. \
         Without flushed-bit, this would be ~50.",
        new_disk_lookups
    );
}

/// Verify that FPs differing only in bit 63 (FLUSHED_BIT) hash to the same
/// probe chain and are treated as the same encoded fingerprint (#2674).
///
/// Before the fix, `hash_index` used full 64-bit `fp.0`, so FP(X) and
/// FP(X | FLUSHED_BIT) would start probing from different indices despite
/// encoding to the same 63-bit value. This could cause `contains()` to
/// return false for an FP that IS in the set (under its bit-63 twin).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_hash_index_consistent_with_fp_mask() {
    use crate::storage::open_addressing::FLUSHED_BIT;

    let set = MmapFingerprintSet::new(1024, None).unwrap();

    // Pick a non-zero fingerprint and its bit-63 twin.
    let base_fp = fp(42);
    let twin_fp = Fingerprint(base_fp.0 | FLUSHED_BIT);

    // Both should encode identically (lower 63 bits are the same).
    assert_eq!(
        base_fp.0 & !FLUSHED_BIT,
        twin_fp.0 & !FLUSHED_BIT,
        "Base and twin must share lower 63 bits"
    );

    // Insert the base fingerprint.
    assert!(
        set.insert(base_fp).unwrap(),
        "base_fp should be newly inserted"
    );

    // The twin (differing only in bit 63) must be found, because
    // encode_fingerprint masks to FP_MASK and hash_index now does too.
    assert!(
        set.contains(twin_fp),
        "contains(twin_fp) must return true: bit-63 twin should hash to the \
         same probe chain as base_fp (both encode to the same 63-bit value)"
    );

    // Inserting twin should report already-present (not a new entry).
    assert!(
        !set.insert(twin_fp).unwrap(),
        "twin_fp should be reported as already present (same encoded value)"
    );

    // Only one entry should exist.
    assert_eq!(set.len(), 1, "bit-63 twin must not create a second entry");
}
