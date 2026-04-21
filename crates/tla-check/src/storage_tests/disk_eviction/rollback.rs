// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test for fail_next_publish fault injection: metadata rollback on publish failure.
///
/// Unlike the read-only directory tests which fail at file *creation*, this tests
/// failure at the publish step — after the merge file has been written and metadata
/// staged, but before the atomic rename. The EvictMetadataRollbackGuard must restore
/// the previous page_index and disk_count.
///
/// Calls evict() directly to prevent insert_checked retry loops from masking the
/// rollback behavior.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_publish_failure_metadata_rollback() {
    use std::sync::atomic::Ordering;

    let tmp_dir = tempfile::tempdir().unwrap();
    let set = DiskFingerprintSet::new(100, tmp_dir.path()).unwrap();

    // Phase 1: Insert enough entries to trigger first successful eviction (>75).
    for i in 1..=80u64 {
        set.insert_checked(fp(i));
    }
    assert!(set.eviction_count() >= 1, "first eviction should occur");

    // Snapshot metadata after successful first eviction.
    let disk_count_after_first = set.disk_count();
    assert!(disk_count_after_first > 0, "disk should have entries");

    // Verify all first-eviction fingerprints are findable.
    for i in 1..=80u64 {
        assert_eq!(
            set.contains_checked(fp(i)),
            LookupOutcome::Present,
            "fp({}) should be present after first eviction",
            i
        );
    }

    // Phase 2: Insert more entries (unflushed) without triggering another eviction.
    // After first eviction, primary count is reset via mark_all_flushed().
    // Insert a moderate batch that stays below the eviction threshold.
    for i in 81..=120u64 {
        set.insert_checked(fp(i));
    }

    // Phase 3: Inject publish failure, then call evict() directly.
    set.fail_next_publish.store(true, Ordering::SeqCst);
    let result = set.evict();
    assert!(
        result.is_err(),
        "eviction should fail from injected publish failure"
    );

    // The fault injection should have been consumed (swapped to false).
    assert!(
        !set.fail_next_publish.load(Ordering::SeqCst),
        "fail_next_publish should be consumed by the eviction attempt"
    );

    // Verify metadata was rolled back after failed publish.
    assert_eq!(
        set.disk_count(),
        disk_count_after_first,
        "disk_count must not change after publish failure (rollback)"
    );

    // Verify fingerprints from the first eviction are still findable on disk.
    for i in 1..=80u64 {
        assert_eq!(
            set.contains_checked(fp(i)),
            LookupOutcome::Present,
            "fp({}) must still be discoverable after failed publish",
            i
        );
    }

    // Phase 4: Verify the set recovers — a subsequent eviction should succeed.
    let eviction_count_before_recovery = set.eviction_count();
    let result = set.evict();
    assert!(
        result.is_ok(),
        "eviction should succeed after publish failure recovery: {:?}",
        result.err()
    );
    assert!(
        set.eviction_count() > eviction_count_before_recovery,
        "successful recovery eviction should increment eviction count"
    );

    // All fingerprints (both disk and primary) should be findable after recovery.
    for i in 1..=120u64 {
        assert_eq!(
            set.contains_checked(fp(i)),
            LookupOutcome::Present,
            "fp({}) must be findable after recovery eviction",
            i
        );
    }
}

/// Regression test for #2307: eviction metadata rollback on rename failure.
///
/// After a successful first eviction, makes the disk directory read-only so the
/// second eviction's tmp file creation or rename fails. Verifies that:
/// 1. page_index and disk_count remain consistent with the old disk file
/// 2. All fingerprints from the first eviction are still discoverable on disk
/// 3. The system does not silently lose fingerprints
#[cfg(unix)]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_eviction_metadata_rollback_on_rename_failure() {
    use std::os::unix::fs::PermissionsExt;

    let tmp_dir = tempfile::tempdir().unwrap();
    let set = DiskFingerprintSet::new(100, tmp_dir.path()).unwrap();

    // Phase 1: Insert enough entries to trigger first eviction (>75 entries).
    for i in 1..=80u64 {
        set.insert_checked(fp(i));
    }
    assert!(set.eviction_count() >= 1, "first eviction should occur");

    // Snapshot metadata after successful first eviction.
    let disk_count_after_first = set.disk_count();
    assert!(disk_count_after_first > 0, "disk should have entries");

    // Verify all first-eviction fingerprints are findable.
    for i in 1..=80u64 {
        assert_eq!(
            set.contains_checked(fp(i)),
            LookupOutcome::Present,
            "fp({}) should be present after first eviction",
            i
        );
    }

    // Phase 2: Make disk directory read-only to force eviction failure.
    std::fs::set_permissions(tmp_dir.path(), std::fs::Permissions::from_mode(0o444)).unwrap();

    // Insert more entries to trigger second eviction attempt (which will fail).
    for i in 81..=160u64 {
        set.insert_checked(fp(i));
    }

    // Restore permissions for cleanup and further assertions.
    std::fs::set_permissions(tmp_dir.path(), std::fs::Permissions::from_mode(0o755)).unwrap();

    // Verify metadata was NOT corrupted by the failed eviction.
    // disk_count should still reflect the first (successful) eviction.
    assert_eq!(
        set.disk_count(),
        disk_count_after_first,
        "disk_count must not change after failed eviction (rollback)"
    );

    // Verify fingerprints from the first eviction are still findable on disk.
    // This exercises the page_index consistency — if page_index was corrupted
    // by the failed eviction, disk lookups would return wrong results.
    for i in 1..=80u64 {
        assert_eq!(
            set.contains_checked(fp(i)),
            LookupOutcome::Present,
            "fp({}) must still be discoverable after failed second eviction",
            i
        );
    }
}
