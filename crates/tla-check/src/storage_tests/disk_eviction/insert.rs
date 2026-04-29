// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #1423: concurrent insert/contains during eviction.
///
/// Spawns multiple threads that insert and check fingerprints while eviction
/// is triggered by table-full conditions. Verifies no fingerprints are lost.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_disk_fpset_concurrent_eviction_no_lost_fingerprints() {
    use std::sync::Arc;
    use std::thread;

    let tmp_dir = tempfile::tempdir().unwrap();
    // Small primary (100 slots, load factor 0.75 -> eviction at ~75) to trigger
    // many evictions during concurrent access.
    let set = Arc::new(DiskFingerprintSet::new(100, tmp_dir.path()).unwrap());

    let num_threads = 4;
    let fps_per_thread = 200;

    let handles: Vec<_> = (0..num_threads)
        .map(|t| {
            let set = Arc::clone(&set);
            thread::spawn(move || {
                let base = (t * fps_per_thread) + 1; // avoid fp(0) edge case
                for i in 0..fps_per_thread {
                    let v = (base + i) as u64;
                    set.insert_checked(fp(v));
                }
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }

    // Verify ALL fingerprints can be found (either in primary or disk)
    let total = num_threads * fps_per_thread;
    let mut missing = Vec::new();
    for t in 0..num_threads {
        let base = (t * fps_per_thread) + 1;
        for i in 0..fps_per_thread {
            let v = (base + i) as u64;
            if set.contains_checked(fp(v)) != LookupOutcome::Present {
                missing.push(v);
            }
        }
    }

    assert!(
        missing.is_empty(),
        "Lost {} fingerprints during concurrent eviction: {:?}{}",
        missing.len(),
        &missing[..missing.len().min(10)],
        if missing.len() > 10 { "..." } else { "" }
    );
    assert_eq!(set.len(), total as usize);
    assert!(
        set.eviction_count() >= 1,
        "Expected at least 1 eviction with {} entries in 100-slot primary",
        total
    );
}

/// Regression test for #1760: eviction failure must not cause infinite busy-loop.
///
/// Creates a DiskFingerprintSet with a small primary, fills it to trigger
/// eviction, then makes the disk directory read-only so `do_evict()` fails.
/// Verifies that `insert()` returns (does not loop forever) and surfaces
/// the error via `has_errors()`/`dropped_count()`.
#[cfg(unix)]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_eviction_failure_does_not_loop_forever() {
    use std::os::unix::fs::PermissionsExt;

    let tmp_dir = tempfile::tempdir().unwrap();
    // Small primary: eviction triggers at ~75 entries (100 slots * 0.75 load factor).
    let set = DiskFingerprintSet::new(100, tmp_dir.path()).unwrap();

    // Fill primary to near-capacity (just below eviction threshold).
    for i in 1..=70 {
        set.insert_checked(fp(i));
    }
    assert!(!set.has_errors(), "no errors before eviction failure");

    // Make the disk directory read-only so do_evict() fails on file creation.
    let perms = std::fs::Permissions::from_mode(0o444);
    std::fs::set_permissions(tmp_dir.path(), perms).unwrap();

    // Insert enough to trigger eviction. Before #1760 fix, this would loop forever.
    for i in 71..=120 {
        set.insert_checked(fp(i));
    }

    // Restore permissions so tempdir cleanup works.
    let perms = std::fs::Permissions::from_mode(0o755);
    std::fs::set_permissions(tmp_dir.path(), perms).unwrap();

    // Verify error was recorded (eviction failed, fingerprints dropped).
    assert!(
        set.has_errors(),
        "eviction I/O failure should set error flag"
    );
    assert!(
        set.dropped_count() >= 1,
        "dropped count should be non-zero after eviction failure"
    );
}

/// Regression test for #1760: insert_checked() returns StorageFault on eviction failure.
///
/// Strengthens `test_disk_fpset_eviction_failure_does_not_loop_forever` by verifying
/// the typed InsertOutcome (not just the bool shim). When do_evict() fails (disk read-only),
/// insert_checked() must return StorageFault after bounded retries, not loop forever.
#[cfg(unix)]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_fpset_insert_checked_returns_storage_fault_on_eviction_failure() {
    use std::os::unix::fs::PermissionsExt;

    let tmp_dir = tempfile::tempdir().unwrap();
    let set = DiskFingerprintSet::new(100, tmp_dir.path()).unwrap();

    // Fill primary to near-capacity.
    for i in 1..=70 {
        assert_eq!(
            set.insert_checked(fp(i)),
            InsertOutcome::Inserted,
            "initial inserts should succeed"
        );
    }

    // Make the disk directory read-only so do_evict() fails.
    std::fs::set_permissions(tmp_dir.path(), std::fs::Permissions::from_mode(0o444)).unwrap();

    // Insert beyond capacity to trigger eviction. Use insert_checked() directly
    // to verify the typed outcome.
    let mut saw_storage_fault = false;
    for i in 71..=120 {
        match set.insert_checked(fp(i)) {
            InsertOutcome::Inserted | InsertOutcome::AlreadyPresent => {}
            InsertOutcome::StorageFault(fault) => {
                saw_storage_fault = true;
                assert_eq!(fault.backend, "disk", "fault should identify disk backend");
                assert_eq!(fault.operation, "insert", "fault should identify insert op");
                break;
            }
            _ => unreachable!(),
        }
    }

    // Restore permissions for cleanup.
    std::fs::set_permissions(tmp_dir.path(), std::fs::Permissions::from_mode(0o755)).unwrap();

    assert!(
        saw_storage_fault,
        "insert_checked must return StorageFault when eviction repeatedly fails"
    );
    assert!(set.has_errors(), "disk_error_count should be non-zero");
}
