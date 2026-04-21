// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Progressive-warning behavior for the in-memory fingerprint storage cap.
//!
//! Part of #4080: the pre-fix behavior fired exactly one warning the first
//! time `len() >= max_capacity`. Very large specs that blew past the limit
//! continued to grow without further operator visibility, masking silent OOM.
//! The fix re-warns at each doubling threshold (1x, 2x, 4x, 8x, ...).

use super::fp;
use super::*;

fn ingest_through_trait(storage: &FingerprintStorage, n: usize) {
    for i in 1..=n as u64 {
        storage.insert_checked(fp(i));
    }
}

#[test]
fn inmemory_progressive_warning_fires_at_1x_2x_4x() {
    // max_capacity=10 so we can cross 1x, 2x, 4x in a tight loop.
    let storage = FingerprintStorage::in_memory_with_max_capacity(10);

    // Below cap: no warning fired.
    ingest_through_trait(&storage, 9);
    assert_eq!(
        storage.inmemory_last_warned_multiple(),
        Some(0),
        "no warning should fire below max_capacity"
    );

    // Reach 1x: warning fires at multiple=1.
    ingest_through_trait(&storage, 10);
    assert_eq!(
        storage.inmemory_last_warned_multiple(),
        Some(1),
        "first warning should register multiple=1 at max_capacity"
    );

    // Grow to 19 entries (still 1x floor). No re-warn.
    for i in 11..=19u64 {
        storage.insert_checked(fp(i));
    }
    assert_eq!(
        storage.inmemory_last_warned_multiple(),
        Some(1),
        "no re-warn between 1x and 2x thresholds"
    );

    // Hit 2x (20 entries): re-warn at multiple=2.
    storage.insert_checked(fp(20));
    assert_eq!(
        storage.inmemory_last_warned_multiple(),
        Some(2),
        "second warning should register multiple=2 at 2x capacity"
    );

    // Skip straight to 4x (40 entries) to verify the threshold rounds down to
    // the largest power of two <= floor(count/cap).
    for i in 21..=40u64 {
        storage.insert_checked(fp(i));
    }
    assert_eq!(
        storage.inmemory_last_warned_multiple(),
        Some(4),
        "third warning should register multiple=4 at 4x capacity"
    );
}

#[test]
fn inmemory_progressive_warning_is_monotonic_across_updates() {
    // An insert that jumps past multiple thresholds in a single call must
    // still only advance `last_warned_multiple` to the highest crossed
    // power-of-two multiple (not revert to a lower one on subsequent inserts).
    let storage = FingerprintStorage::in_memory_with_max_capacity(4);

    // Pre-seed to 16 entries = 4x the cap.
    ingest_through_trait(&storage, 16);
    assert_eq!(storage.inmemory_last_warned_multiple(), Some(4));

    // An extra insert at 17 entries stays in the 4x band (17/4=4).
    // last_warned_multiple must NOT revert to 1.
    storage.insert_checked(fp(17));
    assert_eq!(
        storage.inmemory_last_warned_multiple(),
        Some(4),
        "warning multiple must be monotonic; later inserts cannot lower it"
    );
}

#[test]
fn inmemory_cap_status_warning_matches_growth() {
    // Independently of the eprintln warning, `capacity_status()` must
    // transition to `CapacityStatus::Warning` once len >= max_capacity.
    // This is the signal the BFS loop reads via `check_and_warn_capacity`.
    let storage = FingerprintStorage::in_memory_with_max_capacity(5);
    assert_eq!(storage.capacity_status(), CapacityStatus::Normal);

    ingest_through_trait(&storage, 4);
    assert_eq!(
        storage.capacity_status(),
        CapacityStatus::Normal,
        "below cap should report Normal"
    );

    ingest_through_trait(&storage, 6);
    match storage.capacity_status() {
        CapacityStatus::Warning {
            count, capacity, ..
        } => {
            assert!(count >= 5, "Warning should report count>=5, got {count}");
            assert_eq!(capacity, 5, "Warning should echo the configured cap");
        }
        other => panic!("expected CapacityStatus::Warning, got {other:?}"),
    }
}
