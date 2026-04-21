// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::fp;
use super::*;

// ========== MmapTraceLocations tests ==========

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_locations_basic() {
    let locs = MmapTraceLocations::new(1000, None).unwrap();

    // Initially empty
    assert!(locs.is_empty());
    assert_eq!(locs.len(), 0);

    // Insert new mapping
    assert!(locs.insert(fp(12345), 1024).unwrap());
    assert_eq!(locs.len(), 1);
    assert!(locs.contains(&fp(12345)));
    assert_eq!(locs.get(&fp(12345)), Some(1024));

    // Update existing mapping
    assert!(!locs.insert(fp(12345), 2048).unwrap());
    assert_eq!(locs.len(), 1);
    assert_eq!(locs.get(&fp(12345)), Some(2048));

    // Insert different fingerprint
    assert!(locs.insert(fp(67890), 4096).unwrap());
    assert_eq!(locs.len(), 2);
    assert_eq!(locs.get(&fp(67890)), Some(4096));

    // Check non-existent
    assert!(!locs.contains(&fp(99999)));
    assert_eq!(locs.get(&fp(99999)), None);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_locations_fingerprint_zero() {
    // Fingerprint 0 is special-cased
    let locs = MmapTraceLocations::new(100, None).unwrap();

    assert!(!locs.contains(&fp(0)));
    assert!(locs.insert(fp(0), 512).unwrap());
    assert!(locs.contains(&fp(0)));
    assert_eq!(locs.get(&fp(0)), Some(512));
    assert!(!locs.insert(fp(0), 1024).unwrap()); // update
    assert_eq!(locs.get(&fp(0)), Some(1024));
}

/// Regression test for #1535 / #1589: FP(0) and FP(u64::MAX) must map to distinct offsets.
/// Before the has_zero fix, both values could collide via sentinel encoding.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_locations_fingerprint_zero_vs_max_distinct() {
    let locs = MmapTraceLocations::new(100, None).expect("invariant: create trace locs");

    assert!(locs.insert(fp(0), 512).expect("invariant: insert fp(0)"));
    assert!(locs
        .insert(fp(u64::MAX), 1024)
        .expect("invariant: insert fp(MAX)"));
    assert_eq!(locs.len(), 2);

    assert_eq!(locs.get(&fp(0)), Some(512));
    assert_eq!(locs.get(&fp(u64::MAX)), Some(1024));
    assert!(locs.contains(&fp(0)));
    assert!(locs.contains(&fp(u64::MAX)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_locations_many_entries() {
    let locs = MmapTraceLocations::new(10000, None).unwrap();

    // Insert 5000 entries
    for i in 0..5000u64 {
        let v = i.wrapping_mul(0x12345678_9ABCDEF0);
        let offset = i * 16;
        assert!(
            locs.insert(fp(v), offset).unwrap(),
            "failed to insert fp {} at offset {}",
            v,
            offset
        );
    }

    assert_eq!(locs.len(), 5000);

    // Verify all present with correct offsets
    for i in 0..5000u64 {
        let v = i.wrapping_mul(0x12345678_9ABCDEF0);
        let offset = i * 16;
        assert_eq!(locs.get(&fp(v)), Some(offset), "wrong offset for fp {}", v);
    }

    // Verify non-present
    for i in 5000..5100u64 {
        let v = i.wrapping_mul(0x12345678_9ABCDEF0);
        assert!(!locs.contains(&fp(v)), "unexpected fp {}", v);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_locations_load_factor() {
    let locs = MmapTraceLocations::with_load_factor(100, None, 0.5).unwrap();

    // Insert 50 entries (50% load factor)
    for i in 0..50u64 {
        locs.insert(fp(i + 1), i * 16).unwrap();
    }

    // Next insert should fail
    let result = locs.insert(fp(1000), 0);
    assert!(
        result.is_err(),
        "expected TableFull error, got {:?}",
        result
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_locations_file_backed() {
    let tmp_dir = tempfile::tempdir().unwrap();
    let locs = MmapTraceLocations::new(1000, Some(tmp_dir.path().to_path_buf())).unwrap();

    assert!(locs.insert(fp(12345), 1024).unwrap());
    assert_eq!(locs.get(&fp(12345)), Some(1024));

    locs.flush().unwrap();
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_locations_trait_impl() {
    let locs: Box<dyn TraceLocationStorage> =
        Box::new(MmapTraceLocations::new(1000, None).unwrap());

    locs.insert(fp(12345), 1024);
    assert!(locs.contains(&fp(12345)));
    assert_eq!(locs.get(&fp(12345)), Some(1024));
    assert_eq!(locs.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_locations_trait_insert_table_full_does_not_panic_or_insert() {
    // Capacity 2 at 50% load factor means second unique insert fails internally.
    let locs = MmapTraceLocations::with_load_factor(2, None, 0.5).unwrap();
    let trait_obj: &dyn TraceLocationStorage = &locs;

    assert!(trait_obj.insert(fp(1), 16));
    assert_eq!(trait_obj.get(&fp(1)), Some(16));
    assert_eq!(trait_obj.len(), 1);

    // This goes through the trait impl that now logs once on failure.
    // Part of #1446: insert returns false on mmap table-full error.
    assert!(!trait_obj.insert(fp(2), 32));
    assert_eq!(trait_obj.get(&fp(2)), None);
    assert_eq!(trait_obj.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_locations_storage_mmap_insert_table_full_does_not_insert() {
    let locs =
        TraceLocationsStorage::Mmap(MmapTraceLocations::with_load_factor(2, None, 0.5).unwrap());

    assert!(locs.insert(fp(10), 160));
    assert_eq!(locs.get(&fp(10)), Some(160));
    assert_eq!(locs.len(), 1);

    // Exercise the enum dispatch path (TraceLocationsStorage::Mmap arm).
    // Part of #1446: insert returns false on mmap table-full error.
    assert!(!locs.insert(fp(20), 320));
    assert_eq!(locs.get(&fp(20)), None);
    assert_eq!(locs.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_memory_trace_locations() {
    let locs = InMemoryTraceLocations::new();

    assert!(locs.is_empty());

    // Use trait method
    TraceLocationStorage::insert(&locs, fp(111), 500);
    assert_eq!(locs.get(&fp(111)), Some(500));
    assert!(locs.contains(&fp(111)));
    assert_eq!(locs.len(), 1);

    // Update
    TraceLocationStorage::insert(&locs, fp(111), 600);
    assert_eq!(locs.get(&fp(111)), Some(600));
    assert_eq!(locs.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_in_memory_trace_locations_as_trait() {
    let locs: Box<dyn TraceLocationStorage> = Box::new(InMemoryTraceLocations::new());

    locs.insert(fp(222), 1000);
    assert_eq!(locs.get(&fp(222)), Some(1000));
    assert_eq!(locs.len(), 1);
}
