// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::fp;
use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_error_tracking_no_errors() {
    // Test that a normal use case doesn't report errors
    let set = MmapFingerprintSet::new(1000, None).unwrap();

    assert!(!set.has_errors(), "New set should not have errors");
    assert_eq!(set.dropped_count(), 0, "New set should have 0 dropped");

    // Insert some fingerprints
    for i in 1..=100 {
        set.insert(fp(i)).unwrap();
    }

    assert!(!set.has_errors(), "Normal inserts should not cause errors");
    assert_eq!(set.dropped_count(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_error_tracking_overflow() {
    // Create a very small table that will overflow quickly
    let set = MmapFingerprintSet::with_load_factor(10, None, 0.9).expect("Failed to create set");

    assert!(!set.has_errors(), "New set should not have errors");
    assert_eq!(set.dropped_count(), 0);

    // Fill the table to trigger overflow errors
    // With capacity 10 and 90% load factor, we can fit about 9 entries
    // After that, inserts should start failing
    let mut inserted = 0;
    let mut errors = 0;
    for i in 1..=50 {
        match set.insert(fp(i * 1000)) {
            // Use spaced values to avoid linear probing finding slots
            Ok(true) => inserted += 1,
            Ok(false) => {} // Already present (shouldn't happen with unique values)
            Err(_) => errors += 1,
        }
    }

    // We should have some successful inserts and some errors
    assert!(inserted > 0, "Should have some successful inserts");
    assert!(errors > 0, "Should have some errors from overflow");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_error_tracking_via_trait() {
    // Test that error tracking works through the FingerprintSet trait
    let set = MmapFingerprintSet::with_load_factor(10, None, 0.9).expect("Failed to create set");

    let trait_obj: &dyn FingerprintSet = &set;

    assert!(!trait_obj.has_errors(), "New set should not have errors");
    assert_eq!(trait_obj.dropped_count(), 0);

    // Fill through the trait interface until we trigger errors
    for i in 1..=50 {
        trait_obj.insert_checked(fp(i * 1000));
    }

    // Now errors should be tracked via the trait
    // Note: The trait impl calls record_error() on overflow
    assert!(
        trait_obj.has_errors(),
        "Trait should report errors after overflow"
    );
    assert!(
        trait_obj.dropped_count() > 0,
        "Trait should report dropped count"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mmap_insert_checked_distinguishes_storage_fault_from_duplicate() {
    let set = MmapFingerprintSet::with_load_factor(4, None, 0.25).expect("Failed to create set");
    let trait_obj: &dyn FingerprintSet = &set;

    assert!(matches!(
        trait_obj.insert_checked(fp(1)),
        InsertOutcome::Inserted
    ));
    match trait_obj.insert_checked(fp(2)) {
        InsertOutcome::StorageFault(_) => {}
        other => panic!("expected StorageFault when table is full, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fingerprint_storage_error_tracking() {
    // Test that FingerprintStorage properly forwards error tracking
    let storage = FingerprintStorage::mmap(10, None).expect("Failed to create mmap storage");

    assert!(!storage.has_errors(), "New storage should not have errors");
    assert_eq!(storage.dropped_count(), 0);

    // In-memory storage should never have errors
    let in_mem = FingerprintStorage::in_memory();
    assert!(!in_mem.has_errors(), "In-memory never has errors");
    assert_eq!(in_mem.dropped_count(), 0);

    // Fill up in-memory (it can grow indefinitely)
    for i in 1..=100 {
        in_mem.insert_checked(fp(i));
    }
    assert!(
        !in_mem.has_errors(),
        "In-memory should never report errors (can grow)"
    );
}

// ========== Capacity status tests ==========

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_capacity_status_normal() {
    // Empty set should be Normal
    let set = MmapFingerprintSet::new(1000, None).unwrap();
    assert_eq!(set.capacity_status(), CapacityStatus::Normal);

    // Set at low usage should be Normal
    for i in 1..=100 {
        set.insert(fp(i)).unwrap();
    }
    // 100/1000 = 10% usage, well below warning threshold
    assert_eq!(
        set.capacity_status(),
        CapacityStatus::Normal,
        "10% usage should be Normal"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_capacity_status_warning() {
    // Create set with default 0.75 load factor
    // Warning threshold: 80% of 0.75 = 60% usage
    let set = MmapFingerprintSet::new(1000, None).unwrap();

    // Fill to just above warning threshold (60% = 600 entries)
    for i in 1..=610 {
        let _ = set.insert(fp(i));
    }

    match set.capacity_status() {
        CapacityStatus::Warning { usage, .. } => {
            assert!(usage >= 0.60, "Usage should be >= 60%");
            assert!(usage < 0.72, "Usage should be < 72% (critical threshold)");
        }
        other => panic!("Expected Warning status, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_capacity_status_critical() {
    // Create set with default 0.75 load factor
    // Critical threshold: 95% of 0.75 = 71.25% usage
    let set = MmapFingerprintSet::new(1000, None).unwrap();

    // Fill to just above critical threshold (72% = 720 entries)
    for i in 1..=720 {
        let _ = set.insert(fp(i));
    }

    match set.capacity_status() {
        CapacityStatus::Critical { usage, .. } => {
            assert!(usage >= 0.71, "Usage should be >= 71%");
        }
        other => panic!("Expected Critical status, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_capacity_status_via_trait() {
    // Test that capacity_status works through the FingerprintSet trait
    let set = MmapFingerprintSet::new(100, None).unwrap();
    let trait_obj: &dyn FingerprintSet = &set;

    assert_eq!(trait_obj.capacity_status(), CapacityStatus::Normal);

    // Fill to warning level (60% of 100 = 60 entries)
    for i in 1..=65 {
        trait_obj.insert_checked(fp(i));
    }

    // Should now be Warning
    assert!(
        matches!(trait_obj.capacity_status(), CapacityStatus::Warning { .. }),
        "65% should trigger Warning status"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_capacity_status_fingerprint_storage() {
    // Test that FingerprintStorage properly forwards capacity_status
    let storage = FingerprintStorage::mmap(100, None).expect("Failed to create mmap storage");

    assert_eq!(
        storage.capacity_status(),
        CapacityStatus::Normal,
        "New mmap storage should be Normal"
    );

    // In-memory storage should always be Normal (growable)
    let in_mem = FingerprintStorage::in_memory();
    assert_eq!(
        in_mem.capacity_status(),
        CapacityStatus::Normal,
        "In-memory storage should always be Normal"
    );

    // Fill in-memory with many entries - should still be Normal
    for i in 1..=1000 {
        in_mem.insert_checked(fp(i));
    }
    assert_eq!(
        in_mem.capacity_status(),
        CapacityStatus::Normal,
        "In-memory storage should still be Normal after many inserts"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_capacity_status_dashset_default() {
    // DashSet uses default implementation (always Normal)
    let set: Box<dyn FingerprintSet> = Box::new(dashmap::DashSet::<Fingerprint>::new());
    assert_eq!(
        set.capacity_status(),
        CapacityStatus::Normal,
        "DashSet should default to Normal (growable)"
    );

    // Fill with many entries
    for i in 1..=1000 {
        set.insert_checked(fp(i));
    }
    assert_eq!(
        set.capacity_status(),
        CapacityStatus::Normal,
        "DashSet should still be Normal (growable)"
    );
}
