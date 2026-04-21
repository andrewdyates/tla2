// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Capacity status helper and mmap fingerprint storage integration tests

use super::parse_module;
use super::*;
use crate::storage::CapacityStatus;
use crate::CheckError;
use std::sync::atomic::{AtomicU8, Ordering};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_capacity_status_to_u8() {
    assert_eq!(
        capacity_status_to_u8(&CapacityStatus::Normal),
        CAPACITY_NORMAL
    );
    assert_eq!(
        capacity_status_to_u8(&CapacityStatus::Warning {
            count: 100,
            capacity: 150,
            usage: 0.66,
        }),
        CAPACITY_WARNING
    );
    assert_eq!(
        capacity_status_to_u8(&CapacityStatus::Critical {
            count: 100,
            capacity: 120,
            usage: 0.83,
        }),
        CAPACITY_CRITICAL
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_and_warn_capacity_no_change() {
    // When status doesn't change, no warning should be emitted
    use dashmap::DashSet;

    let set: Arc<dyn FingerprintSet> = Arc::new(DashSet::<Fingerprint>::new());
    let last_status = AtomicU8::new(CAPACITY_NORMAL);

    // DashSet always returns Normal status
    check_and_warn_capacity(set.as_ref(), &last_status);

    // Status should remain Normal
    assert_eq!(last_status.load(Ordering::Relaxed), CAPACITY_NORMAL);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_mmap_fingerprint_storage_integration() {
    let _serial = super::acquire_interner_lock();
    // Test that parallel checker can use mmap storage and reports errors on overflow
    use crate::storage::MmapFingerprintSet;
    use crate::InfraCheckError;

    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };

    // Create mmap storage with very small capacity to trigger overflow
    let mmap_set = MmapFingerprintSet::new(10, None).expect("Failed to create mmap storage");
    let storage: Arc<dyn FingerprintSet> = Arc::new(mmap_set);

    let mut checker = ParallelChecker::new(&module, &config, 1);
    checker.set_deadlock_check(false);
    checker.set_store_states(false);
    checker.set_fingerprint_storage(storage);
    // No max_states set — default is None (unlimited).
    // The unbounded Counter spec will fill the tiny mmap (capacity 10) and overflow.

    let result = checker.check();

    // Should fail due to fingerprint storage overflow.
    // With 1 worker on a tiny table, overflow is the expected outcome.
    let (is_overflow, dropped) = match &result {
        CheckResult::Error {
            error: CheckError::Infra(InfraCheckError::FingerprintOverflow { dropped, .. }),
            ..
        } => (true, *dropped),
        _ => (false, 0),
    };
    assert!(is_overflow, "Expected overflow error, got: {result:?}");
    assert!(dropped > 0, "Should have dropped some fingerprints");
}
