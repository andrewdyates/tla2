// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::path::Path;
use std::time::Duration;
use tla_check::{
    CheckResult, CheckStats, Fingerprint, FingerprintSet, FingerprintSetFactory,
    FingerprintStorage, InsertOutcome, JsonOutput, StorageConfig, StorageMode, StorageStats,
};

#[test]
fn test_storage_stats_reexport_supports_dyn_fingerprint_set_usage() {
    let storage: Box<dyn FingerprintSet> = Box::new(FingerprintStorage::in_memory());

    assert_eq!(
        storage.insert_checked(Fingerprint(1)),
        InsertOutcome::Inserted
    );

    let stats: StorageStats = FingerprintSet::stats(&*storage);
    assert_eq!(stats.memory_count, 1);
    assert_eq!(stats.disk_count, 0);
    assert_eq!(stats.disk_lookups, 0);
    assert_eq!(stats.disk_hits, 0);
    assert_eq!(stats.eviction_count, 0);
    // Part of #4080: InMemory now reports non-zero memory_bytes estimated
    // from the HashSet's capacity with fragmentation overhead.
    assert!(
        stats.memory_bytes > 0,
        "InMemory stats should report non-zero memory_bytes"
    );
}

#[test]
fn test_storage_stats_reexport_supports_factory_trait_object_usage() {
    let storage = FingerprintSetFactory::create(StorageConfig {
        mode: StorageMode::InMemory,
        ..StorageConfig::default()
    })
    .expect("factory should create in-memory storage");

    assert_eq!(
        storage.insert_checked(Fingerprint(2)),
        InsertOutcome::Inserted
    );

    let stats: StorageStats = FingerprintSet::stats(&*storage);
    assert_eq!(stats.memory_count, 1);
    assert_eq!(stats.disk_count, 0);
    assert_eq!(stats.disk_lookups, 0);
    assert_eq!(stats.disk_hits, 0);
    assert_eq!(stats.eviction_count, 0);
    // Part of #4080: InMemory now reports non-zero memory_bytes estimated
    // from the HashSet's capacity with fragmentation overhead.
    assert!(
        stats.memory_bytes > 0,
        "InMemory stats should report non-zero memory_bytes"
    );
}

#[test]
fn test_json_output_reports_memory_only_storage_stats() {
    let mut storage_stats = StorageStats::default();
    storage_stats.memory_count = 3;
    storage_stats.memory_bytes = 8 * 1024 * 1024;

    let mut stats = CheckStats::default();
    stats.storage_stats = storage_stats;

    let output = JsonOutput::new(Path::new("Spec.tla"), None, "Spec", 1)
        .with_check_result(&CheckResult::Success(stats), Duration::from_secs(1));
    let storage = output
        .statistics
        .storage
        .expect("mmap-style reserved memory should be reported");

    assert_eq!(storage.memory_count, 3);
    assert_eq!(storage.disk_count, 0);
    assert_eq!(storage.memory_bytes, Some(8 * 1024 * 1024));
    assert_eq!(storage.disk_lookups, None);
    assert_eq!(storage.disk_hits, None);
    assert_eq!(storage.eviction_count, None);
}
