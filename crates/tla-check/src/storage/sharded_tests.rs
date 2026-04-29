// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for sharded fingerprint set

use super::contracts::{InsertOutcome, LookupOutcome, StorageFault};
use super::sharded::*;
use crate::state::Fingerprint;

#[derive(Default)]
struct FaultingShard {
    insert_fault: Option<StorageFault>,
    contains_fault: Option<StorageFault>,
}

impl FaultingShard {
    fn with_insert_fault(detail: &str) -> Self {
        Self {
            insert_fault: Some(StorageFault::new("disk", "insert", detail)),
            contains_fault: None,
        }
    }

    fn with_contains_fault(detail: &str) -> Self {
        Self {
            insert_fault: None,
            contains_fault: Some(StorageFault::new("disk", "contains", detail)),
        }
    }
}

impl ShardBackend for FaultingShard {
    fn shard_insert(&mut self, _fp: Fingerprint) -> Result<bool, StorageFault> {
        match &self.insert_fault {
            Some(fault) => Err(fault.clone()),
            None => Ok(true),
        }
    }

    fn shard_contains(&self, _fp: &Fingerprint) -> Result<bool, StorageFault> {
        match &self.contains_fault {
            Some(fault) => Err(fault.clone()),
            None => Ok(false),
        }
    }

    fn shard_len(&self) -> usize {
        0
    }
}

#[test]
fn test_fxhashset_shard_insert_contains() {
    let mut shard = FxHashSetShard::new();
    let fp = Fingerprint(0xDEAD_BEEF);

    assert!(!shard.shard_contains(&fp).unwrap());
    assert!(shard.shard_insert(fp).unwrap());
    assert!(shard.shard_contains(&fp).unwrap());
    // Duplicate insert returns false
    assert!(!shard.shard_insert(fp).unwrap());
    assert_eq!(shard.shard_len(), 1);
}

#[test]
fn test_disk_shard_insert_contains_consistency() {
    // Verify DiskShard.shard_contains returns correct Results and is
    // consistent with shard_insert (errors propagate as StorageFault).
    let dir = tempfile::tempdir().unwrap();
    let mut shard = DiskShard::new(1024, dir.path().join("shard_0")).unwrap();
    let fp = Fingerprint(0xCAFE_BABE);

    assert!(!shard.shard_contains(&fp).unwrap());
    assert!(shard.shard_insert(fp).unwrap());
    assert!(shard.shard_contains(&fp).unwrap());
    assert!(!shard.shard_insert(fp).unwrap());
    assert_eq!(shard.shard_len(), 1);
}

#[test]
fn test_sharded_contains_after_insert() {
    let set = ShardedFingerprintSet::new(2); // 4 shards
    let fps: Vec<_> = (0..100).map(|i| Fingerprint(i * 7919)).collect();

    for &fp in &fps {
        assert_eq!(set.contains_checked(fp), LookupOutcome::Absent);
        assert_eq!(set.insert_checked(fp), InsertOutcome::Inserted);
        assert_eq!(set.contains_checked(fp), LookupOutcome::Present);
    }
    assert_eq!(set.len(), 100);
}

#[test]
fn test_insert_checked_surfaces_shard_context_on_insert_fault() {
    let set = ShardedFingerprintSet::from_shards(vec![
        FaultingShard::default(),
        FaultingShard::with_insert_fault("permission denied"),
    ]);
    let fp = Fingerprint(1 << 63);

    match set.insert_checked(fp) {
        InsertOutcome::StorageFault(fault) => {
            assert_eq!(fault.backend, "disk");
            assert_eq!(fault.operation, "insert");
            assert!(
                fault.detail.contains("shard 1 during insert"),
                "fault detail should identify the failing shard and insert path: {fault}"
            );
            assert!(
                fault.detail.contains("permission denied"),
                "fault detail should preserve backend detail: {fault}"
            );
        }
        other => panic!("expected insert storage fault, got {other:?}"),
    }
}

#[test]
fn test_contains_checked_surfaces_shard_context_on_lookup_fault() {
    let set = ShardedFingerprintSet::from_shards(vec![
        FaultingShard::default(),
        FaultingShard::with_contains_fault("missing fingerprints.fp"),
    ]);
    let fp = Fingerprint(1 << 63);

    match set.contains_checked(fp) {
        LookupOutcome::StorageFault(fault) => {
            assert_eq!(fault.backend, "disk");
            assert_eq!(fault.operation, "contains");
            assert!(
                fault.detail.contains("shard 1 during lookup"),
                "fault detail should identify the failing shard and lookup path: {fault}"
            );
            assert!(
                fault.detail.contains("missing fingerprints.fp"),
                "fault detail should preserve backend detail: {fault}"
            );
        }
        other => panic!("expected lookup storage fault, got {other:?}"),
    }
}
