// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shard backend trait and implementations for [`super::sharded::ShardedFingerprintSet`].
//!
//! Extracted from `sharded.rs` (Part of #3472) to keep files under 500 production lines.
//!
//! Provides:
//! - [`ShardBackend`]: trait for shard-local fingerprint storage
//! - [`FxHashSetShard`]: in-memory shard using `FxHashSet` (default)
//! - [`DiskShard`]: disk-backed shard wrapping `DiskFingerprintSet`

use crate::state::Fingerprint;
use rustc_hash::FxHashSet;
use std::io;
use std::path::PathBuf;

use super::contracts::{FingerprintSet, InsertOutcome, LookupOutcome, StorageFault, StorageStats};
use super::disk::DiskFingerprintSet;

/// A shard-local fingerprint backend. Must be `Send + Sync` for cross-thread access.
///
/// The `RwLock` is external (owned by `ShardedFingerprintSet`), so backends
/// don't need internal synchronization. `&mut self` methods are called under
/// a write lock; `&self` methods under a read lock.
///
/// The optional methods (`shard_has_errors`, `shard_begin_checkpoint`, etc.)
/// allow disk-backed shards to surface error/checkpoint behavior through the
/// generic `FingerprintSet` impl on `ShardedFingerprintSet<S>`.
///
/// Part of #2568: composable storage — Step 2.
pub trait ShardBackend: Send + Sync {
    /// Insert a fingerprint. Returns `Ok(true)` if newly inserted, `Ok(false)` if already present.
    /// Returns `Err(StorageFault)` on disk I/O or other backend errors.
    fn shard_insert(&mut self, fp: Fingerprint) -> Result<bool, StorageFault>;
    /// Check if a fingerprint is present.
    /// Returns `Err(StorageFault)` on disk I/O or other backend errors.
    fn shard_contains(&self, fp: &Fingerprint) -> Result<bool, StorageFault>;
    /// Number of fingerprints in this shard.
    fn shard_len(&self) -> usize;

    /// Whether this shard has encountered storage errors.
    fn shard_has_errors(&self) -> bool {
        false
    }
    /// Count of fingerprints dropped due to errors in this shard.
    fn shard_dropped_count(&self) -> usize {
        0
    }
    /// Storage counters for this shard.
    fn shard_stats(&self) -> StorageStats {
        StorageStats {
            memory_count: self.shard_len(),
            ..StorageStats::default()
        }
    }
    /// Whether this shard backend prefers the disk-backed liveness successor graph.
    fn shard_prefers_disk_successor_graph(&self) -> bool {
        false
    }
    /// Prepare this shard for checkpoint serialization.
    fn shard_begin_checkpoint(&self) -> Result<(), StorageFault> {
        Ok(())
    }
    /// Finalize a checkpoint for this shard.
    fn shard_commit_checkpoint(&self) -> Result<(), StorageFault> {
        Ok(())
    }
    /// Restore this shard from checkpoint.
    fn shard_recover_checkpoint(&self) -> Result<(), StorageFault> {
        Ok(())
    }
    /// Collect all fingerprints in this shard.
    ///
    /// Part of #2893.
    fn shard_collect_fingerprints(&self) -> Result<Vec<Fingerprint>, StorageFault> {
        Err(StorageFault::new(
            "shard",
            "collect_fingerprints",
            "not implemented for this shard backend",
        ))
    }
}

/// In-memory shard using `FxHashSet` (current default).
///
/// This is a zero-cost wrapper that implements [`ShardBackend`] for the
/// existing in-memory hash set backend.
pub struct FxHashSetShard(FxHashSet<Fingerprint>);

impl FxHashSetShard {
    /// Create a new empty shard.
    pub fn new() -> Self {
        Self(FxHashSet::default())
    }

    /// Create a shard with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self(FxHashSet::with_capacity_and_hasher(
            capacity,
            Default::default(),
        ))
    }
}

impl Default for FxHashSetShard {
    fn default() -> Self {
        Self::new()
    }
}

impl ShardBackend for FxHashSetShard {
    #[inline]
    fn shard_insert(&mut self, fp: Fingerprint) -> Result<bool, StorageFault> {
        Ok(self.0.insert(fp))
    }

    #[inline]
    fn shard_contains(&self, fp: &Fingerprint) -> Result<bool, StorageFault> {
        Ok(self.0.contains(fp))
    }

    #[inline]
    fn shard_len(&self) -> usize {
        self.0.len()
    }

    fn shard_collect_fingerprints(&self) -> Result<Vec<Fingerprint>, StorageFault> {
        Ok(self.0.iter().copied().collect())
    }
}

/// Disk-backed shard wrapping [`DiskFingerprintSet`].
///
/// Each shard is an independent two-tier storage instance (mmap primary + sorted
/// disk file). This matches TLC's `MultiFPSet<DiskFPSet>` pattern where each
/// sub-FPSet independently manages its own disk eviction.
///
/// The outer `ShardedFingerprintSet` provides MSB-based routing to reduce lock
/// contention. `DiskFingerprintSet` uses interior mutability for its own
/// eviction coordination, so the outer `RwLock` is redundant but harmless —
/// the contention reduction from sharding is the main benefit.
///
/// Part of #2568: composable storage — Step 2.
pub struct DiskShard(DiskFingerprintSet);

impl DiskShard {
    /// Create a new disk-backed shard.
    ///
    /// Each shard gets its own subdirectory under `base_dir` for independent
    /// disk file management.
    pub(crate) fn new(primary_capacity: usize, shard_dir: impl Into<PathBuf>) -> io::Result<Self> {
        Ok(Self(DiskFingerprintSet::new(primary_capacity, shard_dir)?))
    }
}

impl ShardBackend for DiskShard {
    #[inline]
    fn shard_insert(&mut self, fp: Fingerprint) -> Result<bool, StorageFault> {
        // DiskFingerprintSet uses interior mutability — &self is sufficient.
        // The &mut self requirement is satisfied by the outer RwLock write guard.
        //
        // Fix for #2820/#3204: propagate StorageFault through the Result type
        // instead of panicking, allowing the checker to report a clean error.
        match self.0.insert_checked(fp) {
            InsertOutcome::Inserted => Ok(true),
            InsertOutcome::AlreadyPresent => Ok(false),
            InsertOutcome::StorageFault(fault) => Err(fault),
            _ => unreachable!(),
        }
    }

    #[inline]
    fn shard_contains(&self, fp: &Fingerprint) -> Result<bool, StorageFault> {
        match self.0.contains_checked(*fp) {
            LookupOutcome::Present => Ok(true),
            LookupOutcome::Absent => Ok(false),
            LookupOutcome::StorageFault(fault) => Err(fault),
            _ => unreachable!(),
        }
    }

    #[inline]
    fn shard_len(&self) -> usize {
        self.0.len()
    }

    fn shard_has_errors(&self) -> bool {
        self.0.has_errors()
    }

    fn shard_dropped_count(&self) -> usize {
        self.0.dropped_count()
    }

    fn shard_stats(&self) -> StorageStats {
        self.0.stats()
    }

    fn shard_prefers_disk_successor_graph(&self) -> bool {
        true
    }

    fn shard_begin_checkpoint(&self) -> Result<(), StorageFault> {
        self.0.begin_checkpoint()
    }

    fn shard_commit_checkpoint(&self) -> Result<(), StorageFault> {
        self.0.commit_checkpoint()
    }

    fn shard_recover_checkpoint(&self) -> Result<(), StorageFault> {
        self.0.recover_checkpoint()
    }

    fn shard_collect_fingerprints(&self) -> Result<Vec<Fingerprint>, StorageFault> {
        self.0.collect_fingerprints()
    }
}
