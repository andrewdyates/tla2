// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sharded fingerprint set for parallel model checking.
//!
//! [`ShardedFingerprintSet`] partitions fingerprints by their most significant
//! bits into N shards (where N = 2^shard_bits), similar to TLC's MultiFPSet.
//! Each shard is protected by its own `RwLock` and implements [`ShardBackend`].
//!
//! The default shard type is [`FxHashSetShard`] (in-memory). For disk-backed
//! shards, use `ShardedFingerprintSet<DiskShard>` (Part of #2568, Step 3).
//!
//! Shard backend definitions live in the sibling `sharded_backend` module
//! (Part of #3472 file split).

use crate::state::Fingerprint;
use std::io;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};

use super::contracts::{FingerprintSet, InsertOutcome, LookupOutcome, StorageFault, StorageStats};
pub use super::sharded_backend::{DiskShard, FxHashSetShard, ShardBackend};

/// Sharded fingerprint set for parallel model checking.
///
/// This implementation is similar to TLC's MultiFPSet - it partitions fingerprints
/// by their most significant bits into N shards (where N = 2^shard_bits).
/// Each shard implements [`ShardBackend`] and is protected by its own `RwLock`.
///
/// The default shard type `S = FxHashSetShard` provides the existing in-memory
/// behavior. For disk-backed shards, use `ShardedFingerprintSet<DiskShard>`
/// (constructed via `FingerprintSetFactory` with `StorageMode::ShardedDisk`).
///
/// This provides:
/// - Good distribution: fingerprints are already hashes, so MSB distribution is uniform
/// - Low contention: with 64 shards and 8 workers, collision probability is ~12.5%
/// - Simple implementation: just an array of locked shard backends
/// - Cache-friendly: each shard can fit in L1/L2 cache when small
/// - Composable: any `ShardBackend` can be plugged in per shard
///
/// # Example
///
/// ```rust
/// use tla_check::{ShardedFingerprintSet, InsertOutcome, LookupOutcome};
/// use tla_check::Fingerprint;
///
/// let set = ShardedFingerprintSet::new(6); // 2^6 = 64 shards
/// let fp = Fingerprint(12345678u64);
/// assert_eq!(set.contains_checked(fp), LookupOutcome::Absent);
/// assert_eq!(set.insert_checked(fp), InsertOutcome::Inserted);
/// assert_eq!(set.contains_checked(fp), LookupOutcome::Present);
/// assert_eq!(set.insert_checked(fp), InsertOutcome::AlreadyPresent);
/// ```
pub struct ShardedFingerprintSet<S: ShardBackend = FxHashSetShard> {
    /// The shards — each is a `RwLock<S>` where `S` implements `ShardBackend`.
    shards: Box<[parking_lot::RwLock<S>]>,
    /// Number of bits used for sharding (log2 of shard count)
    shard_bits: u32,
    /// Mask for extracting shard index: (1 << shard_bits) - 1
    shard_mask: usize,
    /// Shift amount: 64 - shard_bits (to get MSB)
    shift: u32,
    /// Total count of distinct fingerprints inserted.
    ///
    /// ORDERING: Writers use `Release` (in `insert_checked`) so that readers
    /// using `Acquire` (in `len`) see all preceding inserts. This matters for
    /// `snapshot_states_at_stop` on ARM where `Relaxed` loads may return a
    /// stale cached value. See design doc
    /// `designs/2026-02-27-1911-parallel-checker-safety-contracts.md` Contract 3.
    count: AtomicUsize,
}

impl ShardedFingerprintSet<FxHashSetShard> {
    /// Create a new sharded fingerprint set with in-memory shards.
    ///
    /// # Arguments
    ///
    /// * `shard_bits` - Number of bits for sharding. Creates 2^shard_bits shards.
    ///   Recommended: 6 (64 shards) for 8-16 workers, 8 (256 shards) for 32+ workers.
    ///
    /// # Panics
    ///
    /// Panics if shard_bits is 0 or > 16.
    pub fn new(shard_bits: u32) -> Self {
        assert!(
            shard_bits > 0 && shard_bits <= 16,
            "shard_bits must be 1-16"
        );

        let num_shards = 1usize << shard_bits;
        let shards: Vec<_> = (0..num_shards)
            .map(|_| parking_lot::RwLock::new(FxHashSetShard::new()))
            .collect();

        ShardedFingerprintSet {
            shards: shards.into_boxed_slice(),
            shard_bits,
            shard_mask: num_shards - 1,
            shift: 64 - shard_bits,
            count: AtomicUsize::new(0),
        }
    }

    /// Create with a specific number of shards (must be power of 2).
    #[allow(dead_code)] // Public API used in tests
    pub fn with_shards(num_shards: usize) -> Self {
        assert!(
            num_shards.is_power_of_two(),
            "num_shards must be power of 2"
        );
        let shard_bits = num_shards.trailing_zeros();
        Self::new(shard_bits)
    }

    /// Create a new sharded fingerprint set with pre-allocated capacity.
    ///
    /// Part of #229: Pre-allocating capacity reduces FxHashSet resizing during
    /// model checking, which causes performance degradation at scale. For MCBakery
    /// N=3 (6M states), pre-allocation avoids ~20 resize events per shard.
    ///
    /// # Arguments
    ///
    /// * `shard_bits` - Number of bits for sharding. Creates 2^shard_bits shards.
    /// * `total_capacity` - Total expected capacity. Each shard gets capacity/num_shards.
    ///
    /// # Panics
    ///
    /// Panics if shard_bits is 0 or > 16.
    pub fn new_with_capacity(shard_bits: u32, total_capacity: usize) -> Self {
        assert!(
            shard_bits > 0 && shard_bits <= 16,
            "shard_bits must be 1-16"
        );

        let num_shards = 1usize << shard_bits;
        let per_shard = total_capacity.div_ceil(num_shards);
        let shards: Vec<_> = (0..num_shards)
            .map(|_| parking_lot::RwLock::new(FxHashSetShard::with_capacity(per_shard)))
            .collect();

        ShardedFingerprintSet {
            shards: shards.into_boxed_slice(),
            shard_bits,
            shard_mask: num_shards - 1,
            shift: 64 - shard_bits,
            count: AtomicUsize::new(0),
        }
    }
}

impl<S: ShardBackend> ShardedFingerprintSet<S> {
    /// Construct from a pre-built vector of shard backends.
    ///
    /// This is the generic constructor used by `FingerprintSetFactory` to create
    /// `ShardedFingerprintSet<DiskShard>` and other composite backends.
    ///
    /// # Panics
    ///
    /// Panics if `shards` is empty, not a power of 2, or requires more than 16
    /// shard bits (i.e., more than 65536 shards).
    pub(crate) fn from_shards(shards: Vec<S>) -> Self {
        let num_shards = shards.len();
        assert!(
            num_shards > 0 && num_shards.is_power_of_two(),
            "shard count must be a positive power of 2, got {}",
            num_shards,
        );
        let shard_bits = num_shards.trailing_zeros();
        assert!(
            (1..=16).contains(&shard_bits),
            "shard_bits must be 1-16, got {} (from {} shards)",
            shard_bits,
            num_shards,
        );

        let shards: Vec<_> = shards.into_iter().map(parking_lot::RwLock::new).collect();

        ShardedFingerprintSet {
            shards: shards.into_boxed_slice(),
            shard_bits,
            shard_mask: num_shards - 1,
            shift: 64 - shard_bits,
            count: AtomicUsize::new(0),
        }
    }

    /// Get the shard index for a fingerprint (using MSB like TLC's MultiFPSet).
    #[inline]
    fn shard_index(&self, fp: Fingerprint) -> usize {
        // Use MSB for partitioning (same as TLC: fp >>> fpbits)
        (fp.0 >> self.shift) as usize & self.shard_mask
    }

    #[inline]
    fn with_shard_fault_context(
        idx: usize,
        context: &'static str,
        fault: StorageFault,
    ) -> StorageFault {
        let StorageFault {
            backend,
            operation,
            detail,
            ..
        } = fault;
        StorageFault::new(
            backend,
            operation,
            format!("shard {idx} {context}: {detail}"),
        )
    }

    /// Insert a fingerprint with typed outcome.
    ///
    /// Returns [`InsertOutcome::Inserted`] if newly inserted,
    /// [`InsertOutcome::AlreadyPresent`] if already present.
    /// In-memory storage never produces [`InsertOutcome::StorageFault`].
    pub fn insert_checked(&self, fp: Fingerprint) -> InsertOutcome {
        let idx = self.shard_index(fp);
        // Typical TLC-style workloads generate many duplicate successors. Avoid taking an
        // exclusive write lock when the fingerprint is already present by checking under a
        // shared read lock first.
        {
            let shard = self.shards[idx].read();
            match shard.shard_contains(&fp) {
                Ok(true) => return InsertOutcome::AlreadyPresent,
                Ok(false) => {}
                Err(fault) => {
                    return InsertOutcome::StorageFault(Self::with_shard_fault_context(
                        idx,
                        "during insert precheck",
                        fault,
                    ))
                }
            }
        }

        // Racy with other inserters between the read and write locks.
        let mut shard = self.shards[idx].write();
        match shard.shard_insert(fp) {
            Ok(true) => {
                // ORDERING: Release pairs with the Acquire load in `len()`, ensuring
                // that a reader who sees this incremented count also sees the shard
                // mutation that preceded it. Critical for `snapshot_states_at_stop`
                // on ARM (Apple Silicon) where Relaxed loads may return stale values.
                self.count.fetch_add(1, Ordering::Release);
                InsertOutcome::Inserted
            }
            Ok(false) => InsertOutcome::AlreadyPresent,
            Err(fault) => InsertOutcome::StorageFault(Self::with_shard_fault_context(
                idx,
                "during insert",
                fault,
            )),
        }
    }

    /// Check if a fingerprint is present with typed outcome.
    ///
    /// Returns [`LookupOutcome::Present`] or [`LookupOutcome::Absent`].
    /// Disk-backed shards may produce [`LookupOutcome::StorageFault`].
    pub fn contains_checked(&self, fp: Fingerprint) -> LookupOutcome {
        let idx = self.shard_index(fp);
        let shard = self.shards[idx].read();
        match shard.shard_contains(&fp) {
            Ok(true) => LookupOutcome::Present,
            Ok(false) => LookupOutcome::Absent,
            Err(fault) => LookupOutcome::StorageFault(Self::with_shard_fault_context(
                idx,
                "during lookup",
                fault,
            )),
        }
    }

    /// Return the total number of distinct fingerprints inserted.
    ///
    /// ORDERING: Acquire pairs with the Release in `insert_checked`, ensuring
    /// the returned count reflects all inserts that happened-before this load.
    /// Used by `snapshot_states_at_stop` to capture an accurate state count
    /// at the moment a worker detects a terminal event.
    pub fn len(&self) -> usize {
        self.count.load(Ordering::Acquire)
    }

    /// Check if empty.
    #[allow(dead_code)] // Public API used in tests
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return the number of shards.
    #[allow(dead_code)] // Public API used in tests
    pub fn num_shards(&self) -> usize {
        self.shards.len()
    }

    /// Return the number of bits used for sharding.
    #[allow(dead_code)] // Public API used in tests
    pub fn shard_bits(&self) -> u32 {
        self.shard_bits
    }
}

impl<S: ShardBackend> tla_mc_core::FingerprintSet<Fingerprint> for ShardedFingerprintSet<S> {
    fn insert_checked(&self, fp: Fingerprint) -> InsertOutcome {
        ShardedFingerprintSet::insert_checked(self, fp)
    }

    fn contains_checked(&self, fp: Fingerprint) -> LookupOutcome {
        ShardedFingerprintSet::contains_checked(self, fp)
    }

    fn len(&self) -> usize {
        ShardedFingerprintSet::len(self)
    }

    fn has_errors(&self) -> bool {
        self.shards.iter().any(|s| s.read().shard_has_errors())
    }

    fn dropped_count(&self) -> usize {
        self.shards
            .iter()
            .map(|s| s.read().shard_dropped_count())
            .sum()
    }
}

impl<S: ShardBackend> FingerprintSet for ShardedFingerprintSet<S> {
    fn stats(&self) -> StorageStats {
        let mut stats = StorageStats::default();
        for shard in self.shards.iter() {
            stats.accumulate(shard.read().shard_stats());
        }
        stats
    }

    fn prefers_disk_successor_graph(&self) -> bool {
        self.shards
            .first()
            .is_some_and(|shard| shard.read().shard_prefers_disk_successor_graph())
    }

    fn begin_checkpoint(&self) -> Result<(), StorageFault> {
        for shard in self.shards.iter() {
            shard.read().shard_begin_checkpoint()?;
        }
        Ok(())
    }

    fn commit_checkpoint(&self) -> Result<(), StorageFault> {
        for shard in self.shards.iter() {
            shard.read().shard_commit_checkpoint()?;
        }
        Ok(())
    }

    fn recover_checkpoint(&self) -> Result<(), StorageFault> {
        for shard in self.shards.iter() {
            shard.read().shard_recover_checkpoint()?;
        }
        Ok(())
    }

    fn collect_fingerprints(&self) -> Result<Vec<Fingerprint>, StorageFault> {
        let mut result = Vec::with_capacity(self.len());
        for shard in self.shards.iter() {
            result.extend(shard.read().shard_collect_fingerprints()?);
        }
        Ok(result)
    }
}

// ============================================================================
// Disk-backed shard specialization (Part of #2568, Step 3)
// ============================================================================

impl ShardedFingerprintSet<DiskShard> {
    /// Create a sharded disk-backed fingerprint set.
    ///
    /// Each shard gets its own subdirectory (`shard_0/`, `shard_1/`, ...) under
    /// `base_dir` for independent disk file management. This matches TLC's
    /// `MultiFPSet<OffHeapDiskFPSet>` architecture.
    ///
    /// # Arguments
    ///
    /// * `shard_bits` - Number of bits for sharding. Creates 2^shard_bits shards.
    ///   Must be 1-16.
    /// * `primary_capacity_per_shard` - In-memory primary tier capacity per shard.
    /// * `base_dir` - Base directory. Each shard creates a subdirectory.
    pub(crate) fn new_disk(
        shard_bits: u32,
        primary_capacity_per_shard: usize,
        base_dir: impl AsRef<Path>,
    ) -> io::Result<Self> {
        assert!(
            (1..=16).contains(&shard_bits),
            "shard_bits must be 1-16, got {}",
            shard_bits,
        );

        let num_shards = 1usize << shard_bits;
        let base = base_dir.as_ref();

        let mut shards = Vec::with_capacity(num_shards);
        for i in 0..num_shards {
            let shard_dir = base.join(format!("shard_{i}"));
            shards.push(DiskShard::new(primary_capacity_per_shard, shard_dir)?);
        }

        Ok(Self::from_shards(shards))
    }
}
