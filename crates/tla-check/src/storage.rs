// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Scalable fingerprint storage for TLA+ model checking.
//!
//! This module provides multiple fingerprint storage backends:
//! - [`MmapFingerprintSet`]: Open-addressing table in memory-mapped files
//! - [`ShardedFingerprintSet`]: MSB-partitioned shards (TLC MultiFPSet pattern)
//! - [`DiskFingerprintSet`]: Two-tier storage with automatic disk eviction
//! - [`FingerprintStorage`]: Unified dispatch enum for backend selection

// Decomposed submodules (wired from storage/ directory).
mod adapters;
pub(crate) mod atomic_adapter;
pub(crate) mod bitmask_map;
pub(crate) mod cas_fpset;
mod contracts;
mod disk;
pub(crate) mod disk_bitmask;
pub(crate) mod disk_bitmask_action;
mod disk_eviction;
mod disk_invariant;
mod disk_lookup;
mod disk_page_lookup;
mod disk_search;
pub(crate) mod disk_successor_graph;
#[cfg(test)]
#[path = "storage/disk_tests.rs"]
mod disk_tests;
pub mod factory;
mod mmap;
pub(crate) mod open_addressing;
mod sharded;
mod sharded_backend;
#[cfg(test)]
mod sharded_tests;
pub(crate) mod successor_graph;
mod trace;

// --- Public API re-exports (maintains identical crate-level API surface) ---
pub(crate) use bitmask_map::{
    reconstruct_check_from_bitmask, ActionBitmaskLookup, ActionBitmaskMap, LiveBitmask,
    StateBitmaskLookup, StateBitmaskMap,
};
pub use contracts::{
    CapacityStatus, FingerprintSet, InsertOutcome, LookupOutcome, StorageFault, StorageStats,
};
pub use disk::DiskFingerprintSet;
pub use mmap::MmapFingerprintSet;
#[allow(unused_imports)]
pub use open_addressing::MmapError;
#[allow(unused_imports)]
pub use sharded::ShardedFingerprintSet;
pub(crate) use successor_graph::SuccessorGraph;
#[allow(unused_imports)]
pub use trace::{
    InMemoryTraceLocations, MmapTraceLocations, TraceLocationStorage, TraceLocationsStorage,
};

// --- Crate-internal re-exports for test access ---
// These items were previously private to the monolithic storage.rs and
// accessed by storage_tests.rs via `use super::*`. Now they live in
// submodules, so we re-import them here for backward compatibility.
// Gated behind #[cfg(test)] since they are only used by storage_tests.rs.
#[cfg(test)]
pub(super) use disk::{
    read_next_fp, EvictGuard, EvictionBarrier, EvictionState, EVICTION_STATUS_FAILURE,
    EVICTION_STATUS_SUCCESS,
};
#[cfg(test)]
pub(super) use disk_search::{FINGERPRINT_BYTES, FPS_PER_PAGE};
#[cfg(test)]
pub(super) use open_addressing::{decode_fingerprint, encode_fingerprint, EMPTY};
#[cfg(test)]
pub(super) use std::sync::atomic::{AtomicU64, Ordering};
#[cfg(test)]
pub(super) use trace::TRACE_ENTRY_SIZE;

// --- Imports for FingerprintStorage ---
use crate::state::{Fingerprint, FpHashSet};
use std::io;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

/// Default maximum capacity for in-memory fingerprint storage.
///
/// When sequential (single-worker) mode uses `FingerprintStorage::InMemory`,
/// the underlying hash set grows unboundedly. At 10M entries (~80 MB for
/// fingerprints alone, plus hash-map overhead), this threshold triggers a
/// warning suggesting `--workers 2` to activate sharded disk mode, which
/// auto-evicts to disk and prevents OOM.
///
/// Override via the `TLA2_INMEMORY_FP_MAX` environment variable.
///
/// Part of #4080: OOM safety — InMemory fingerprint storage capacity guard.
pub const DEFAULT_INMEMORY_MAX_CAPACITY: usize = 10_000_000;

/// Fingerprint storage abstraction that supports different backends.
///
/// For sequential model checking, use `FingerprintStorage::InMemory`.
/// For large state spaces that exceed RAM, use `FingerprintStorage::Mmap`.
/// For billion-state specs, use `FingerprintStorage::Disk` (auto-eviction to disk).
#[non_exhaustive]
#[allow(clippy::large_enum_variant)] // DiskFingerprintSet is large by nature; boxing deferred.
pub enum FingerprintStorage {
    /// In-memory hash set with identity hasher for pre-hashed fingerprints.
    /// Uses parking_lot::RwLock which spins briefly before blocking, making it
    /// efficient for both single-threaded and multi-threaded access.
    ///
    /// Part of #4128: Uses identity hashing (FpHashSet) instead of FxHash.
    /// Fingerprints are already high-quality 64-bit hashes, so additional
    /// hashing degrades distribution at scale (MCBoulanger 51% regression).
    ///
    /// The `max_capacity` field limits unbounded growth. When exceeded, a
    /// warning is logged progressively (at max_capacity, 2x, 4x, 8x, ...)
    /// via `last_warned_multiple`, and `capacity_status()` returns
    /// `CapacityStatus::Warning` so the BFS loop can react.
    ///
    /// Part of #4080: OOM safety — InMemory capacity guard.
    ///
    /// The `last_warned_multiple` field stores the last-warned multiple of
    /// `max_capacity` (0 = never warned, 1 = warned at max, 2 = warned at 2x,
    /// etc.). Progressive re-warning surfaces silent OOM on very large specs
    /// that blow past the initial threshold.
    InMemory {
        set: parking_lot::RwLock<FpHashSet>,
        max_capacity: usize,
        last_warned_multiple: AtomicUsize,
    },
    /// Memory-mapped file (scales beyond RAM, slightly slower).
    Mmap(MmapFingerprintSet),
    /// Disk-backed storage with automatic eviction (for billion-state specs).
    Disk(DiskFingerprintSet),
}

impl FingerprintStorage {
    /// Read the max in-memory capacity from `TLA2_INMEMORY_FP_MAX` env var,
    /// falling back to [`DEFAULT_INMEMORY_MAX_CAPACITY`].
    /// Cached via `OnceLock` (Part of #4114).
    fn inmemory_max_from_env() -> usize {
        static CACHED: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
        *CACHED.get_or_init(|| {
            std::env::var("TLA2_INMEMORY_FP_MAX")
                .ok()
                .and_then(|v| v.parse::<usize>().ok())
                .unwrap_or(DEFAULT_INMEMORY_MAX_CAPACITY)
        })
    }

    /// Create in-memory storage.
    pub fn in_memory() -> Self {
        FingerprintStorage::InMemory {
            set: parking_lot::RwLock::new(crate::state::fp_hashset()),
            max_capacity: Self::inmemory_max_from_env(),
            last_warned_multiple: AtomicUsize::new(0),
        }
    }

    /// Create in-memory storage with pre-allocated capacity.
    ///
    /// Part of #188, #229: Pre-allocating capacity reduces hash set resizing
    /// during model checking, which causes performance degradation at scale.
    /// For MCBakery N=3 (6M states), pre-allocation avoids ~20 resize events
    /// that each trigger O(n) rehashing.
    pub fn in_memory_with_capacity(capacity: usize) -> Self {
        FingerprintStorage::InMemory {
            set: parking_lot::RwLock::new(crate::state::fp_hashset_with_capacity(capacity)),
            max_capacity: Self::inmemory_max_from_env(),
            last_warned_multiple: AtomicUsize::new(0),
        }
    }

    /// Create in-memory storage with an explicit `max_capacity`.
    ///
    /// Test-only helper that bypasses the `TLA2_INMEMORY_FP_MAX` env var,
    /// so unit tests can deterministically exercise the capacity-guard path
    /// (Part of #4080 progressive warning) without polluting process env.
    #[cfg(test)]
    pub(crate) fn in_memory_with_max_capacity(max_capacity: usize) -> Self {
        FingerprintStorage::InMemory {
            set: parking_lot::RwLock::new(crate::state::fp_hashset()),
            max_capacity,
            last_warned_multiple: AtomicUsize::new(0),
        }
    }

    /// Read the last-warned multiple (test-only).
    ///
    /// Returns 0 if no warning has fired, 1 if warned at max_capacity, 2 if
    /// warned at 2x, 4 at 4x, etc. Used by unit tests to assert progressive
    /// warning behavior (Part of #4080).
    #[cfg(test)]
    pub(crate) fn inmemory_last_warned_multiple(&self) -> Option<usize> {
        match self {
            FingerprintStorage::InMemory {
                last_warned_multiple,
                ..
            } => Some(last_warned_multiple.load(AtomicOrdering::Relaxed)),
            _ => None,
        }
    }

    fn warn_inmemory_capacity_if_needed(
        count: usize,
        max_capacity: usize,
        last_warned_multiple: &AtomicUsize,
    ) {
        // Part of #4080: warn progressively (at max_capacity, 2x, 4x, 8x, ...)
        // when in-memory set exceeds capacity. Previously warned only once,
        // which hid unbounded growth from operators on very large specs.
        if max_capacity == 0 || count < max_capacity {
            return;
        }

        // Highest crossed doubling threshold (1, 2, 4, 8, ...).
        // `count / max_capacity` floors to the integer multiple of cap; the
        // highest power-of-two <= that floor is the threshold we warn at.
        let floor_multiple = count / max_capacity;
        let threshold = if floor_multiple <= 1 {
            1
        } else {
            // Largest power of two <= floor_multiple.
            1usize << (usize::BITS - 1 - floor_multiple.leading_zeros())
        };
        let previous = last_warned_multiple.load(AtomicOrdering::Relaxed);
        if threshold > previous
            && last_warned_multiple
                .compare_exchange(
                    previous,
                    threshold,
                    AtomicOrdering::Relaxed,
                    AtomicOrdering::Relaxed,
                )
                .is_ok()
        {
            eprintln!(
                "Warning: in-memory fingerprint storage has {count} entries \
                 (>= {threshold}x capacity of {max_capacity}). Consider using --workers 2 \
                 to enable sharded disk-backed storage, or set \
                 TLA2_INMEMORY_FP_MAX to raise this limit."
            );
        }
    }

    fn insert_batch_prefix_checked(
        fingerprints: &[Fingerprint],
        mut insert: impl FnMut(Fingerprint) -> InsertOutcome,
    ) -> Vec<InsertOutcome> {
        let mut outcomes = Vec::with_capacity(fingerprints.len());
        for &fp in fingerprints {
            let outcome = insert(fp);
            let stop = matches!(&outcome, InsertOutcome::StorageFault(_));
            outcomes.push(outcome);
            if stop {
                break;
            }
        }
        outcomes
    }

    fn insert_batch_value_prefix_checked_into(
        fingerprint_values: &[u64],
        outcomes: &mut Vec<InsertOutcome>,
        mut insert: impl FnMut(Fingerprint) -> InsertOutcome,
    ) {
        outcomes.clear();
        outcomes.reserve(fingerprint_values.len());
        for &fp in fingerprint_values {
            let outcome = insert(Fingerprint(fp));
            let stop = matches!(&outcome, InsertOutcome::StorageFault(_));
            outcomes.push(outcome);
            if stop {
                break;
            }
        }
    }

    /// Create memory-mapped storage.
    ///
    /// # Arguments
    ///
    /// * `capacity` - Maximum number of fingerprints to store.
    /// * `backing_dir` - Optional directory for the backing file. If None,
    ///   uses anonymous mapping (in-memory, but allows using mmap semantics).
    pub fn mmap(capacity: usize, backing_dir: Option<PathBuf>) -> io::Result<Self> {
        Ok(FingerprintStorage::Mmap(MmapFingerprintSet::new(
            capacity,
            backing_dir,
        )?))
    }

    /// Create disk-backed storage with automatic eviction.
    ///
    /// # Arguments
    ///
    /// * `primary_capacity` - Size of the in-memory primary storage.
    ///   When this fills up, entries are evicted to disk.
    /// * `disk_dir` - Directory for the disk storage file.
    pub fn disk<P: Into<PathBuf>>(primary_capacity: usize, disk_dir: P) -> io::Result<Self> {
        Ok(FingerprintStorage::Disk(DiskFingerprintSet::new(
            primary_capacity,
            disk_dir,
        )?))
    }

    /// Insert a fingerprint with typed outcome.
    pub fn insert_checked(&self, fp: Fingerprint) -> InsertOutcome {
        match self {
            FingerprintStorage::InMemory {
                set,
                max_capacity,
                last_warned_multiple,
            } => {
                let mut guard = set.write();
                if !guard.insert(fp) {
                    return InsertOutcome::AlreadyPresent;
                }
                Self::warn_inmemory_capacity_if_needed(
                    guard.len(),
                    *max_capacity,
                    last_warned_multiple,
                );
                InsertOutcome::Inserted
            }
            FingerprintStorage::Mmap(set) => tla_mc_core::FingerprintSet::insert_checked(set, fp),
            FingerprintStorage::Disk(set) => set.insert_checked(fp),
        }
    }

    /// Insert a batch of fingerprints with typed per-fingerprint outcomes.
    ///
    /// Fault-free batches return one outcome per input fingerprint. If storage
    /// faults, the returned vector includes outcomes through the first
    /// [`InsertOutcome::StorageFault`] and no later suffix fingerprints are
    /// attempted, so compiled BFS cannot miss tracing/enqueuing an admitted
    /// fingerprint.
    pub fn insert_batch_checked(&self, fingerprints: &[Fingerprint]) -> Vec<InsertOutcome> {
        match self {
            FingerprintStorage::InMemory {
                set,
                max_capacity,
                last_warned_multiple,
            } => {
                let mut outcomes = Vec::with_capacity(fingerprints.len());
                let mut inserted_any = false;
                let mut guard = set.write();

                for &fp in fingerprints {
                    if guard.insert(fp) {
                        inserted_any = true;
                        outcomes.push(InsertOutcome::Inserted);
                    } else {
                        outcomes.push(InsertOutcome::AlreadyPresent);
                    }
                }

                if inserted_any {
                    Self::warn_inmemory_capacity_if_needed(
                        guard.len(),
                        *max_capacity,
                        last_warned_multiple,
                    );
                }

                outcomes
            }
            FingerprintStorage::Mmap(set) => {
                Self::insert_batch_prefix_checked(fingerprints, |fp| {
                    tla_mc_core::FingerprintSet::insert_checked(set, fp)
                })
            }
            FingerprintStorage::Disk(set) => {
                Self::insert_batch_prefix_checked(fingerprints, |fp| set.insert_checked(fp))
            }
        }
    }

    /// Insert a batch of raw 64-bit fingerprint values with typed outcomes.
    ///
    /// This mirrors [`Self::insert_batch_checked`] but accepts the compiled
    /// backend's borrowed fingerprint sidecar directly.
    pub fn insert_batch_fingerprint_values_checked(
        &self,
        fingerprint_values: &[u64],
    ) -> Vec<InsertOutcome> {
        let mut outcomes = Vec::with_capacity(fingerprint_values.len());
        self.insert_batch_fingerprint_values_checked_into(fingerprint_values, &mut outcomes);
        outcomes
    }

    /// Insert a batch of raw 64-bit fingerprint values into caller-owned
    /// outcome scratch.
    pub fn insert_batch_fingerprint_values_checked_into(
        &self,
        fingerprint_values: &[u64],
        outcomes: &mut Vec<InsertOutcome>,
    ) {
        match self {
            FingerprintStorage::InMemory {
                set,
                max_capacity,
                last_warned_multiple,
            } => {
                outcomes.clear();
                outcomes.reserve(fingerprint_values.len());
                let mut inserted_any = false;
                let mut guard = set.write();

                for &fp in fingerprint_values {
                    if guard.insert(Fingerprint(fp)) {
                        inserted_any = true;
                        outcomes.push(InsertOutcome::Inserted);
                    } else {
                        outcomes.push(InsertOutcome::AlreadyPresent);
                    }
                }

                if inserted_any {
                    Self::warn_inmemory_capacity_if_needed(
                        guard.len(),
                        *max_capacity,
                        last_warned_multiple,
                    );
                }
            }
            FingerprintStorage::Mmap(set) => {
                set.insert_fingerprint_values_checked_into(fingerprint_values, outcomes);
            }
            FingerprintStorage::Disk(set) => {
                Self::insert_batch_value_prefix_checked_into(fingerprint_values, outcomes, |fp| {
                    set.insert_checked(fp)
                });
            }
        }
    }

    /// Check if a fingerprint is present with typed outcome.
    pub fn contains_checked(&self, fp: Fingerprint) -> LookupOutcome {
        match self {
            FingerprintStorage::InMemory { set, .. } => {
                if set.read().contains(&fp) {
                    LookupOutcome::Present
                } else {
                    LookupOutcome::Absent
                }
            }
            FingerprintStorage::Mmap(set) => tla_mc_core::FingerprintSet::contains_checked(set, fp),
            FingerprintStorage::Disk(set) => set.contains_checked(fp),
        }
    }

    /// Return the number of fingerprints.
    pub fn len(&self) -> usize {
        match self {
            FingerprintStorage::InMemory { set, .. } => set.read().len(),
            FingerprintStorage::Mmap(set) => set.len(),
            FingerprintStorage::Disk(set) => set.len(),
        }
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Check if any insert errors have occurred.
    pub fn has_errors(&self) -> bool {
        match self {
            FingerprintStorage::InMemory { .. } => false,
            FingerprintStorage::Mmap(set) => set.has_errors(),
            FingerprintStorage::Disk(set) => set.has_errors(),
        }
    }

    /// Get the count of dropped fingerprints due to errors.
    pub fn dropped_count(&self) -> usize {
        match self {
            FingerprintStorage::InMemory { .. } => 0,
            FingerprintStorage::Mmap(set) => set.dropped_count(),
            FingerprintStorage::Disk(set) => set.dropped_count(),
        }
    }

    /// Check the current capacity status.
    ///
    /// Part of #4080: InMemory now reports `CapacityStatus::Warning` when the
    /// set exceeds `max_capacity`, enabling the BFS loop's existing
    /// `check_and_warn_capacity` mechanism to surface the condition.
    pub fn capacity_status(&self) -> CapacityStatus {
        match self {
            FingerprintStorage::InMemory {
                set, max_capacity, ..
            } => {
                let count = set.read().len();
                if count >= *max_capacity {
                    CapacityStatus::Warning {
                        count,
                        capacity: *max_capacity,
                        usage: count as f64 / *max_capacity as f64,
                    }
                } else {
                    CapacityStatus::Normal
                }
            }
            FingerprintStorage::Mmap(set) => set.capacity_status(),
            // Disk storage is unlimited (auto-eviction), so always Normal
            FingerprintStorage::Disk(_) => CapacityStatus::Normal,
        }
    }

    /// Return storage counters for the active backend.
    ///
    /// Part of #4080: InMemory now reports `memory_bytes` estimated from
    /// the HashSet's capacity using `estimate_hashmap_bytes` (includes
    /// 15% fragmentation overhead), so memory pressure monitoring can
    /// account for fingerprint storage without relying solely on lagging
    /// RSS measurements.
    pub fn stats(&self) -> StorageStats {
        match self {
            FingerprintStorage::InMemory { set, .. } => {
                let guard = set.read();
                let count = guard.len();
                let capacity = guard.capacity();
                // Use estimate_hashmap_bytes for consistency with run_monitoring.
                // HashSet<Fingerprint> ~ HashMap<Fingerprint, ()>.
                let bytes = crate::memory::estimate_hashmap_bytes::<crate::state::Fingerprint, ()>(
                    capacity,
                );
                StorageStats {
                    memory_count: count,
                    memory_bytes: bytes,
                    ..StorageStats::default()
                }
            }
            FingerprintStorage::Mmap(set) => set.stats(),
            FingerprintStorage::Disk(set) => set.stats(),
        }
    }

    /// Collect all fingerprints from the active backend.
    ///
    /// Part of #2893.
    pub fn collect_fingerprints(&self) -> Result<Vec<Fingerprint>, StorageFault> {
        match self {
            FingerprintStorage::InMemory { set, .. } => Ok(set.read().iter().copied().collect()),
            FingerprintStorage::Mmap(set) => {
                <MmapFingerprintSet as FingerprintSet>::collect_fingerprints(set)
            }
            FingerprintStorage::Disk(set) => {
                <DiskFingerprintSet as FingerprintSet>::collect_fingerprints(set)
            }
        }
    }
}

// --- Core deduplication contract (inherited from tla-mc-core) ---
impl tla_mc_core::FingerprintSet<Fingerprint> for FingerprintStorage {
    fn insert_checked(&self, fp: Fingerprint) -> InsertOutcome {
        FingerprintStorage::insert_checked(self, fp)
    }

    fn contains_checked(&self, fp: Fingerprint) -> LookupOutcome {
        FingerprintStorage::contains_checked(self, fp)
    }

    fn len(&self) -> usize {
        FingerprintStorage::len(self)
    }

    fn has_errors(&self) -> bool {
        FingerprintStorage::has_errors(self)
    }

    fn dropped_count(&self) -> usize {
        FingerprintStorage::dropped_count(self)
    }

    fn capacity_status(&self) -> CapacityStatus {
        FingerprintStorage::capacity_status(self)
    }
}

// --- Model-checking extensions (tla-check FingerprintSet) ---
impl FingerprintSet for FingerprintStorage {
    fn insert_batch_checked(&self, fingerprints: &[Fingerprint]) -> Vec<InsertOutcome> {
        FingerprintStorage::insert_batch_checked(self, fingerprints)
    }

    fn insert_batch_fingerprint_values_checked(
        &self,
        fingerprint_values: &[u64],
    ) -> Vec<InsertOutcome> {
        FingerprintStorage::insert_batch_fingerprint_values_checked(self, fingerprint_values)
    }

    fn insert_batch_fingerprint_values_checked_into(
        &self,
        fingerprint_values: &[u64],
        outcomes: &mut Vec<InsertOutcome>,
    ) {
        FingerprintStorage::insert_batch_fingerprint_values_checked_into(
            self,
            fingerprint_values,
            outcomes,
        )
    }

    fn stats(&self) -> StorageStats {
        FingerprintStorage::stats(self)
    }

    fn prefers_disk_successor_graph(&self) -> bool {
        matches!(self, FingerprintStorage::Disk(_))
    }

    fn fresh_empty_clone(&self) -> Result<std::sync::Arc<dyn FingerprintSet>, StorageFault> {
        match self {
            FingerprintStorage::InMemory {
                set, max_capacity, ..
            } => {
                let capacity = set.read().capacity();
                Ok(std::sync::Arc::new(FingerprintStorage::InMemory {
                    set: parking_lot::RwLock::new(crate::state::fp_hashset_with_capacity(capacity)),
                    max_capacity: *max_capacity,
                    last_warned_multiple: AtomicUsize::new(0),
                }) as std::sync::Arc<dyn FingerprintSet>)
            }
            FingerprintStorage::Mmap(set) => {
                let fresh = set
                    .recreate_empty()
                    .map_err(|e| StorageFault::new("mmap", "fresh_empty_clone", e.to_string()))?;
                Ok(std::sync::Arc::new(FingerprintStorage::Mmap(fresh))
                    as std::sync::Arc<dyn FingerprintSet>)
            }
            FingerprintStorage::Disk(set) => {
                let clone_dir = DiskFingerprintSet::create_fresh_clone_dir(&set.disk_path)
                    .map_err(|e| StorageFault::new("disk", "fresh_empty_clone", e.to_string()))?;
                let fresh = DiskFingerprintSet::new(set.primary.capacity(), clone_dir)
                    .map_err(|e| StorageFault::new("disk", "fresh_empty_clone", e.to_string()))?;
                Ok(std::sync::Arc::new(FingerprintStorage::Disk(fresh))
                    as std::sync::Arc<dyn FingerprintSet>)
            }
        }
    }

    // --- Checkpoint lifecycle delegation (Part of #2656) ---
    //
    // Without these overrides, the default no-ops from the trait are used,
    // which means MmapFingerprintSet::begin_checkpoint (mmap flush) and
    // DiskFingerprintSet::begin_checkpoint (primary flush) are never called
    // when storage is accessed through FingerprintStorage as dyn FingerprintSet.

    fn begin_checkpoint(&self) -> Result<(), StorageFault> {
        match self {
            FingerprintStorage::InMemory { .. } => Ok(()),
            FingerprintStorage::Mmap(set) => {
                <MmapFingerprintSet as FingerprintSet>::begin_checkpoint(set)
            }
            FingerprintStorage::Disk(set) => {
                <DiskFingerprintSet as FingerprintSet>::begin_checkpoint(set)
            }
        }
    }

    fn commit_checkpoint(&self) -> Result<(), StorageFault> {
        match self {
            FingerprintStorage::InMemory { .. } => Ok(()),
            FingerprintStorage::Mmap(set) => {
                <MmapFingerprintSet as FingerprintSet>::commit_checkpoint(set)
            }
            FingerprintStorage::Disk(set) => {
                <DiskFingerprintSet as FingerprintSet>::commit_checkpoint(set)
            }
        }
    }

    fn recover_checkpoint(&self) -> Result<(), StorageFault> {
        match self {
            FingerprintStorage::InMemory { .. } => Ok(()),
            FingerprintStorage::Mmap(set) => {
                <MmapFingerprintSet as FingerprintSet>::recover_checkpoint(set)
            }
            FingerprintStorage::Disk(set) => {
                <DiskFingerprintSet as FingerprintSet>::recover_checkpoint(set)
            }
        }
    }

    fn collect_fingerprints(&self) -> Result<Vec<Fingerprint>, StorageFault> {
        FingerprintStorage::collect_fingerprints(self)
    }
}

#[cfg(test)]
#[path = "storage_tests/mod.rs"]
mod tests;
