// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
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
    ActionBitmaskLookup, ActionBitmaskMap, StateBitmaskLookup, StateBitmaskMap,
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
use crate::state::{BuildFingerprintHasher, Fingerprint, FpHashSet};
use std::io;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};

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
    /// warning is logged once (guarded by `warned`) and `capacity_status()`
    /// returns `CapacityStatus::Warning` so the BFS loop can react.
    ///
    /// Part of #4080: OOM safety — InMemory capacity guard.
    InMemory {
        set: parking_lot::RwLock<FpHashSet>,
        max_capacity: usize,
        warned: AtomicBool,
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
            warned: AtomicBool::new(false),
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
            warned: AtomicBool::new(false),
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
                warned,
            } => {
                let mut guard = set.write();
                if !guard.insert(fp) {
                    return InsertOutcome::AlreadyPresent;
                }
                // Part of #4080: warn once when in-memory set exceeds capacity.
                let count = guard.len();
                if count >= *max_capacity
                    && !warned.swap(true, AtomicOrdering::Relaxed)
                {
                    eprintln!(
                        "Warning: in-memory fingerprint storage exceeded {} entries \
                         ({} states). Consider using --workers 2 to enable sharded \
                         disk-backed storage, or set TLA2_INMEMORY_FP_MAX to raise \
                         this limit.",
                        max_capacity, count
                    );
                }
                InsertOutcome::Inserted
            }
            FingerprintStorage::Mmap(set) => tla_mc_core::FingerprintSet::insert_checked(set, fp),
            FingerprintStorage::Disk(set) => set.insert_checked(fp),
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
                let bytes = crate::memory::estimate_hashmap_bytes::<
                    crate::state::Fingerprint,
                    (),
                >(capacity);
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
            FingerprintStorage::InMemory { set, .. } => {
                Ok(set.read().iter().copied().collect())
            }
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
    fn stats(&self) -> StorageStats {
        FingerprintStorage::stats(self)
    }

    fn prefers_disk_successor_graph(&self) -> bool {
        matches!(self, FingerprintStorage::Disk(_))
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
