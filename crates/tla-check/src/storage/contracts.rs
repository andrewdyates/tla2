// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::state::Fingerprint;

// --- Consolidated storage types from tla-mc-core (Part of #3716) ---
pub use tla_mc_core::{CapacityStatus, InsertOutcome, LookupOutcome, StorageFault};

/// Storage performance counters exposed through [`FingerprintSet`].
///
/// This is a minimal trait-level subset of TLC's `FPSetStatistic` surface:
/// enough to report memory residency, disk traffic, and eviction pressure
/// regardless of the concrete backend behind `dyn FingerprintSet`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct StorageStats {
    /// Fingerprints currently resident in the in-memory tier.
    pub memory_count: usize,
    /// Fingerprints persisted to the disk tier.
    pub disk_count: usize,
    /// Disk-backed lookup operations performed.
    pub disk_lookups: usize,
    /// Disk-backed lookups that found a matching fingerprint.
    pub disk_hits: usize,
    /// Number of evictions from memory to disk.
    pub eviction_count: usize,
    /// Bytes reserved by the in-memory storage tier.
    pub memory_bytes: usize,
}

impl StorageStats {
    pub(crate) fn accumulate(&mut self, other: Self) {
        self.memory_count = self.memory_count.saturating_add(other.memory_count);
        self.disk_count = self.disk_count.saturating_add(other.disk_count);
        self.disk_lookups = self.disk_lookups.saturating_add(other.disk_lookups);
        self.disk_hits = self.disk_hits.saturating_add(other.disk_hits);
        self.eviction_count = self.eviction_count.saturating_add(other.eviction_count);
        self.memory_bytes = self.memory_bytes.saturating_add(other.memory_bytes);
    }
}

/// Model-checking extension trait for fingerprint sets.
///
/// Extends the generic [`tla_mc_core::FingerprintSet`] contract with
/// model-checking-specific capabilities: richer storage statistics
/// (disk tier counters), checkpoint lifecycle, and storage invariant
/// verification. The core deduplication methods (`insert_checked`,
/// `contains_checked`, `len`, `is_empty`, `has_errors`, `dropped_count`,
/// `capacity_status`) are inherited from the supertrait.
///
/// All extension methods have default implementations, so in-memory
/// backends that only need the core contract can implement the mc-core
/// trait and provide an empty `impl FingerprintSet for T {}`.
pub trait FingerprintSet: tla_mc_core::FingerprintSet<Fingerprint> {
    /// Return backend storage counters for observability.
    ///
    /// Returns the richer [`StorageStats`] (with disk-tier counters) used by
    /// the model checker's monitoring and checkpoint subsystems.
    ///
    /// Default implementation returns zeroed counters for backends that do not
    /// track storage-specific metrics.
    fn stats(&self) -> StorageStats {
        StorageStats::default()
    }

    /// Whether liveness successor caching should prefer the disk-backed graph.
    ///
    /// Backends that already rely on disk tiers for large-state exploration can
    /// request the bounded-memory successor graph so liveness caching does not
    /// reintroduce an unbounded in-memory map on that same path.
    fn prefers_disk_successor_graph(&self) -> bool {
        false
    }

    // --- Checkpoint lifecycle (Part of #2656) ---
    //
    // TLC's FPSet enforces beginChkpt/commitChkpt/recover at the type level.
    // These methods bring TLA2's FingerprintSet to parity, ensuring future
    // backends (e.g., ShardedDiskFPSet from #2568) are forced by the type
    // system to consider checkpoint support.
    //
    // Default no-op implementations mean in-memory backends (DashSet,
    // FxHashSet, ShardedFingerprintSet) work without changes.

    /// Prepare for checkpoint serialization.
    ///
    /// Called before the checkpoint module extracts fingerprints. Backends
    /// that buffer writes (mmap, disk) should flush to durable storage here.
    ///
    /// Mirrors TLC's `FPSet.beginChkpt()`.
    fn begin_checkpoint(&self) -> Result<(), StorageFault> {
        Ok(())
    }

    /// Finalize a checkpoint after data has been written.
    ///
    /// Called after the checkpoint module has successfully serialized all
    /// fingerprints. Backends may use this to perform atomic rename or
    /// cleanup of temporary files.
    ///
    /// Mirrors TLC's `FPSet.commitChkpt()`.
    fn commit_checkpoint(&self) -> Result<(), StorageFault> {
        Ok(())
    }

    /// Restore backend state after fingerprints have been replayed.
    ///
    /// Called after `insert_checked` has been called for each fingerprint
    /// from the checkpoint. Backends may use this to rebuild indexes or
    /// finalize recovery.
    ///
    /// Mirrors TLC's `FPSet.recover()`.
    fn recover_checkpoint(&self) -> Result<(), StorageFault> {
        Ok(())
    }

    /// Collect all fingerprints currently stored in this set.
    ///
    /// Returns all fingerprints across all tiers (memory, disk) in an
    /// unspecified order. Used by checkpoint to serialize the full state.
    ///
    /// Default implementation returns an error — backends must override this
    /// if they participate in checkpoint workflows.
    ///
    /// Part of #2893.
    fn collect_fingerprints(&self) -> Result<Vec<Fingerprint>, StorageFault> {
        Err(StorageFault::new(
            "default",
            "collect_fingerprints",
            "not implemented for this backend",
        ))
    }

    /// Verify internal consistency of storage state.
    ///
    /// Returns `Ok(true)` if all invariants hold, `Ok(false)` if a violation
    /// is detected (with details logged to stderr), or `Err` on I/O failure.
    ///
    /// TLC reference: `FPSetStatistic.checkInvariant()`, `FPSet.checkFPs()`.
    ///
    /// Part of #2664.
    fn check_invariant(&self) -> Result<bool, StorageFault> {
        Ok(true)
    }
}
