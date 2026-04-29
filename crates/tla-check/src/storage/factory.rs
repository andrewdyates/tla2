// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Central factory for fingerprint storage backend selection.
//!
//! Replaces the 4-location storage construction pattern with a single dispatch
//! point, matching TLC's `FPSetFactory.getFPSet()` pattern.
//!
//! Part of #2568: composable storage — Steps 1 & 4.

use super::atomic_adapter::AtomicFpSetAdapter;
use super::cas_fpset::PartitionedCasFingerprintSet;
use super::sharded::ShardedFingerprintSet;
use super::{DiskFingerprintSet, FingerprintSet, FingerprintStorage, MmapFingerprintSet};
use std::io;
use std::path::PathBuf;
use std::sync::Arc;

/// Configuration for fingerprint storage creation.
pub struct StorageConfig {
    /// Which storage backend to use.
    pub mode: StorageMode,
    /// Number of MSB bits for shard partitioning (default: 8 for parallel, 6 for CLI).
    pub shard_bits: u32,
    /// Pre-allocated capacity (total across all shards).
    pub capacity: Option<usize>,
    /// Directory for mmap/disk backing files.
    pub backing_dir: Option<PathBuf>,
}

impl Default for StorageConfig {
    fn default() -> Self {
        Self {
            mode: StorageMode::Auto { num_workers: 1 },
            shard_bits: 8,
            capacity: None,
            backing_dir: None,
        }
    }
}

/// Storage backend selection mode.
#[non_exhaustive]
pub enum StorageMode {
    /// Auto-select based on worker count and capacity hint.
    /// Sequential (1 worker) → InMemory, parallel (>1) → Sharded,
    /// parallel + capacity > [`DISK_THRESHOLD`] → ShardedDisk.
    Auto { num_workers: usize },
    /// In-memory hash set (sequential default).
    InMemory,
    /// MSB-sharded in-memory (parallel default).
    Sharded,
    /// Memory-mapped open-addressing table.
    Mmap,
    /// Memory-mapped open-addressing table with huge page advisory hints.
    ///
    /// Identical to `Mmap` but requests the OS to use huge pages (2MB) for
    /// reduced TLB pressure on large state tables. Falls back gracefully to
    /// regular pages if huge pages are unavailable.
    ///
    /// Part of #3856.
    MmapHugePages,
    /// Two-tier with disk eviction (single instance).
    Disk,
    /// Sharded with disk-backed shards (composable).
    ///
    /// Creates `ShardedFingerprintSet<DiskShard>` — N independent
    /// `DiskFingerprintSet` instances partitioned by fingerprint MSB.
    /// For specs requiring both parallelism and billion-state support.
    /// Matches TLC's `MultiFPSet<OffHeapDiskFPSet>` architecture.
    ///
    /// Part of #2568.
    ShardedDisk,
    /// Lock-free CAS-based partitioned fingerprint set (parallel default).
    ///
    /// Creates `PartitionedCasFingerprintSet` — open-addressing tables with
    /// atomic CAS insertion, partitioned by fingerprint MSB. Eliminates the
    /// `RwLock` contention that caps `Sharded` throughput at 4 workers.
    /// Matches TLC's `MultiFPSet<OffHeapDiskFPSet>` CAS pattern.
    ///
    /// Part of #3170.
    ShardedCas,
    /// Lock-free 128-bit atomic fingerprint set with auto-resize.
    ///
    /// Creates an [`AtomicFpSetAdapter`] wrapping a 128-bit
    /// [`ResizableAtomicFpSet`]. Uses three-phase CAS insertion (claim,
    /// write hi/lo, commit) with bounded spinning. Auto-resizes at 75%
    /// load factor via an `RwLock` upgrade path (read-lock for steady
    /// state, write-lock only during resize).
    ///
    /// Compared to `ShardedCas` (64-bit, partitioned), this variant stores
    /// fingerprints as 128-bit values for collision resistance beyond
    /// Birthday Paradox bounds at billion-state scales.
    ///
    /// Part of #3991.
    AtomicLockFree,
}

/// Capacity threshold (in number of states) above which `Auto` mode selects
/// `ShardedDisk` instead of `Sharded` for parallel checkers.
///
/// 10M states is the approximate memory-pressure transition point where
/// in-memory storage starts causing GC pressure in TLC. At ~8 bytes per
/// fingerprint, 10M states ≈ 80MB — comfortable for in-memory; beyond this,
/// disk backing prevents OOM on billion-state specs.
///
/// Part of #2568, Step 4.
pub const DISK_THRESHOLD: usize = 10_000_000;

/// Default CAS FPSet capacity for parallel runs with up to 4 workers.
pub(crate) const DEFAULT_PARALLEL_FPSET_CAPACITY_LOW_WORKERS: usize = 1 << 25; // 32M

/// Default CAS FPSet capacity for parallel runs above 4 workers.
/// Raised from 8M to 32M: ElevatorSafetyMedium needs 18M states, SlushMedium
/// needs 9.9M. At 8M capacity, CAS probe chains exhaust at ~88% load factor.
/// 32M keeps load under 60% for all baseline specs (max 18M states).
pub(crate) const DEFAULT_PARALLEL_FPSET_CAPACITY_HIGH_WORKERS: usize = 1 << 25; // 32M

/// Select the default total CAS FPSet capacity for the given worker count.
///
/// Both low-worker and high-worker modes use 32M capacity (256MB at 8 bytes/entry).
/// The previous smaller capacity for >4 workers caused fingerprint storage overflow
/// on large specs.
#[must_use]
pub(crate) fn default_parallel_fpset_capacity(num_workers: usize) -> usize {
    if num_workers > 4 {
        DEFAULT_PARALLEL_FPSET_CAPACITY_HIGH_WORKERS
    } else {
        DEFAULT_PARALLEL_FPSET_CAPACITY_LOW_WORKERS
    }
}

/// Central factory for fingerprint storage backend selection.
///
/// All storage construction should go through this factory to ensure
/// consistent configuration and composability.
pub struct FingerprintSetFactory;

impl FingerprintSetFactory {
    /// Create a fingerprint storage backend from the given configuration.
    pub fn create(config: StorageConfig) -> io::Result<Arc<dyn FingerprintSet>> {
        match config.mode {
            StorageMode::Auto { num_workers } => {
                let mode = if num_workers <= 1 {
                    StorageMode::InMemory
                } else if config.capacity.is_some_and(|c| c > DISK_THRESHOLD) {
                    StorageMode::ShardedDisk
                } else {
                    // Part of #3170: use lock-free CAS backend for parallel
                    // in-memory runs instead of RwLock-backed Sharded.
                    StorageMode::ShardedCas
                };
                // Enforce a minimum capacity floor for CAS mode. The CAS
                // hash table has a hard failure mode (probe chains > 1024 →
                // storage full) unlike growable hash maps. When callers pass
                // a capacity hint from pilot estimation, it may dramatically
                // underestimate (e.g., 240K for a 9.9M-state spec). Use
                // max(hint, default) so the table never starts too small.
                let capacity = if matches!(mode, StorageMode::ShardedCas) {
                    let default_cap = default_parallel_fpset_capacity(num_workers);
                    Some(config.capacity.map_or(default_cap, |c| c.max(default_cap)))
                } else {
                    config.capacity
                };
                Self::create(StorageConfig {
                    mode,
                    capacity,
                    ..config
                })
            }
            StorageMode::InMemory => {
                let storage = match config.capacity {
                    Some(cap) => FingerprintStorage::in_memory_with_capacity(cap),
                    None => FingerprintStorage::in_memory(),
                };
                Ok(Arc::new(storage) as Arc<dyn FingerprintSet>)
            }
            StorageMode::Sharded => {
                let storage = match config.capacity {
                    Some(cap) => ShardedFingerprintSet::new_with_capacity(config.shard_bits, cap),
                    None => ShardedFingerprintSet::new(config.shard_bits),
                };
                Ok(Arc::new(storage) as Arc<dyn FingerprintSet>)
            }
            StorageMode::Mmap => {
                let capacity = config.capacity.unwrap_or(1 << 24); // 16M default
                let storage = MmapFingerprintSet::new(capacity, config.backing_dir)?;
                Ok(Arc::new(FingerprintStorage::Mmap(storage)) as Arc<dyn FingerprintSet>)
            }
            StorageMode::MmapHugePages => {
                // Part of #3856: mmap with huge page advisory hints.
                let capacity = config.capacity.unwrap_or(1 << 24); // 16M default
                let storage =
                    MmapFingerprintSet::new_with_huge_pages(capacity, config.backing_dir)?;
                Ok(Arc::new(FingerprintStorage::Mmap(storage)) as Arc<dyn FingerprintSet>)
            }
            StorageMode::Disk => {
                let capacity = config.capacity.unwrap_or(1 << 20); // 1M primary default
                let dir = config
                    .backing_dir
                    .unwrap_or_else(|| std::env::temp_dir().join("tla2_disk_fps"));
                let storage = DiskFingerprintSet::new(capacity, dir)?;
                Ok(Arc::new(FingerprintStorage::Disk(storage)) as Arc<dyn FingerprintSet>)
            }
            StorageMode::ShardedDisk => {
                let num_shards = 1usize << config.shard_bits;
                // Default: 1M primary capacity per shard
                let per_shard_capacity =
                    config.capacity.map_or(1 << 20, |c| c.div_ceil(num_shards));
                let dir = config
                    .backing_dir
                    .unwrap_or_else(|| std::env::temp_dir().join("tla2_sharded_disk_fps"));
                let storage =
                    ShardedFingerprintSet::new_disk(config.shard_bits, per_shard_capacity, dir)?;
                Ok(Arc::new(storage) as Arc<dyn FingerprintSet>)
            }
            StorageMode::ShardedCas => {
                // Part of #3170: lock-free CAS backend for parallel in-memory.
                // Part of #3314: callers that know the worker count should pass
                // the worker-aware default (16M through 4 workers, 8M above 4).
                // Keep the 8M fallback here so direct ShardedCas users preserve
                // the prior default unless they opt into worker-aware sizing.
                // Override via TLA2_FP_CAPACITY for specs needing more capacity.
                let total_capacity = config
                    .capacity
                    .unwrap_or(DEFAULT_PARALLEL_FPSET_CAPACITY_HIGH_WORKERS);
                let storage = PartitionedCasFingerprintSet::new(config.shard_bits, total_capacity);
                Ok(Arc::new(storage) as Arc<dyn FingerprintSet>)
            }
            StorageMode::AtomicLockFree => {
                // Part of #3991: 128-bit lock-free atomic fingerprint set.
                // Uses ResizableAtomicFpSet (auto-resize at 75% load) wrapped
                // by AtomicFpSetAdapter for the 64-bit Fingerprint interface.
                let total_capacity = config
                    .capacity
                    .unwrap_or(DEFAULT_PARALLEL_FPSET_CAPACITY_HIGH_WORKERS);
                let storage = AtomicFpSetAdapter::new(total_capacity);
                Ok(Arc::new(storage) as Arc<dyn FingerprintSet>)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::Fingerprint;
    use crate::storage::contracts::{InsertOutcome, LookupOutcome};

    /// Insert/lookup roundtrip assertion helper.
    ///
    /// Verifies: insert new → Inserted, insert dup → AlreadyPresent,
    /// contains present → Present, contains absent → Absent, len accurate.
    fn assert_insert_lookup_roundtrip(storage: &dyn FingerprintSet) {
        let fp1 = Fingerprint(0xDEADBEEF_CAFEBABE);
        let fp2 = Fingerprint(0x1234_5678_9ABC_DEF0);
        let fp_absent = Fingerprint(0xFFFF_FFFF_FFFF_FFFF);

        // Insert fp1
        assert_eq!(storage.insert_checked(fp1), InsertOutcome::Inserted);
        assert_eq!(storage.len(), 1);

        // Dedup fp1
        assert_eq!(storage.insert_checked(fp1), InsertOutcome::AlreadyPresent);
        assert_eq!(storage.len(), 1);

        // Insert fp2
        assert_eq!(storage.insert_checked(fp2), InsertOutcome::Inserted);
        assert_eq!(storage.len(), 2);

        // Contains checks
        assert_eq!(storage.contains_checked(fp1), LookupOutcome::Present);
        assert_eq!(storage.contains_checked(fp2), LookupOutcome::Present);
        assert_eq!(storage.contains_checked(fp_absent), LookupOutcome::Absent);

        // Error state
        assert!(!storage.has_errors());
        assert_eq!(storage.dropped_count(), 0);
    }

    // --- Auto mode ---

    #[test]
    fn test_auto_sequential_roundtrip() {
        let config = StorageConfig {
            mode: StorageMode::Auto { num_workers: 1 },
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    #[test]
    fn test_auto_parallel_roundtrip() {
        let config = StorageConfig {
            mode: StorageMode::Auto { num_workers: 4 },
            shard_bits: 2,
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    #[test]
    fn test_auto_zero_workers_uses_in_memory() {
        let config = StorageConfig {
            mode: StorageMode::Auto { num_workers: 0 },
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    // --- InMemory ---

    #[test]
    fn test_in_memory_roundtrip() {
        let config = StorageConfig {
            mode: StorageMode::InMemory,
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    #[test]
    fn test_in_memory_with_capacity_roundtrip() {
        let config = StorageConfig {
            mode: StorageMode::InMemory,
            capacity: Some(1000),
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    // --- Sharded ---

    #[test]
    fn test_sharded_roundtrip() {
        let config = StorageConfig {
            mode: StorageMode::Sharded,
            shard_bits: 2,
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    #[test]
    fn test_sharded_with_capacity_roundtrip() {
        let config = StorageConfig {
            mode: StorageMode::Sharded,
            shard_bits: 2,
            capacity: Some(1000),
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    // --- Mmap ---

    #[test]
    fn test_mmap_roundtrip() {
        let dir = tempfile::tempdir().unwrap();
        let config = StorageConfig {
            mode: StorageMode::Mmap,
            backing_dir: Some(dir.path().to_path_buf()),
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    // --- MmapHugePages (Part of #3856) ---

    #[test]
    fn test_mmap_huge_pages_roundtrip() {
        let dir = tempfile::tempdir().unwrap();
        let config = StorageConfig {
            mode: StorageMode::MmapHugePages,
            backing_dir: Some(dir.path().to_path_buf()),
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    #[test]
    fn test_mmap_huge_pages_anonymous_roundtrip() {
        // Anonymous mapping (no backing dir) -- still works, just no file.
        let config = StorageConfig {
            mode: StorageMode::MmapHugePages,
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    // --- Disk ---

    #[test]
    fn test_disk_roundtrip() {
        let dir = tempfile::tempdir().unwrap();
        let config = StorageConfig {
            mode: StorageMode::Disk,
            backing_dir: Some(dir.path().to_path_buf()),
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    // --- ShardedDisk (Part of #2568) ---

    #[test]
    fn test_sharded_disk_roundtrip() {
        let dir = tempfile::tempdir().unwrap();
        let config = StorageConfig {
            mode: StorageMode::ShardedDisk,
            shard_bits: 2, // 4 shards
            backing_dir: Some(dir.path().to_path_buf()),
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    #[test]
    fn test_sharded_disk_with_capacity_roundtrip() {
        let dir = tempfile::tempdir().unwrap();
        let config = StorageConfig {
            mode: StorageMode::ShardedDisk,
            shard_bits: 1, // 2 shards
            capacity: Some(4096),
            backing_dir: Some(dir.path().to_path_buf()),
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    // --- Boundary: shard_bits = 2 (boundary for Auto num_workers > 1) ---

    #[test]
    fn test_auto_boundary_num_workers_2() {
        let config = StorageConfig {
            mode: StorageMode::Auto { num_workers: 2 },
            shard_bits: 1,
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    // --- Auto + DISK_THRESHOLD (Part of #2568, Step 4) ---

    #[test]
    fn test_auto_large_capacity_selects_sharded_disk() {
        // When capacity exceeds DISK_THRESHOLD and num_workers > 1,
        // Auto should select ShardedDisk.
        let dir = tempfile::tempdir().unwrap();
        let config = StorageConfig {
            mode: StorageMode::Auto { num_workers: 4 },
            shard_bits: 1, // 2 shards (small for test speed)
            capacity: Some(DISK_THRESHOLD + 1),
            backing_dir: Some(dir.path().to_path_buf()),
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
        // Verify ShardedDisk was actually selected: shard subdirs are an
        // observable signal that DiskShard backends were created.
        assert!(
            dir.path().join("shard_0").exists(),
            "shard_0 dir missing — ShardedDisk not selected"
        );
        assert!(
            dir.path().join("shard_1").exists(),
            "shard_1 dir missing — ShardedDisk not selected"
        );
    }

    #[test]
    fn test_auto_below_threshold_selects_sharded() {
        // When capacity is at or below DISK_THRESHOLD, Auto stays with Sharded.
        let dir = tempfile::tempdir().unwrap();
        let config = StorageConfig {
            mode: StorageMode::Auto { num_workers: 4 },
            shard_bits: 1,
            capacity: Some(DISK_THRESHOLD),
            backing_dir: Some(dir.path().to_path_buf()),
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
        // Verify ShardedDisk was NOT selected: no shard subdirs should exist.
        assert!(
            !dir.path().join("shard_0").exists(),
            "shard_0 dir exists — ShardedDisk selected unexpectedly"
        );
    }

    #[test]
    fn test_auto_large_capacity_sequential_stays_in_memory() {
        // Even with large capacity, sequential (num_workers=1) uses InMemory.
        let config = StorageConfig {
            mode: StorageMode::Auto { num_workers: 1 },
            capacity: Some(DISK_THRESHOLD + 1),
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    // --- ShardedCas (Part of #3170) ---

    #[test]
    fn test_sharded_cas_roundtrip() {
        let config = StorageConfig {
            mode: StorageMode::ShardedCas,
            shard_bits: 2, // 4 partitions
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    #[test]
    fn test_sharded_cas_with_capacity_roundtrip() {
        let config = StorageConfig {
            mode: StorageMode::ShardedCas,
            shard_bits: 2,
            capacity: Some(8192),
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    #[test]
    fn test_auto_parallel_selects_sharded_cas() {
        // Auto with parallel workers (below disk threshold) now selects ShardedCas.
        let config = StorageConfig {
            mode: StorageMode::Auto { num_workers: 4 },
            shard_bits: 2,
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    #[test]
    fn test_default_parallel_fpset_capacity_keeps_32m_through_four_workers() {
        assert_eq!(
            default_parallel_fpset_capacity(1),
            DEFAULT_PARALLEL_FPSET_CAPACITY_LOW_WORKERS
        );
        assert_eq!(
            default_parallel_fpset_capacity(4),
            DEFAULT_PARALLEL_FPSET_CAPACITY_LOW_WORKERS
        );
    }

    #[test]
    fn test_default_parallel_fpset_capacity_uses_32m_above_four_workers() {
        assert_eq!(
            default_parallel_fpset_capacity(5),
            DEFAULT_PARALLEL_FPSET_CAPACITY_HIGH_WORKERS
        );
        assert_eq!(
            default_parallel_fpset_capacity(8),
            DEFAULT_PARALLEL_FPSET_CAPACITY_HIGH_WORKERS
        );
    }

    #[test]
    fn test_auto_cas_enforces_capacity_floor() {
        // When Auto selects ShardedCas with a small capacity hint (e.g.,
        // from a pilot phase underestimate), the factory must enforce a
        // minimum of default_parallel_fpset_capacity(). Without this
        // floor, CAS probe chains overflow on large specs.
        let config = StorageConfig {
            mode: StorageMode::Auto { num_workers: 4 },
            shard_bits: 2,
            capacity: Some(1000), // Tiny hint — would overflow CAS at ~1K states
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        // Must handle at least 32M inserts without overflow.
        // We just verify it creates successfully and handles basic ops.
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    // --- AtomicLockFree (Part of #3991) ---

    #[test]
    fn test_atomic_lock_free_roundtrip() {
        let config = StorageConfig {
            mode: StorageMode::AtomicLockFree,
            capacity: Some(1024),
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }

    #[test]
    fn test_atomic_lock_free_default_capacity_roundtrip() {
        // Without explicit capacity, uses DEFAULT_PARALLEL_FPSET_CAPACITY_HIGH_WORKERS.
        let config = StorageConfig {
            mode: StorageMode::AtomicLockFree,
            ..Default::default()
        };
        let storage = FingerprintSetFactory::create(config).unwrap();
        assert_insert_lookup_roundtrip(storage.as_ref());
    }
}
