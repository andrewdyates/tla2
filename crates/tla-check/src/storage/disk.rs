// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Two-tier disk-backed fingerprint storage for billion-state model checking.
//!
//! [`DiskFingerprintSet`] implements TLC's DiskFPSet pattern: an in-memory
//! primary tier ([`MmapFingerprintSet`]) with automatic eviction to a sorted
//! disk file. Lookups use a page index for interpolated search on disk.

use crate::state::Fingerprint;
use std::io;
use std::path::{Path, PathBuf};
#[cfg(test)]
use std::sync::atomic::AtomicBool;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

use super::contracts::{
    CapacityStatus, FingerprintSet, InsertOutcome, LookupOutcome, StorageFault, StorageStats,
};
pub(crate) use super::disk_eviction::EvictionBarrier;
#[cfg(test)]
pub(crate) use super::disk_eviction::{
    read_next_fp, EvictGuard, EvictionState, EVICTION_STATUS_FAILURE, EVICTION_STATUS_SUCCESS,
};
use super::disk_lookup::DiskLookupPool;
use super::mmap::MmapFingerprintSet;
use super::open_addressing::MmapError;

// ============================================================================
// DiskFingerprintSet
// ============================================================================

/// Disk-backed fingerprint set for billion-state model checking.
///
/// This implements the two-tier storage pattern from TLC's DiskFPSet:
/// - Primary: In-memory storage (MmapFingerprintSet or similar)
/// - Secondary: Sorted disk file with page index for interpolated search
///
/// When the primary storage fills up, fingerprints are evicted to disk
/// in sorted order. Lookups check both primary and secondary storage.
///
/// # Algorithm
///
/// **Insert (`put`):**
/// 1. Try to insert into primary storage
/// 2. If primary is full, trigger eviction
/// 3. Eviction: collect all primary FPs, sort, merge with disk, write new file
/// 4. Retry insert after eviction
///
/// **Lookup (`contains`):**
/// 1. Check primary storage
/// 2. If not found and disk file exists, do interpolated search on disk
///
/// # Thread Safety
///
/// The implementation supports concurrent reads and writes:
/// - Primary storage handles its own concurrency
/// - Disk reads are lock-free (immutable sorted file)
/// - Eviction uses a flag to coordinate pausing workers
///
/// # Example
///
/// ```rust,ignore
/// # fn main() -> std::io::Result<()> {
/// use tla_check::DiskFingerprintSet;
/// use tla_check::Fingerprint;
///
/// let set = DiskFingerprintSet::new(1_000_000, "/tmp/fp_storage")?;
/// set.insert(Fingerprint(12345));
/// assert!(set.contains(Fingerprint(12345)));
/// # Ok(())
/// # }
/// ```
pub struct DiskFingerprintSet {
    /// Primary: in-memory storage with fixed capacity.
    pub(super) primary: MmapFingerprintSet,

    /// Secondary: sorted disk file (None until first eviction).
    pub(super) disk_path: PathBuf,

    /// Page index: first fingerprint of each disk page for interpolated search.
    /// If empty, no disk file exists yet.
    pub(crate) page_index: parking_lot::RwLock<Vec<u64>>,

    /// Number of fingerprints stored on disk.
    pub(crate) disk_count: AtomicUsize,

    /// Eviction coordination barrier: Condvar-based blocking replaces busy-spin.
    /// Workers that discover eviction in progress park on the condvar instead of
    /// calling `thread::yield_now()`. Part of #2494.
    pub(crate) eviction_barrier: EvictionBarrier,

    /// Coordination barrier: workers hold a read lock for primary access,
    /// eviction holds a write lock for the primary mutation phase.
    /// This ensures eviction never mutates the primary concurrently with
    /// `insert()`/`contains()`. Fix for #1423.
    pub(crate) primary_barrier: parking_lot::RwLock<()>,

    /// Pooled disk lookup sessions: persistent file handles + reusable page
    /// buffers. Eliminates per-lookup File::open + metadata + Vec alloc.
    /// Part of #2371 (S1).
    pub(super) disk_reader_pool: DiskLookupPool,

    /// Cached disk file length (bytes). Updated after each eviction publish.
    /// Readers use this instead of per-lookup `metadata()` syscalls.
    /// Part of #2371 (S1).
    pub(crate) disk_file_len: AtomicU64,

    /// Total count (primary + disk).
    total_count: AtomicUsize,

    /// Statistics: number of evictions performed.
    pub(super) eviction_count: AtomicUsize,

    /// Statistics: number of disk lookups.
    pub(super) disk_lookups: AtomicUsize,

    /// Statistics: number of disk hits.
    pub(super) disk_hits: AtomicUsize,
    /// Number of disk lookup I/O failures.
    pub(super) disk_error_count: AtomicUsize,
    /// Test-only fault injection for eviction publish failures.
    #[cfg(test)]
    pub(crate) fail_next_publish: AtomicBool,
}

// ============================================================================
// impl DiskFingerprintSet
// ============================================================================

impl DiskFingerprintSet {
    pub(crate) fn create_fresh_clone_dir(existing_disk_path: &Path) -> io::Result<PathBuf> {
        let disk_dir = existing_disk_path.parent().ok_or_else(|| {
            io::Error::other(format!(
                "disk storage path {} has no parent directory",
                existing_disk_path.display()
            ))
        })?;

        static FRESH_CLONE_COUNTER: AtomicU64 = AtomicU64::new(0);
        for _ in 0..64 {
            let nonce = FRESH_CLONE_COUNTER.fetch_add(1, Ordering::Relaxed);
            let clone_dir =
                disk_dir.join(format!(".fresh-empty-clone-{}-{nonce}", std::process::id()));
            match std::fs::create_dir(&clone_dir) {
                Ok(()) => return Ok(clone_dir),
                Err(err) if err.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(err) => return Err(err),
            }
        }

        Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            format!(
                "failed to allocate an isolated fresh-clone directory under {}",
                disk_dir.display()
            ),
        ))
    }

    /// Create a new disk-backed fingerprint set.
    ///
    /// # Arguments
    ///
    /// * `primary_capacity` - Capacity of the in-memory primary storage.
    /// * `disk_dir` - Directory for the disk file.
    ///
    /// # Returns
    ///
    /// The new set, or an I/O error if initialization fails.
    pub fn new(primary_capacity: usize, disk_dir: impl Into<PathBuf>) -> io::Result<Self> {
        let disk_dir = disk_dir.into();
        std::fs::create_dir_all(&disk_dir)?;

        let disk_path = disk_dir.join("fingerprints.fp");

        // Use file-backed mmap for primary (allows OS paging)
        let primary = MmapFingerprintSet::new(primary_capacity, Some(disk_dir.clone()))?;

        Ok(DiskFingerprintSet {
            disk_reader_pool: DiskLookupPool::new(disk_path.clone()),
            disk_file_len: AtomicU64::new(0),
            primary,
            disk_path,
            page_index: parking_lot::RwLock::new(Vec::new()),
            disk_count: AtomicUsize::new(0),
            eviction_barrier: EvictionBarrier::new(),
            primary_barrier: parking_lot::RwLock::new(()),
            total_count: AtomicUsize::new(0),
            eviction_count: AtomicUsize::new(0),
            disk_lookups: AtomicUsize::new(0),
            disk_hits: AtomicUsize::new(0),
            disk_error_count: AtomicUsize::new(0),
            #[cfg(test)]
            fail_next_publish: AtomicBool::new(false),
        })
    }

    /// Insert a fingerprint with typed outcome.
    ///
    /// Unbounded retry for contention (primary full → evict → retry), matching
    /// TLC's `OffHeapDiskFPSet.memInsert0()` which recursively calls `put(fp0)`
    /// after `forceFlush()` with no retry limit. Only real disk I/O errors
    /// (from eviction) or probe exhaustion break out immediately.
    ///
    /// Fix for #2820: the previous bounded retry (MAX_EVICTION_RETRIES=3, added
    /// in #1760) conflated contention with disk failure, causing silent
    /// fingerprint loss under multi-threaded contention.
    pub fn insert_checked(&self, fp: Fingerprint) -> InsertOutcome {
        loop {
            // Hold read lock while accessing primary to prevent concurrent clear().
            // Fix for #1423: clear() requires exclusive access.
            {
                let _guard = self.primary_barrier.read();

                // Fast path: check primary first (O(1) mmap probe, no disk I/O).
                // Matches TLC's memLookup → diskLookup → memInsert order.
                // Part of #2666.
                if self.primary.contains(fp) {
                    return InsertOutcome::AlreadyPresent;
                }

                // Not in primary — probe disk overflow.
                match self.disk_lookup_checked(fp) {
                    LookupOutcome::Present => return InsertOutcome::AlreadyPresent,
                    LookupOutcome::Absent => {}
                    LookupOutcome::StorageFault(fault) => {
                        return InsertOutcome::StorageFault(fault)
                    }
                    _ => unreachable!(),
                }

                // Try to insert into primary
                // Part of #2058: Match MmapError variants explicitly instead of Err(_).
                // TableFull → eviction is appropriate (load factor exceeded).
                // ProbeExceeded → clustering issue, surface as StorageFault immediately.
                match self.primary.insert(fp) {
                    Ok(true) => {
                        self.total_count.fetch_add(1, Ordering::Relaxed);
                        return InsertOutcome::Inserted;
                    }
                    Ok(false) => return InsertOutcome::AlreadyPresent,
                    Err(MmapError::TableFull { .. }) => {
                        // Primary full — drop read lock, evict, and retry (TLC: unbounded)
                    }
                    Err(e @ MmapError::ProbeExceeded { .. }) => {
                        return InsertOutcome::StorageFault(StorageFault::new(
                            "disk",
                            "insert",
                            format!("primary probe exhaustion: {e}"),
                        ));
                    }
                    // #[non_exhaustive] guard: surface unknown future variants as faults.
                    #[allow(unreachable_patterns)]
                    Err(e) => {
                        return InsertOutcome::StorageFault(StorageFault::new(
                            "disk",
                            "insert",
                            format!("unexpected primary error: {e}"),
                        ));
                    }
                }
            }
            // Read lock released: evict to disk. If disk I/O fails, that IS a
            // real error — return immediately (not a contention retry).
            if let Err(e) = self.evict() {
                self.record_disk_error("eviction during insert", &e);
                return InsertOutcome::StorageFault(StorageFault::new(
                    "disk",
                    "insert",
                    e.to_string(),
                ));
            }
            // Eviction succeeded — loop back and retry insert (TLC pattern)
        }
    }

    /// Check if a fingerprint is present with typed outcome.
    pub fn contains_checked(&self, fp: Fingerprint) -> LookupOutcome {
        // Hold read lock while accessing primary to prevent concurrent clear().
        // Fix for #1423.
        let _guard = self.primary_barrier.read();

        // Check primary first (fast path)
        if self.primary.contains(fp) {
            return LookupOutcome::Present;
        }

        // Check disk if we have a disk file
        self.disk_lookup_checked(fp)
    }

    /// Return the total number of fingerprints (primary + disk).
    pub fn len(&self) -> usize {
        self.total_count.load(Ordering::Relaxed)
    }

    /// Check if the set is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return the number of fingerprints on disk.
    pub fn disk_count(&self) -> usize {
        self.disk_count.load(Ordering::Relaxed)
    }

    /// Return the number of evictions performed.
    pub fn eviction_count(&self) -> usize {
        self.eviction_count.load(Ordering::Relaxed)
    }

    /// Return statistics about disk operations.
    pub fn disk_stats(&self) -> (usize, usize) {
        (
            self.disk_lookups.load(Ordering::Relaxed),
            self.disk_hits.load(Ordering::Relaxed),
        )
    }

    /// Return storage counters aggregated across the primary and disk tiers.
    pub fn stats(&self) -> StorageStats {
        let (disk_lookups, disk_hits) = self.disk_stats();
        StorageStats {
            disk_count: self.disk_count(),
            disk_lookups,
            disk_hits,
            eviction_count: self.eviction_count(),
            ..self.primary.stats()
        }
    }

    /// Returns true if lookup I/O failures or primary storage errors occurred.
    pub fn has_errors(&self) -> bool {
        self.disk_error_count.load(Ordering::Relaxed) > 0 || self.primary.has_errors()
    }

    /// Returns the total number of storage-level errors encountered.
    pub fn dropped_count(&self) -> usize {
        self.disk_error_count
            .load(Ordering::Relaxed)
            .saturating_add(self.primary.dropped_count())
    }
}

// ============================================================================
// Trait impls
// ============================================================================

impl tla_mc_core::FingerprintSet<Fingerprint> for DiskFingerprintSet {
    fn insert_checked(&self, fp: Fingerprint) -> InsertOutcome {
        DiskFingerprintSet::insert_checked(self, fp)
    }

    fn contains_checked(&self, fp: Fingerprint) -> LookupOutcome {
        DiskFingerprintSet::contains_checked(self, fp)
    }

    fn len(&self) -> usize {
        DiskFingerprintSet::len(self)
    }

    fn has_errors(&self) -> bool {
        DiskFingerprintSet::has_errors(self)
    }

    fn dropped_count(&self) -> usize {
        DiskFingerprintSet::dropped_count(self)
    }

    fn capacity_status(&self) -> CapacityStatus {
        // Disk storage has effectively unlimited capacity
        CapacityStatus::Normal
    }
}

impl FingerprintSet for DiskFingerprintSet {
    fn stats(&self) -> StorageStats {
        DiskFingerprintSet::stats(self)
    }

    fn prefers_disk_successor_graph(&self) -> bool {
        true
    }

    fn begin_checkpoint(&self) -> Result<(), StorageFault> {
        // Flush the primary mmap tier so pending writes reach disk before
        // checkpoint extraction. Delegates to MmapFingerprintSet::begin_checkpoint.
        self.primary.begin_checkpoint()
    }

    fn check_invariant(&self) -> Result<bool, StorageFault> {
        DiskFingerprintSet::check_invariant_impl(self)
    }

    fn collect_fingerprints(&self) -> Result<Vec<Fingerprint>, StorageFault> {
        self.collect_all_fingerprints()
    }
}
