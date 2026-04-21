// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Maintenance, eviction, and observability helpers for MmapFingerprintSet.

use std::io;
use std::sync::atomic::Ordering;

use crate::storage::contracts::CapacityStatus;
use crate::storage::open_addressing::{decode_fingerprint, is_flushed, mark_flushed, EMPTY};

use super::MmapFingerprintSet;

impl MmapFingerprintSet {
    /// Return the number of fingerprints stored.
    ///
    /// Note: In concurrent usage, this may be slightly stale.
    pub fn len(&self) -> usize {
        self.count.load(Ordering::Relaxed)
    }

    /// Check if the set is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return the capacity (maximum number of fingerprints).
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Return the current load factor (count / capacity).
    pub fn load_factor(&self) -> f64 {
        self.len() as f64 / self.capacity as f64
    }

    /// Flush any pending writes to disk (for file-backed mappings).
    ///
    /// This is useful before checkpointing.
    pub fn flush(&self) -> io::Result<()> {
        self.mmap.flush()
    }

    /// Flush asynchronously (returns immediately).
    pub fn flush_async(&self) -> io::Result<()> {
        self.mmap.flush_async()
    }

    /// Check if any insert errors have occurred (table overflow).
    ///
    /// When this returns true, some fingerprints were not stored and the
    /// model checking results may be incomplete (states may have been dropped).
    pub fn has_errors(&self) -> bool {
        self.has_error.load(Ordering::Relaxed)
    }

    /// Get the count of dropped fingerprints due to table overflow.
    ///
    /// If this is non-zero, model checking results are unreliable.
    pub fn dropped_count(&self) -> usize {
        self.dropped_count.load(Ordering::Relaxed)
    }

    /// Record an insert error (table overflow or probe exceeded).
    pub(crate) fn record_error(&self) {
        self.has_error.store(true, Ordering::Relaxed);
        self.dropped_count.fetch_add(1, Ordering::Relaxed);
    }

    /// Check the current capacity status.
    ///
    /// Returns `CapacityStatus::Normal` if plenty of space is available,
    /// `CapacityStatus::Warning` if approaching limit (>80% of load factor),
    /// or `CapacityStatus::Critical` if very close to limit (>95% of load factor).
    ///
    /// Use this to provide early warning to users when the fingerprint table
    /// is approaching capacity.
    pub fn capacity_status(&self) -> CapacityStatus {
        let count = self.count.load(Ordering::Relaxed);
        let usage = count as f64 / self.capacity as f64;
        let max_usage = self.max_load_factor;

        // Calculate how close we are to the load factor limit
        let usage_ratio = usage / max_usage;

        if usage_ratio >= 0.95 {
            CapacityStatus::Critical {
                count,
                capacity: self.capacity,
                usage,
            }
        } else if usage_ratio >= 0.80 {
            CapacityStatus::Warning {
                count,
                capacity: self.capacity,
                usage,
            }
        } else {
            CapacityStatus::Normal
        }
    }

    /// Get the max load factor for this set.
    pub fn max_load_factor(&self) -> f64 {
        self.max_load_factor
    }

    /// Collect all unflushed fingerprints currently stored in this set.
    ///
    /// Flushed entries (already evicted to disk) are skipped — only entries
    /// that need to be written to disk during eviction are returned.
    ///
    /// This scans all slots and returns decoded fingerprint values.
    /// Time complexity is O(capacity), so use sparingly (e.g., during eviction).
    ///
    /// # Thread Safety
    ///
    /// This method provides a point-in-time snapshot. Concurrent inserts
    /// may or may not be included in the result.
    pub fn collect_all(&self) -> Vec<u64> {
        let mut result = Vec::with_capacity(self.count.load(Ordering::Relaxed));

        // Fix #1535: Include FP(0) if present (stored via flag, not in array).
        if self.has_zero.load(Ordering::Acquire) {
            result.push(0);
        }

        for i in 0..self.capacity {
            let slot = self.slot(i);
            let encoded = slot.load(Ordering::Acquire);

            // Skip empty slots and flushed entries (already on disk).
            if encoded != EMPTY && !is_flushed(encoded) {
                result.push(decode_fingerprint(encoded));
            }
        }

        result
    }

    /// Mark all occupied slots as flushed (TLC MSBDiskFPSet parity).
    ///
    /// After eviction, entries stay in the mmap as a lookup cache — `contains()`
    /// still returns true for flushed entries, avoiding unnecessary disk I/O for
    /// recently-evicted fingerprints. `collect_all()` skips flushed entries since
    /// they are already on disk.
    ///
    /// Only unflushed entries count toward load factor, so this resets the count
    /// to 0, allowing new inserts up to the load factor threshold. New inserts
    /// can overwrite flushed slots.
    ///
    /// # Thread Safety
    ///
    /// This method is NOT safe to call concurrently with insert/contains.
    /// Use only when exclusive access is guaranteed (e.g., during eviction
    /// when all workers are paused).
    pub fn mark_all_flushed(&self) {
        for i in 0..self.capacity {
            let slot = self.slot(i);
            let val = slot.load(Ordering::Relaxed);
            if val != EMPTY && !is_flushed(val) {
                slot.store(mark_flushed(val), Ordering::Relaxed);
            }
        }
        // Only unflushed entries count toward load factor.
        self.count.store(0, Ordering::Relaxed);
        self.has_error.store(false, Ordering::Relaxed);
        self.dropped_count.store(0, Ordering::Relaxed);
        // Note: has_zero is NOT reset — flushed zero entries are still "present".
    }

    /// Clear all entries from this set.
    ///
    /// This resets all slots to EMPTY and count to 0.
    /// Time complexity is O(capacity).
    ///
    /// # Thread Safety
    ///
    /// This method is NOT safe to call concurrently with insert/contains.
    /// Use only when exclusive access is guaranteed (e.g., during eviction
    /// when all workers are paused).
    pub fn clear(&self) {
        for i in 0..self.capacity {
            let slot = self.slot(i);
            slot.store(EMPTY, Ordering::Release);
        }
        self.count.store(0, Ordering::Relaxed);
        self.has_error.store(false, Ordering::Relaxed);
        self.dropped_count.store(0, Ordering::Relaxed);
        self.has_zero.store(false, Ordering::Relaxed);
    }
}
