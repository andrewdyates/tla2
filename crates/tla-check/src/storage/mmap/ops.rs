// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Hot-path open-addressing probe operations for MmapFingerprintSet.

use crate::state::Fingerprint;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::storage::open_addressing::{
    encode_fingerprint, is_flushed, mark_flushed, MmapError, EMPTY, FP_MASK, MAX_PROBE,
};

use super::MmapFingerprintSet;

impl MmapFingerprintSet {
    /// Get a reference to the slot at the given index as an atomic u64.
    ///
    /// # Safety
    ///
    /// The index must be in bounds (0..capacity).
    #[inline]
    pub(in crate::storage::mmap) fn slot(&self, index: usize) -> &AtomicU64 {
        assert!(
            index < self.capacity,
            "slot index {index} out of bounds (capacity {})",
            self.capacity
        );
        let ptr = self.mmap.as_ptr().cast::<AtomicU64>();
        // SAFETY: The mmap is properly aligned for u64, and index < capacity
        // is enforced by the assert above.
        #[allow(clippy::cast_ptr_alignment)]
        unsafe {
            &*ptr.add(index)
        }
    }

    /// Compute the primary hash index for a fingerprint.
    #[inline]
    pub(in crate::storage::mmap) fn hash_index(&self, fp: Fingerprint) -> usize {
        // Use the fingerprint itself as a hash (it's already a hash).
        // Apply a secondary scramble to improve distribution.
        // Mask off MSB (FLUSHED_BIT) so FPs differing only in bit 63 hash
        // to the same probe chain — encode_fingerprint also masks to FP_MASK,
        // so without this they'd occupy separate slots with identical encoded
        // values (#2674).
        let h = (fp.0 & FP_MASK).wrapping_mul(0x9E3779B97F4A7C15); // Golden ratio constant
        (h as usize) % self.capacity
    }

    /// Insert a fingerprint into the set.
    ///
    /// # Returns
    ///
    /// - `Ok(true)` if the fingerprint was newly inserted
    /// - `Ok(false)` if the fingerprint was already present
    /// - `Err(...)` if the table is too full (load factor exceeded)
    ///
    /// # Thread Safety
    ///
    /// This method is safe to call from multiple threads simultaneously.
    pub fn insert(&self, fp: Fingerprint) -> Result<bool, MmapError> {
        // Fix #1535: Handle FPs that encode to 0 via separate flag — they cannot
        // be stored in the mmap array since 0 is the EMPTY sentinel.
        // This covers FP(0) and FP(FLUSHED_BIT) since both have lower 63 bits = 0.
        if fp.0 & FP_MASK == 0 {
            let was_new = !self.has_zero.swap(true, Ordering::AcqRel);
            if was_new {
                self.count.fetch_add(1, Ordering::Relaxed);
            }
            return Ok(was_new);
        }

        // Check load factor before inserting (only unflushed entries count)
        let current_count = self.count.load(Ordering::Relaxed);
        if current_count as f64 / self.capacity as f64 >= self.max_load_factor {
            return Err(MmapError::TableFull {
                count: current_count,
                capacity: self.capacity,
            });
        }

        let encoded = encode_fingerprint(fp);
        let start_index = self.hash_index(fp);

        for probe in 0..MAX_PROBE {
            let index = (start_index + probe) % self.capacity;
            let slot = self.slot(index);

            let current = slot.load(Ordering::Acquire);

            // Check for match (including flushed variant of same fingerprint).
            // A flushed entry with the same FP means it was evicted to disk but
            // is being re-inserted — treat as "already present".
            if current == encoded || current == mark_flushed(encoded) {
                return Ok(false);
            }

            // Both EMPTY and flushed slots are valid insertion targets.
            // Flushed slots can be overwritten because their data is on disk.
            if current == EMPTY || is_flushed(current) {
                match slot.compare_exchange(current, encoded, Ordering::AcqRel, Ordering::Acquire) {
                    Ok(_) => {
                        self.count.fetch_add(1, Ordering::Relaxed);
                        return Ok(true);
                    }
                    Err(actual) => {
                        if actual == encoded || actual == mark_flushed(encoded) {
                            return Ok(false);
                        }
                        // Different fingerprint — continue probing
                    }
                }
            }
            // Slot occupied by different unflushed fingerprint — continue probing
        }

        Err(MmapError::ProbeExceeded {
            fp,
            probes: MAX_PROBE,
        })
    }

    /// Check if a fingerprint is present in the set.
    ///
    /// # Thread Safety
    ///
    /// This method is safe to call from multiple threads simultaneously.
    pub fn contains(&self, fp: Fingerprint) -> bool {
        // FPs that encode to 0 are tracked via separate flag.
        if fp.0 & FP_MASK == 0 {
            return self.has_zero.load(Ordering::Acquire);
        }

        let encoded = encode_fingerprint(fp);
        let start_index = self.hash_index(fp);

        for probe in 0..MAX_PROBE {
            let index = (start_index + probe) % self.capacity;
            let slot = self.slot(index);
            let current = slot.load(Ordering::Acquire);

            // Match both unflushed and flushed variants of the same fingerprint.
            // Flushed entries are still "present" — they exist in the set (on disk).
            if current == encoded || current == mark_flushed(encoded) {
                return true;
            }

            if current == EMPTY {
                return false;
            }
        }

        false
    }
}
