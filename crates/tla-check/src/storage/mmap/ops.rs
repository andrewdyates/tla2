// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Hot-path open-addressing probe operations for MmapFingerprintSet.

use crate::state::Fingerprint;
use crate::storage::{InsertOutcome, StorageFault};
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

        let encoded = encode_fingerprint(fp);
        let start_index = self.hash_index(fp);
        'retry: loop {
            let current_count = self.count.load(Ordering::Relaxed);
            let table_full = current_count as f64 / self.capacity as f64 >= self.max_load_factor;
            let mut first_flushed: Option<(usize, u64)> = None;

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

                if is_flushed(current) {
                    first_flushed.get_or_insert((index, current));
                    continue;
                }

                if current == EMPTY {
                    if table_full {
                        return Err(MmapError::TableFull {
                            count: current_count,
                            capacity: self.capacity,
                        });
                    }
                    let (target_index, expected) = first_flushed.unwrap_or((index, current));
                    let target = self.slot(target_index);
                    match target.compare_exchange(
                        expected,
                        encoded,
                        Ordering::AcqRel,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => {
                            self.count.fetch_add(1, Ordering::Relaxed);
                            return Ok(true);
                        }
                        Err(actual) => {
                            if actual == encoded || actual == mark_flushed(encoded) {
                                return Ok(false);
                            }
                            // A racing insert/flush changed the reusable slot; retry
                            // from the head so duplicate detection remains complete.
                            continue 'retry;
                        }
                    }
                }
                // Slot occupied by different unflushed fingerprint — continue probing.
            }

            if table_full {
                return Err(MmapError::TableFull {
                    count: current_count,
                    capacity: self.capacity,
                });
            }

            if let Some((target_index, expected)) = first_flushed {
                let target = self.slot(target_index);
                match target.compare_exchange(
                    expected,
                    encoded,
                    Ordering::AcqRel,
                    Ordering::Acquire,
                ) {
                    Ok(_) => {
                        self.count.fetch_add(1, Ordering::Relaxed);
                        return Ok(true);
                    }
                    Err(actual) => {
                        if actual == encoded || actual == mark_flushed(encoded) {
                            return Ok(false);
                        }
                        continue 'retry;
                    }
                }
            }

            return Err(MmapError::ProbeExceeded {
                fp,
                probes: MAX_PROBE,
            });
        }
    }

    /// Insert raw fingerprint values into caller-owned outcome scratch.
    ///
    /// The batch stops at the first storage fault and does not attempt suffix
    /// fingerprints after that fault.
    pub(crate) fn insert_fingerprint_values_checked_into(
        &self,
        fingerprint_values: &[u64],
        outcomes: &mut Vec<InsertOutcome>,
    ) {
        outcomes.clear();
        outcomes.reserve(fingerprint_values.len());
        for &fp in fingerprint_values {
            let outcome = match self.insert(Fingerprint(fp)) {
                Ok(true) => InsertOutcome::Inserted,
                Ok(false) => InsertOutcome::AlreadyPresent,
                Err(err) => {
                    self.record_error();
                    InsertOutcome::StorageFault(StorageFault::new(
                        "mmap",
                        "insert",
                        err.to_string(),
                    ))
                }
            };
            let stop = matches!(&outcome, InsertOutcome::StorageFault(_));
            outcomes.push(outcome);
            if stop {
                break;
            }
        }
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
