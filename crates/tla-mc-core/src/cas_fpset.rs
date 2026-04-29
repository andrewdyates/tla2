// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lock-free CAS-based fingerprint set for parallel model checking.
//!
//! [`CasFingerprintSet`] is an open-addressing hash table using `AtomicU64`
//! slots with compare-and-swap insertion. This eliminates the `RwLock`
//! contention that caps `ShardedFingerprintSet` throughput at 4 workers.
//!
//! [`PartitionedCasFingerprintSet`] partitions fingerprints by MSB across
//! multiple `CasFingerprintSet` instances, matching TLC's
//! `MultiFPSet<OffHeapDiskFPSet>` architecture.
//!
//! Part of #3718.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

use crate::storage::{FingerprintSet, InsertOutcome, LookupOutcome, StorageFault, StorageStats};

/// Sentinel value for empty slots.
/// Fingerprint 0 is handled separately via a dedicated `has_zero` flag.
const EMPTY: u64 = 0;

/// Mask for the lower 63 bits — the actual fingerprint value.
/// The MSB is reserved for the flushed flag.
const FP_MASK: u64 = !(1u64 << 63);

/// Maximum number of probes before giving up on insert.
/// If exceeded, the table is too full and should be resized.
const MAX_PROBE: usize = 1024;

/// A single lock-free open-addressing fingerprint table.
///
/// Uses `AtomicU64` slots with CAS insertion. Empty slots contain [`EMPTY`] (0).
/// Fingerprints that encode to 0 after masking are tracked via a dedicated
/// `has_zero` flag, matching the existing open-addressing conventions.
///
/// The table has a fixed capacity set at construction time. Exceeding
/// [`MAX_PROBE`] linear probes on insert indicates the table is too full.
pub struct CasFingerprintSet {
    /// The open-addressing table. Each slot is either EMPTY or an encoded fingerprint.
    table: Box<[AtomicU64]>,
    /// Total number of distinct fingerprints inserted.
    count: AtomicUsize,
    /// Whether a fingerprint encoding to 0 has been inserted.
    has_zero: AtomicBool,
    /// Bitmask for index computation: capacity - 1.
    mask: usize,
}

impl CasFingerprintSet {
    /// Create a new CAS fingerprint set with the given capacity.
    ///
    /// Capacity is rounded up to the next power of two.
    ///
    /// # Panics
    ///
    /// Panics if capacity is 0.
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0, "CasFingerprintSet capacity must be > 0");
        let capacity = capacity.next_power_of_two();
        let table: Vec<AtomicU64> = (0..capacity).map(|_| AtomicU64::new(EMPTY)).collect();
        Self {
            table: table.into_boxed_slice(),
            count: AtomicUsize::new(0),
            has_zero: AtomicBool::new(false),
            mask: capacity - 1,
        }
    }

    /// Encode a fingerprint for table storage (mask off MSB, reserved for flushed flag).
    #[inline]
    fn encode(fp: u64) -> u64 {
        fp & FP_MASK
    }

    /// Memory bytes used by the table.
    fn memory_bytes(&self) -> usize {
        self.table.len() * std::mem::size_of::<AtomicU64>()
    }
}

impl FingerprintSet<u64> for CasFingerprintSet {
    #[inline]
    fn insert_checked(&self, fingerprint: u64) -> InsertOutcome {
        let encoded = Self::encode(fingerprint);

        // Zero-encoded fingerprints use the side flag.
        if encoded == EMPTY {
            return if self
                .has_zero
                .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                .is_ok()
            {
                self.count.fetch_add(1, Ordering::Release);
                InsertOutcome::Inserted
            } else {
                InsertOutcome::AlreadyPresent
            };
        }

        // Linear probing with CAS.
        let start = (encoded as usize) & self.mask;
        for probe in 0..MAX_PROBE {
            let idx = (start + probe) & self.mask;
            let slot = &self.table[idx];

            // Fast path: read the slot first.
            let current = slot.load(Ordering::Acquire);

            if current == encoded {
                // Already present — dedup.
                return InsertOutcome::AlreadyPresent;
            }

            if current == EMPTY {
                // Try to claim this empty slot via CAS.
                match slot.compare_exchange_weak(
                    EMPTY,
                    encoded,
                    Ordering::AcqRel,
                    Ordering::Acquire,
                ) {
                    Ok(_) => {
                        // Successfully inserted.
                        self.count.fetch_add(1, Ordering::Release);
                        return InsertOutcome::Inserted;
                    }
                    Err(actual) => {
                        // Someone else wrote to this slot. Check if it's our value.
                        if actual == encoded {
                            return InsertOutcome::AlreadyPresent;
                        }
                        // Otherwise continue probing — the slot is now occupied
                        // by a different fingerprint.
                    }
                }
            }
            // Slot occupied by a different fingerprint — continue probing.
        }

        // Probe limit exceeded — table is too full.
        InsertOutcome::StorageFault(StorageFault::new(
            "cas",
            "insert",
            format!(
                "exceeded {} probes inserting fingerprint {}",
                MAX_PROBE, fingerprint
            ),
        ))
    }

    #[inline]
    fn contains_checked(&self, fingerprint: u64) -> LookupOutcome {
        let encoded = Self::encode(fingerprint);

        if encoded == EMPTY {
            return if self.has_zero.load(Ordering::Acquire) {
                LookupOutcome::Present
            } else {
                LookupOutcome::Absent
            };
        }

        let start = (encoded as usize) & self.mask;
        for probe in 0..MAX_PROBE {
            let idx = (start + probe) & self.mask;
            let current = self.table[idx].load(Ordering::Acquire);

            if current == encoded {
                return LookupOutcome::Present;
            }
            if current == EMPTY {
                return LookupOutcome::Absent;
            }
            // Different fingerprint — continue probing.
        }

        // Probe limit exceeded without finding EMPTY — conservatively report absent.
        LookupOutcome::Absent
    }

    fn len(&self) -> usize {
        self.count.load(Ordering::Acquire)
    }

    fn stats(&self) -> StorageStats {
        StorageStats {
            memory_count: self.len(),
            memory_bytes: self.memory_bytes(),
        }
    }
}

/// MSB-partitioned CAS fingerprint set for parallel model checking.
///
/// Partitions fingerprints across multiple [`CasFingerprintSet`] instances
/// using MSB routing, matching TLC's `MultiFPSet` architecture. Each partition
/// is independently lock-free, so workers contend only when they hash to the
/// same partition AND probe the same cache line.
///
/// Part of #3718.
pub struct PartitionedCasFingerprintSet {
    /// The CAS partitions.
    partitions: Box<[CasFingerprintSet]>,
    /// Right-shift amount: 64 - partition_bits.
    shift: u32,
    /// Mask for extracting partition index: num_partitions - 1.
    mask: usize,
}

impl PartitionedCasFingerprintSet {
    /// Create a new partitioned CAS fingerprint set.
    ///
    /// # Arguments
    ///
    /// * `partition_bits` - Number of MSB bits for partitioning.
    ///   Creates 2^partition_bits partitions. Must be 1-16.
    /// * `total_capacity` - Total capacity across all partitions.
    ///   Each partition gets `total_capacity / num_partitions` slots.
    ///
    /// # Panics
    ///
    /// Panics if `partition_bits` is 0 or > 16.
    pub fn new(partition_bits: u32, total_capacity: usize) -> Self {
        assert!(
            (1..=16).contains(&partition_bits),
            "partition_bits must be 1-16, got {}",
            partition_bits,
        );

        let num_partitions = 1usize << partition_bits;
        let per_partition = total_capacity.div_ceil(num_partitions).max(1024);
        let partitions: Vec<CasFingerprintSet> = (0..num_partitions)
            .map(|_| CasFingerprintSet::new(per_partition))
            .collect();

        Self {
            partitions: partitions.into_boxed_slice(),
            shift: 64 - partition_bits,
            mask: num_partitions - 1,
        }
    }

    /// MSB partition routing (same as TLC's `MultiFPSet.getIndex`).
    #[inline]
    fn partition_index(&self, fp: u64) -> usize {
        (fp >> self.shift) as usize & self.mask
    }
}

impl FingerprintSet<u64> for PartitionedCasFingerprintSet {
    #[inline]
    fn insert_checked(&self, fingerprint: u64) -> InsertOutcome {
        let idx = self.partition_index(fingerprint);
        self.partitions[idx].insert_checked(fingerprint)
    }

    #[inline]
    fn contains_checked(&self, fingerprint: u64) -> LookupOutcome {
        let idx = self.partition_index(fingerprint);
        self.partitions[idx].contains_checked(fingerprint)
    }

    fn len(&self) -> usize {
        self.partitions.iter().map(|p| FingerprintSet::len(p)).sum()
    }

    fn stats(&self) -> StorageStats {
        StorageStats {
            memory_count: self.len(),
            memory_bytes: self
                .partitions
                .iter()
                .map(CasFingerprintSet::memory_bytes)
                .sum(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::{InsertOutcome, LookupOutcome};
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn test_cas_insert_contains_roundtrip() {
        let set = CasFingerprintSet::new(1024);
        let fp1: u64 = 0xDEADBEEF_CAFEBABE;
        let fp2: u64 = 0x1234_5678_9ABC_DEF0;
        let fp_absent: u64 = 0xFFFF_FFFF_FFFF_FFFF;

        // Insert fp1.
        assert_eq!(set.insert_checked(fp1), InsertOutcome::Inserted);
        assert_eq!(FingerprintSet::len(&set), 1);

        // Dedup fp1.
        assert_eq!(set.insert_checked(fp1), InsertOutcome::AlreadyPresent);
        assert_eq!(FingerprintSet::len(&set), 1);

        // Insert fp2.
        assert_eq!(set.insert_checked(fp2), InsertOutcome::Inserted);
        assert_eq!(FingerprintSet::len(&set), 2);

        // Contains checks.
        assert_eq!(set.contains_checked(fp1), LookupOutcome::Present);
        assert_eq!(set.contains_checked(fp2), LookupOutcome::Present);
        assert_eq!(set.contains_checked(fp_absent), LookupOutcome::Absent);
    }

    #[test]
    fn test_cas_zero_fingerprint_handling() {
        let set = CasFingerprintSet::new(1024);
        // A fingerprint whose lower 63 bits are all zero.
        let fp_zero: u64 = 1u64 << 63; // MSB set, encodes to 0

        assert_eq!(set.contains_checked(fp_zero), LookupOutcome::Absent);
        assert_eq!(set.insert_checked(fp_zero), InsertOutcome::Inserted);
        assert_eq!(set.contains_checked(fp_zero), LookupOutcome::Present);
        assert_eq!(set.insert_checked(fp_zero), InsertOutcome::AlreadyPresent);
        assert_eq!(FingerprintSet::len(&set), 1);

        // Also test fingerprint 0 itself (both MSB and lower bits are 0).
        let fp_real_zero: u64 = 0;
        // Encodes to 0 as well, so same side-flag — counts as duplicate.
        assert_eq!(
            set.insert_checked(fp_real_zero),
            InsertOutcome::AlreadyPresent
        );
    }

    #[test]
    fn test_cas_concurrent_duplicate_inserts() {
        let set = Arc::new(CasFingerprintSet::new(65536));
        let fp: u64 = 0xCAFE_BABE_1234_5678;

        let handles: Vec<_> = (0..8)
            .map(|_| {
                let set = Arc::clone(&set);
                thread::spawn(move || set.insert_checked(fp))
            })
            .collect();

        let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        let inserted_count = results
            .iter()
            .filter(|r| **r == InsertOutcome::Inserted)
            .count();

        // Exactly one thread should succeed with Inserted.
        assert_eq!(inserted_count, 1);
        assert_eq!(FingerprintSet::len(&*set), 1);
    }

    #[test]
    fn test_partitioned_routing() {
        // Fingerprints with different MSBs should route to different partitions.
        let set = PartitionedCasFingerprintSet::new(2, 4096); // 4 partitions

        // Insert fingerprints designed to hit different partitions.
        for i in 0..4u64 {
            let fp = i << 62; // MSB 2 bits = partition index
            assert_eq!(set.insert_checked(fp), InsertOutcome::Inserted);
        }
        assert_eq!(FingerprintSet::len(&set), 4);

        // Verify all are findable.
        for i in 0..4u64 {
            let fp = i << 62;
            assert_eq!(set.contains_checked(fp), LookupOutcome::Present);
        }
    }

    #[test]
    fn test_partitioned_concurrent_mixed() {
        // Use enough total capacity and well-distributed fingerprints so
        // inserts don't overflow any single partition.
        let set = Arc::new(PartitionedCasFingerprintSet::new(4, 1 << 20));
        let num_threads = 8;
        let fps_per_thread = 1000;

        let handles: Vec<_> = (0..num_threads)
            .map(|t| {
                let set = Arc::clone(&set);
                thread::spawn(move || {
                    let mut inserted = 0usize;
                    for i in 0..fps_per_thread {
                        // Multiply by a large prime to spread MSBs across partitions.
                        // Raw sequential values all land in partition 0 (MSB = 0).
                        let raw = (t as u64) * 1_000_000 + i as u64 + 1;
                        let fp = raw.wrapping_mul(0x9E3779B97F4A7C15);
                        if set.insert_checked(fp) == InsertOutcome::Inserted {
                            inserted += 1;
                        }
                    }
                    inserted
                })
            })
            .collect();

        let total_inserted: usize = handles.into_iter().map(|h| h.join().unwrap()).sum();
        assert_eq!(total_inserted, num_threads * fps_per_thread);
        assert_eq!(FingerprintSet::len(&*set), num_threads * fps_per_thread);
    }

    #[test]
    fn test_cas_stats() {
        let set = CasFingerprintSet::new(1024);
        // 1024 is already a power of 2, so capacity = 1024.
        let stats = FingerprintSet::stats(&set);
        assert_eq!(stats.memory_count, 0);
        assert_eq!(stats.memory_bytes, 1024 * std::mem::size_of::<AtomicU64>());

        set.insert_checked(42);
        set.insert_checked(99);
        let stats = FingerprintSet::stats(&set);
        assert_eq!(stats.memory_count, 2);
        // memory_bytes unchanged — fixed-size table.
        assert_eq!(stats.memory_bytes, 1024 * std::mem::size_of::<AtomicU64>());
    }
}
