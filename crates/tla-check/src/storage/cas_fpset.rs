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
//! Part of #3170.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};

use crate::state::Fingerprint;

use super::contracts::{FingerprintSet, InsertOutcome, LookupOutcome, StorageFault, StorageStats};
use super::open_addressing::{EMPTY, FP_MASK, MAX_PROBE};

/// A single lock-free open-addressing fingerprint table.
///
/// Uses `AtomicU64` slots with CAS insertion. Empty slots contain [`EMPTY`] (0).
/// Fingerprints that encode to 0 after masking are tracked via a dedicated
/// `has_zero` flag, matching the existing open-addressing conventions.
///
/// The table has a fixed capacity set at construction time. Exceeding
/// [`MAX_PROBE`] linear probes on insert indicates the table is too full.
pub(crate) struct CasFingerprintSet {
    /// The open-addressing table. Each slot is either EMPTY or an encoded fingerprint.
    table: Box<[AtomicU64]>,
    /// Total number of distinct fingerprints inserted.
    count: AtomicUsize,
    /// Whether a fingerprint encoding to 0 has been inserted.
    has_zero: AtomicBool,
    // Part of #3991: advisory probe-chain observability counters.
    /// The longest probe chain observed across all insert attempts.
    max_probe_len: AtomicUsize,
    /// Total probe steps across all insert attempts.
    total_probes: AtomicU64,
    /// Total number of insert attempts.
    total_inserts: AtomicU64,
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
    pub(crate) fn new(capacity: usize) -> Self {
        assert!(capacity > 0, "CasFingerprintSet capacity must be > 0");
        let capacity = capacity.next_power_of_two();
        let table: Vec<AtomicU64> = (0..capacity).map(|_| AtomicU64::new(EMPTY)).collect();
        Self {
            table: table.into_boxed_slice(),
            count: AtomicUsize::new(0),
            has_zero: AtomicBool::new(false),
            max_probe_len: AtomicUsize::new(0),
            total_probes: AtomicU64::new(0),
            total_inserts: AtomicU64::new(0),
            mask: capacity - 1,
        }
    }

    /// Encode a fingerprint for table storage (mask off MSB, reserved for flushed flag).
    #[inline]
    fn encode(fp: Fingerprint) -> u64 {
        fp.0 & FP_MASK
    }

    // Part of #3991: track advisory probe-chain statistics with relaxed atomics.
    #[inline]
    fn record_probe_stats(&self, probe_len: usize) {
        self.total_probes
            .fetch_add(probe_len as u64, Ordering::Relaxed);
        if probe_len > self.max_probe_len.load(Ordering::Relaxed) {
            let _ = self.max_probe_len.fetch_max(probe_len, Ordering::Relaxed);
        }
    }

    #[inline]
    fn total_probes_internal(&self) -> u64 {
        self.total_probes.load(Ordering::Relaxed)
    }

    #[inline]
    fn total_inserts_internal(&self) -> u64 {
        self.total_inserts.load(Ordering::Relaxed)
    }

    // Part of #3991: expose advisory probe-chain observability for a single CAS table.
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn max_probe_len(&self) -> usize {
        self.max_probe_len.load(Ordering::Relaxed)
    }

    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn avg_probe_len(&self) -> f64 {
        let total_inserts = self.total_inserts_internal();
        if total_inserts == 0 {
            0.0
        } else {
            self.total_probes_internal() as f64 / total_inserts as f64
        }
    }

    /// Insert a fingerprint. Returns `true` if newly inserted, `false` if duplicate.
    ///
    /// On probe limit exceeded, returns `false` (drops the fingerprint) and the
    /// caller should check `has_errors()`. This matches the mmap backend behavior.
    #[inline]
    fn insert_internal(&self, fp: Fingerprint) -> InsertOutcome {
        self.total_inserts.fetch_add(1, Ordering::Relaxed);
        let encoded = Self::encode(fp);

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
            let probe_len = probe + 1;
            let idx = (start + probe) & self.mask;
            let slot = &self.table[idx];

            // Fast path: read the slot first.
            let current = slot.load(Ordering::Acquire);

            if current == encoded {
                // Already present — dedup.
                self.record_probe_stats(probe_len);
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
                        self.record_probe_stats(probe_len);
                        return InsertOutcome::Inserted;
                    }
                    Err(actual) => {
                        // Someone else wrote to this slot. Check if it's our value.
                        if actual == encoded {
                            self.record_probe_stats(probe_len);
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
        // This is a storage fault, but we handle it the same way as mmap:
        // the fingerprint is effectively dropped.
        self.record_probe_stats(MAX_PROBE);
        InsertOutcome::StorageFault(super::contracts::StorageFault::new(
            "cas",
            "insert",
            format!("exceeded {} probes inserting fingerprint {}", MAX_PROBE, fp),
        ))
    }

    /// Check if a fingerprint is present.
    #[inline]
    fn contains_internal(&self, fp: Fingerprint) -> LookupOutcome {
        let encoded = Self::encode(fp);

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

    /// Number of distinct fingerprints inserted.
    #[inline]
    fn len_internal(&self) -> usize {
        self.count.load(Ordering::Acquire)
    }

    /// Memory bytes used by this table, including metadata. Part of #3991.
    fn memory_bytes(&self) -> usize {
        std::mem::size_of::<Self>().saturating_add(std::mem::size_of_val(self.table.as_ref()))
    }

    /// Collect all fingerprints stored in this table. Part of #2893.
    fn collect_internal(&self) -> Vec<Fingerprint> {
        let mut result = Vec::with_capacity(self.count.load(Ordering::Acquire));
        if self.has_zero.load(Ordering::Acquire) {
            result.push(Fingerprint(0));
        }
        for slot in self.table.iter() {
            let encoded = slot.load(Ordering::Acquire);
            if encoded != EMPTY {
                result.push(Fingerprint(encoded));
            }
        }
        result
    }
}

/// MSB-partitioned CAS fingerprint set for parallel model checking.
///
/// Partitions fingerprints across multiple [`CasFingerprintSet`] instances
/// using MSB routing, matching TLC's `MultiFPSet` architecture. Each partition
/// is independently lock-free, so workers contend only when they hash to the
/// same partition AND probe the same cache line.
///
/// Part of #3170.
pub(crate) struct PartitionedCasFingerprintSet {
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
    pub(crate) fn new(partition_bits: u32, total_capacity: usize) -> Self {
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
    fn partition_index(&self, fp: Fingerprint) -> usize {
        (fp.0 >> self.shift) as usize & self.mask
    }

    // Part of #3991: aggregate advisory probe-chain stats across all partitions.
    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn max_probe_len(&self) -> usize {
        self.partitions
            .iter()
            .map(CasFingerprintSet::max_probe_len)
            .max()
            .unwrap_or(0)
    }

    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn avg_probe_len(&self) -> f64 {
        let (total_probes, total_inserts) = self.partitions.iter().fold(
            (0u64, 0u64),
            |(total_probes, total_inserts), partition| {
                (
                    total_probes.saturating_add(partition.total_probes_internal()),
                    total_inserts.saturating_add(partition.total_inserts_internal()),
                )
            },
        );
        if total_inserts == 0 {
            0.0
        } else {
            total_probes as f64 / total_inserts as f64
        }
    }
}

impl tla_mc_core::FingerprintSet<Fingerprint> for PartitionedCasFingerprintSet {
    #[inline]
    fn insert_checked(&self, fp: Fingerprint) -> InsertOutcome {
        let idx = self.partition_index(fp);
        self.partitions[idx].insert_internal(fp)
    }

    #[inline]
    fn contains_checked(&self, fp: Fingerprint) -> LookupOutcome {
        let idx = self.partition_index(fp);
        self.partitions[idx].contains_internal(fp)
    }

    fn len(&self) -> usize {
        self.partitions
            .iter()
            .map(CasFingerprintSet::len_internal)
            .sum()
    }
}

impl FingerprintSet for PartitionedCasFingerprintSet {
    fn stats(&self) -> StorageStats {
        StorageStats {
            memory_count: tla_mc_core::FingerprintSet::len(self),
            memory_bytes: std::mem::size_of::<Self>().saturating_add(
                self.partitions
                    .iter()
                    .map(CasFingerprintSet::memory_bytes)
                    .sum::<usize>(),
            ),
            ..StorageStats::default()
        }
    }

    fn fresh_empty_clone(&self) -> Result<std::sync::Arc<dyn FingerprintSet>, StorageFault> {
        let partition_bits = 64 - self.shift;
        let total_capacity = self
            .partitions
            .iter()
            .map(|partition| partition.table.len())
            .sum();
        Ok(
            std::sync::Arc::new(Self::new(partition_bits, total_capacity))
                as std::sync::Arc<dyn FingerprintSet>,
        )
    }

    /// Part of #2893: Collect all fingerprints across all partitions.
    fn collect_fingerprints(&self) -> Result<Vec<Fingerprint>, super::contracts::StorageFault> {
        let mut result = Vec::with_capacity(tla_mc_core::FingerprintSet::len(self));
        for partition in self.partitions.iter() {
            result.extend(partition.collect_internal());
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::contracts::{InsertOutcome, LookupOutcome};
    // Bring insert_checked/contains_checked/len into scope for PartitionedCasFingerprintSet.
    use std::sync::Arc;
    use std::thread;
    use tla_mc_core::FingerprintSet as _;

    // --- CasFingerprintSet unit tests ---

    #[test]
    fn test_cas_insert_contains_roundtrip() {
        let set = CasFingerprintSet::new(1024);
        let fp1 = Fingerprint(0xDEADBEEF_CAFEBABE);
        let fp2 = Fingerprint(0x1234_5678_9ABC_DEF0);
        let fp_absent = Fingerprint(0xFFFF_FFFF_FFFF_FFFF);

        // Insert fp1
        assert_eq!(set.insert_internal(fp1), InsertOutcome::Inserted);
        assert_eq!(set.len_internal(), 1);

        // Dedup fp1
        assert_eq!(set.insert_internal(fp1), InsertOutcome::AlreadyPresent);
        assert_eq!(set.len_internal(), 1);

        // Insert fp2
        assert_eq!(set.insert_internal(fp2), InsertOutcome::Inserted);
        assert_eq!(set.len_internal(), 2);

        // Contains checks
        assert_eq!(set.contains_internal(fp1), LookupOutcome::Present);
        assert_eq!(set.contains_internal(fp2), LookupOutcome::Present);
        assert_eq!(set.contains_internal(fp_absent), LookupOutcome::Absent);
    }

    #[test]
    fn test_cas_zero_fingerprint_handling() {
        let set = CasFingerprintSet::new(1024);
        // A fingerprint whose lower 63 bits are all zero.
        let fp_zero = Fingerprint(1u64 << 63); // MSB set, encodes to 0

        assert_eq!(set.contains_internal(fp_zero), LookupOutcome::Absent);
        assert_eq!(set.insert_internal(fp_zero), InsertOutcome::Inserted);
        assert_eq!(set.contains_internal(fp_zero), LookupOutcome::Present);
        assert_eq!(set.insert_internal(fp_zero), InsertOutcome::AlreadyPresent);
        assert_eq!(set.len_internal(), 1);

        // Also test fingerprint 0 itself (both MSB and lower bits are 0).
        let fp_real_zero = Fingerprint(0);
        // Encodes to 0 as well, so same side-flag — counts as duplicate.
        assert_eq!(
            set.insert_internal(fp_real_zero),
            InsertOutcome::AlreadyPresent
        );
    }

    #[test]
    fn test_cas_concurrent_duplicate_inserts() {
        let set = Arc::new(CasFingerprintSet::new(65536));
        let fp = Fingerprint(0xCAFE_BABE_1234_5678);

        let handles: Vec<_> = (0..8)
            .map(|_| {
                let set = Arc::clone(&set);
                thread::spawn(move || set.insert_internal(fp))
            })
            .collect();

        let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        let inserted_count = results
            .iter()
            .filter(|r| **r == InsertOutcome::Inserted)
            .count();

        // Exactly one thread should succeed with Inserted.
        assert_eq!(inserted_count, 1);
        assert_eq!(set.len_internal(), 1);
    }

    // --- PartitionedCasFingerprintSet tests ---

    #[test]
    fn test_partitioned_insert_contains_roundtrip() {
        let set = PartitionedCasFingerprintSet::new(2, 4096); // 4 partitions
        let fp1 = Fingerprint(0xDEADBEEF_CAFEBABE);
        let fp2 = Fingerprint(0x1234_5678_9ABC_DEF0);
        let fp_absent = Fingerprint(0xFFFF_FFFF_FFFF_FFFF);

        assert_eq!(set.insert_checked(fp1), InsertOutcome::Inserted);
        assert_eq!(set.len(), 1);

        assert_eq!(set.insert_checked(fp1), InsertOutcome::AlreadyPresent);
        assert_eq!(set.len(), 1);

        assert_eq!(set.insert_checked(fp2), InsertOutcome::Inserted);
        assert_eq!(set.len(), 2);

        assert_eq!(set.contains_checked(fp1), LookupOutcome::Present);
        assert_eq!(set.contains_checked(fp2), LookupOutcome::Present);
        assert_eq!(set.contains_checked(fp_absent), LookupOutcome::Absent);
    }

    #[test]
    fn test_partitioned_partition_routing() {
        // Fingerprints with different MSBs should route to different partitions.
        let set = PartitionedCasFingerprintSet::new(2, 4096); // 4 partitions

        // Insert fingerprints designed to hit different partitions.
        for i in 0..4u64 {
            let fp = Fingerprint(i << 62); // MSB 2 bits = partition index
            assert_eq!(set.insert_checked(fp), InsertOutcome::Inserted);
        }
        assert_eq!(set.len(), 4);

        // Verify all are findable.
        for i in 0..4u64 {
            let fp = Fingerprint(i << 62);
            assert_eq!(set.contains_checked(fp), LookupOutcome::Present);
        }
    }

    #[test]
    fn test_partitioned_concurrent_mixed_inserts() {
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
                        let fp = Fingerprint(raw.wrapping_mul(0x9E3779B97F4A7C15));
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
        assert_eq!(set.len(), num_threads * fps_per_thread);
    }

    #[test]
    fn test_cas_stress_32_threads_high_contention() {
        // Part of #3991: verify exact counts under heavy duplicate contention.
        let set = Arc::new(PartitionedCasFingerprintSet::new(4, 1 << 20));
        let num_threads = 32usize;
        let fps_per_thread = 2000usize;
        let overlap = 1000usize; // first 1000 FPs shared across all threads

        let barrier = Arc::new(std::sync::Barrier::new(num_threads));

        let handles: Vec<_> = (0..num_threads)
            .map(|t| {
                let set = Arc::clone(&set);
                let barrier = Arc::clone(&barrier);
                thread::spawn(move || {
                    barrier.wait();
                    let mut inserted = 0usize;
                    for i in 0..fps_per_thread {
                        let raw = if i < overlap {
                            (i as u64) + 1 // shared across all threads
                        } else {
                            (t as u64) * 1_000_000 + (i as u64) + 1 // unique per thread
                        };
                        let fp = Fingerprint(raw.wrapping_mul(0x9E3779B97F4A7C15));
                        if set.insert_checked(fp) == InsertOutcome::Inserted {
                            inserted += 1;
                        }
                    }
                    inserted
                })
            })
            .collect();

        let total_inserted: usize = handles.into_iter().map(|h| h.join().unwrap()).sum();
        let expected = overlap + num_threads * (fps_per_thread - overlap);
        assert_eq!(total_inserted, expected);
        assert_eq!(set.len(), expected);
    }

    // --- Probe chain statistics tests (Part of #3991) ---

    #[test]
    fn test_cas_probe_stats_single_partition() {
        // Part of #3991: validate probe chain observability counters.
        let set = CasFingerprintSet::new(1024);

        // Before any inserts, stats should be zero.
        assert_eq!(set.max_probe_len(), 0);
        assert_eq!(set.avg_probe_len(), 0.0);

        // Insert several distinct fingerprints.
        for i in 1u64..=100 {
            let fp = Fingerprint(i.wrapping_mul(0x9E3779B97F4A7C15));
            set.insert_internal(fp);
        }

        // max_probe_len should be at least 1 (every insert probes at least 1 slot).
        assert!(
            set.max_probe_len() >= 1,
            "max_probe_len should be >= 1 after inserts, got {}",
            set.max_probe_len()
        );

        // avg_probe_len should be between 1.0 and MAX_PROBE.
        let avg = set.avg_probe_len();
        assert!(
            (1.0..=1024.0).contains(&avg),
            "avg_probe_len should be in [1.0, 1024.0], got {avg}"
        );

        // total_inserts should include all 100 inserts.
        assert_eq!(set.total_inserts_internal(), 100);
    }

    #[test]
    fn test_cas_probe_stats_partitioned() {
        // Part of #3991: validate aggregated probe stats across partitions.
        let set = PartitionedCasFingerprintSet::new(2, 4096); // 4 partitions

        for i in 1u64..=200 {
            let fp = Fingerprint(i.wrapping_mul(0x9E3779B97F4A7C15));
            set.insert_checked(fp);
        }

        // Aggregated stats should be non-zero after inserts.
        assert!(
            set.max_probe_len() >= 1,
            "partitioned max_probe_len should be >= 1"
        );
        let avg = set.avg_probe_len();
        assert!(
            avg >= 1.0,
            "partitioned avg_probe_len should be >= 1.0, got {avg}"
        );
    }

    #[test]
    fn test_cas_probe_stats_duplicates_counted() {
        // Part of #3991: verify that duplicate insert attempts are counted
        // in total_inserts (they still probe the table).
        let set = CasFingerprintSet::new(1024);
        let fp = Fingerprint(0xDEAD_BEEF_CAFE_BABE);

        set.insert_internal(fp);
        set.insert_internal(fp); // duplicate
        set.insert_internal(fp); // duplicate

        assert_eq!(set.total_inserts_internal(), 3);
        assert_eq!(set.len_internal(), 1); // only 1 distinct fp
    }

    #[test]
    fn test_partitioned_zero_fingerprint_across_partitions() {
        let set = PartitionedCasFingerprintSet::new(2, 4096);
        // Zero fingerprint should work through the partition routing.
        let fp_zero = Fingerprint(0);
        assert_eq!(set.insert_checked(fp_zero), InsertOutcome::Inserted);
        assert_eq!(set.contains_checked(fp_zero), LookupOutcome::Present);
        assert_eq!(set.insert_checked(fp_zero), InsertOutcome::AlreadyPresent);
        assert_eq!(set.len(), 1);
    }

    // --- collect_fingerprints tests (Part of #2893) ---
    #[test]
    fn test_partitioned_collect_fingerprints_empty() {
        let set = PartitionedCasFingerprintSet::new(2, 4096);
        let fps = FingerprintSet::collect_fingerprints(&set).expect("cas collect");
        assert!(fps.is_empty());
    }

    #[test]
    fn test_partitioned_collect_fingerprints_returns_all() {
        let set = PartitionedCasFingerprintSet::new(2, 4096);
        set.insert_checked(Fingerprint(10));
        set.insert_checked(Fingerprint(20));
        set.insert_checked(Fingerprint(30));

        let fps = FingerprintSet::collect_fingerprints(&set).expect("cas collect");
        let collected: std::collections::HashSet<u64> = fps.iter().map(|f| f.0).collect();
        assert_eq!(collected.len(), 3);
        assert!(collected.contains(&10));
        assert!(collected.contains(&20));
        assert!(collected.contains(&30));
    }

    #[test]
    fn test_partitioned_collect_fingerprints_includes_zero() {
        let set = PartitionedCasFingerprintSet::new(2, 4096);
        set.insert_checked(Fingerprint(0));
        set.insert_checked(Fingerprint(1));

        let fps = FingerprintSet::collect_fingerprints(&set).expect("cas collect");
        let collected: std::collections::HashSet<u64> = fps.iter().map(|f| f.0).collect();
        assert!(collected.contains(&0), "FP(0) must be included");
        assert!(collected.contains(&1));
        assert_eq!(collected.len(), 2);
    }
}
