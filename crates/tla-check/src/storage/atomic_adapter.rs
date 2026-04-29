// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Adapts the 128-bit lock-free [`ResizableAtomicFpSet`] for use with the
//! 64-bit [`Fingerprint`] type used in model checking.

use crate::state::atomic_fp_set::{InsertResult, ResizableAtomicFpSet};
use crate::state::Fingerprint;
use std::sync::Arc;
use tla_mc_core::{FingerprintSet as CoreFingerprintSet, InsertOutcome, LookupOutcome};

use super::contracts::{FingerprintSet as McFingerprintSet, StorageStats};

pub(crate) struct AtomicFpSetAdapter(ResizableAtomicFpSet);

impl AtomicFpSetAdapter {
    #[must_use]
    pub(crate) fn new(capacity: usize) -> Self {
        Self(ResizableAtomicFpSet::new(capacity))
    }

    #[inline]
    fn encode(fp: Fingerprint) -> u128 {
        u128::from(fp.0)
    }

    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn capacity(&self) -> usize {
        self.0.capacity()
    }

    #[must_use]
    #[allow(dead_code)]
    pub(crate) fn load_factor(&self) -> f64 {
        self.0.load_factor()
    }
}

impl CoreFingerprintSet<Fingerprint> for AtomicFpSetAdapter {
    fn insert_checked(&self, fp: Fingerprint) -> InsertOutcome {
        match self.0.insert_if_absent(Self::encode(fp)) {
            InsertResult::Inserted => InsertOutcome::Inserted,
            InsertResult::AlreadyPresent => InsertOutcome::AlreadyPresent,
            InsertResult::ProbeLimitHit => {
                InsertOutcome::StorageFault(super::contracts::StorageFault::new(
                    "atomic",
                    "insert",
                    format!(
                        "unexpected probe limit inserting fingerprint into \
                         ResizableAtomicFpSet: {fp}"
                    ),
                ))
            }
        }
    }

    fn contains_checked(&self, fp: Fingerprint) -> LookupOutcome {
        if self.0.contains(Self::encode(fp)) {
            LookupOutcome::Present
        } else {
            LookupOutcome::Absent
        }
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

impl McFingerprintSet for AtomicFpSetAdapter {
    fn stats(&self) -> StorageStats {
        StorageStats {
            memory_count: self.0.len(),
            memory_bytes: self.0.memory_bytes(),
            ..StorageStats::default()
        }
    }

    fn fresh_empty_clone(
        &self,
    ) -> Result<Arc<dyn McFingerprintSet>, super::contracts::StorageFault> {
        Ok(Arc::new(Self(self.0.fresh_empty_clone())) as Arc<dyn McFingerprintSet>)
    }

    /// Collect all fingerprints from the 128-bit table, truncated to 64-bit.
    ///
    /// The underlying `ResizableAtomicFpSet` stores 128-bit values, but the
    /// adapter encodes 64-bit [`Fingerprint`] values as `u128`. The lower 64
    /// bits of each entry reconstruct the original `Fingerprint`.
    ///
    /// Part of #3991.
    fn collect_fingerprints(&self) -> Result<Vec<Fingerprint>, super::contracts::StorageFault> {
        let all = self.0.collect_all();
        Ok(all.iter().map(|fp128| Fingerprint(*fp128 as u64)).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::super::contracts::{FingerprintSet as McFingerprintSet, StorageStats};
    use super::AtomicFpSetAdapter;
    use crate::state::Fingerprint;
    use tla_mc_core::{FingerprintSet as CoreFingerprintSet, InsertOutcome, LookupOutcome};

    #[test]
    fn test_adapter_basic_insert_contains() {
        let set = AtomicFpSetAdapter::new(16);
        let fp = Fingerprint(0xDEAD_BEEF_CAFE_BABE);
        let missing = Fingerprint(0x1234_5678_9ABC_DEF0);

        assert_eq!(
            CoreFingerprintSet::contains_checked(&set, fp),
            LookupOutcome::Absent
        );
        assert_eq!(
            CoreFingerprintSet::insert_checked(&set, fp),
            InsertOutcome::Inserted
        );
        assert_eq!(
            CoreFingerprintSet::contains_checked(&set, fp),
            LookupOutcome::Present
        );
        assert_eq!(
            CoreFingerprintSet::contains_checked(&set, missing),
            LookupOutcome::Absent
        );
        assert_eq!(set.len(), 1);
        assert!(set.capacity() >= 16);
        assert!(set.load_factor() > 0.0);

        let stats: StorageStats = McFingerprintSet::stats(&set);
        assert_eq!(stats.memory_count, 1);
        assert_eq!(stats.disk_count, 0);
        assert!(stats.memory_bytes > 0);
    }

    #[test]
    fn test_adapter_duplicate() {
        let set = AtomicFpSetAdapter::new(8);
        let fp = Fingerprint(42);

        assert_eq!(
            CoreFingerprintSet::insert_checked(&set, fp),
            InsertOutcome::Inserted
        );
        assert_eq!(
            CoreFingerprintSet::insert_checked(&set, fp),
            InsertOutcome::AlreadyPresent
        );
        assert_eq!(
            CoreFingerprintSet::contains_checked(&set, fp),
            LookupOutcome::Present
        );
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_adapter_zero_fingerprint() {
        let set = AtomicFpSetAdapter::new(8);
        let zero = Fingerprint(0);

        assert_eq!(
            CoreFingerprintSet::contains_checked(&set, zero),
            LookupOutcome::Absent
        );
        assert_eq!(
            CoreFingerprintSet::insert_checked(&set, zero),
            InsertOutcome::Inserted
        );
        assert_eq!(
            CoreFingerprintSet::contains_checked(&set, zero),
            LookupOutcome::Present
        );
        assert_eq!(
            CoreFingerprintSet::insert_checked(&set, zero),
            InsertOutcome::AlreadyPresent
        );
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_adapter_never_returns_probe_limit() {
        let set = AtomicFpSetAdapter::new(8);
        let initial_capacity = set.capacity();

        for i in 1..=512u64 {
            let fp = Fingerprint(i.wrapping_mul(0x517C_C1B7_2722_0A95));
            let outcome = CoreFingerprintSet::insert_checked(&set, fp);
            assert!(
                matches!(
                    outcome,
                    InsertOutcome::Inserted | InsertOutcome::AlreadyPresent
                ),
                "unexpected insert outcome for {fp}: {outcome:?}"
            );
        }

        assert_eq!(set.len(), 512);
        assert!(
            set.capacity() > initial_capacity,
            "capacity should grow beyond {initial_capacity}, got {}",
            set.capacity()
        );
        for i in 1..=512u64 {
            let fp = Fingerprint(i.wrapping_mul(0x517C_C1B7_2722_0A95));
            assert_eq!(
                CoreFingerprintSet::contains_checked(&set, fp),
                LookupOutcome::Present
            );
        }
    }

    // --- collect_fingerprints tests (Part of #3991) ---

    #[test]
    fn test_adapter_collect_fingerprints_empty() {
        let set = AtomicFpSetAdapter::new(64);
        let fps = McFingerprintSet::collect_fingerprints(&set).expect("should not fail");
        assert!(fps.is_empty());
    }

    #[test]
    fn test_adapter_collect_fingerprints_roundtrip() {
        let set = AtomicFpSetAdapter::new(64);
        CoreFingerprintSet::insert_checked(&set, Fingerprint(10));
        CoreFingerprintSet::insert_checked(&set, Fingerprint(20));
        CoreFingerprintSet::insert_checked(&set, Fingerprint(30));

        let fps = McFingerprintSet::collect_fingerprints(&set).expect("should not fail");
        let collected: std::collections::HashSet<u64> = fps.iter().map(|f| f.0).collect();
        assert_eq!(collected.len(), 3);
        assert!(collected.contains(&10));
        assert!(collected.contains(&20));
        assert!(collected.contains(&30));
    }

    #[test]
    fn test_adapter_collect_fingerprints_includes_zero() {
        let set = AtomicFpSetAdapter::new(64);
        CoreFingerprintSet::insert_checked(&set, Fingerprint(0));
        CoreFingerprintSet::insert_checked(&set, Fingerprint(1));

        let fps = McFingerprintSet::collect_fingerprints(&set).expect("should not fail");
        let collected: std::collections::HashSet<u64> = fps.iter().map(|f| f.0).collect();
        assert!(collected.contains(&0), "FP(0) must be included");
        assert!(collected.contains(&1));
        assert_eq!(collected.len(), 2);
    }

    #[test]
    fn test_adapter_fresh_empty_clone_is_empty_and_preserves_capacity() {
        let set = AtomicFpSetAdapter::new(8);
        for i in 1..=512u64 {
            let fp = Fingerprint(i.wrapping_mul(0x517C_C1B7_2722_0A95));
            assert!(matches!(
                CoreFingerprintSet::insert_checked(&set, fp),
                InsertOutcome::Inserted | InsertOutcome::AlreadyPresent
            ));
        }

        let original_stats = McFingerprintSet::stats(&set);
        let fresh = McFingerprintSet::fresh_empty_clone(&set).expect("fresh clone should succeed");

        assert_eq!(fresh.len(), 0);
        assert_eq!(
            CoreFingerprintSet::contains_checked(fresh.as_ref(), Fingerprint(1)),
            LookupOutcome::Absent
        );
        assert_eq!(
            McFingerprintSet::stats(fresh.as_ref()).memory_bytes,
            original_stats.memory_bytes
        );
        assert_eq!(
            CoreFingerprintSet::insert_checked(fresh.as_ref(), Fingerprint(1)),
            InsertOutcome::Inserted
        );
        assert_eq!(
            CoreFingerprintSet::contains_checked(fresh.as_ref(), Fingerprint(1)),
            LookupOutcome::Present
        );
        assert_eq!(set.len(), 512);
    }

    // --- Concurrent stress test (Part of #3991) ---

    #[test]
    fn test_adapter_concurrent_16_threads() {
        use std::sync::Arc;
        use std::thread;

        let set = Arc::new(AtomicFpSetAdapter::new(1 << 18));
        let num_threads = 16usize;
        let fps_per_thread = 2000usize;
        let overlap = 500usize;

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
                            // Shared fingerprints across all threads.
                            (i as u64) + 1
                        } else {
                            // Unique per thread.
                            (t as u64) * 1_000_000 + (i as u64) + 1
                        };
                        let fp = Fingerprint(raw.wrapping_mul(0x9E3779B97F4A7C15));
                        if CoreFingerprintSet::insert_checked(&*set, fp) == InsertOutcome::Inserted
                        {
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
        assert_eq!(CoreFingerprintSet::<Fingerprint>::len(&*set), expected);

        // Verify collect_fingerprints matches len.
        let fps = McFingerprintSet::collect_fingerprints(set.as_ref()).expect("collect");
        assert_eq!(fps.len(), expected);
    }
}
