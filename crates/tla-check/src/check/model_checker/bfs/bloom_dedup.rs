// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Two-level Bloom filter dedup for compiled BFS.
//!
//! State deduplication in BFS model checking is on the critical path: every
//! successor must be checked against the global seen set. For million-state
//! specs, the hash set lookup dominates wall time due to cache misses on the
//! large hash table.
//!
//! This module provides a two-level dedup structure:
//!
//! 1. **Bloom filter** (fast, approximate): A compact bit array with 3 hash
//!    functions. Negative results are definitive (state is definitely new).
//!    Positive results may be false positives.
//!
//! 2. **Exact hash set** (slow, precise): Only consulted when the Bloom filter
//!    says "maybe seen". If the exact set confirms the state is present, it is
//!    a true duplicate. If absent, it was a Bloom false positive — the state
//!    is new.
//!
//! The key insight: for BFS model checking, most successors at each level are
//! duplicates (states already visited in prior levels). The Bloom filter
//! handles these duplicates with a single cache-friendly bit-probe, avoiding
//! the expensive hash set lookup. Only truly new states and the small fraction
//! of false positives hit the hash set.
//!
//! # Sizing
//!
//! The Bloom filter auto-scales based on an initial capacity hint. With 3 hash
//! functions and m/n ratio of ~10 (10 bits per element), the false positive
//! rate is approximately 0.82%. The filter can grow by re-creating with a
//! larger capacity when the element count exceeds the initial hint.
//!
//! Part of #4172: Two-level Bloom filter dedup for compiled BFS.

use crate::state::Fingerprint;

/// Number of hash functions used by the Bloom filter.
///
/// With k=3 and m/n=10, FPR ≈ 0.82%.
/// With k=3 and m/n=14.4 (1M bits / 69K elements), FPR ≈ 0.15%.
const NUM_HASHES: usize = 3;

/// Minimum number of bits in the Bloom filter.
/// 1M bits = 128 KB — fits comfortably in L2 cache.
const MIN_BITS: usize = 1 << 20; // 1,048,576

/// Bits per element for sizing. 10 bits/element gives ~0.82% FPR with k=3.
const BITS_PER_ELEMENT: usize = 10;

/// A simple Bloom filter for u64 fingerprints.
///
/// Uses 3 hash functions derived from a single u64 fingerprint via
/// double-hashing (Kirschner-Mitzenmacher). Since `Fingerprint` values
/// are already high-quality 64-bit hashes (FP64 polynomial), we split
/// the fingerprint into two 32-bit halves to derive independent probes:
///
///   h_i(x) = (h1(x) + i * h2(x)) mod m
///
/// This is a well-known technique that provides the same asymptotic
/// false positive rate as fully independent hash functions.
///
/// Reference: Kirschner & Mitzenmacher, "Less Hashing, Same Performance:
/// Building a Better Bloom Filter", ESA 2006.
pub(in crate::check::model_checker) struct BloomFilter {
    /// Bit array stored as u64 words for efficient bit manipulation.
    bits: Vec<u64>,
    /// Total number of bits (= bits.len() * 64).
    num_bits: usize,
    /// Number of elements inserted (for statistics).
    count: usize,
}

impl BloomFilter {
    /// Create a new Bloom filter sized for at least `capacity` elements.
    ///
    /// The actual bit count is `max(MIN_BITS, capacity * BITS_PER_ELEMENT)`,
    /// rounded up to a multiple of 64 for word alignment.
    #[must_use]
    pub(in crate::check::model_checker) fn new(capacity: usize) -> Self {
        let raw_bits = capacity
            .saturating_mul(BITS_PER_ELEMENT)
            .max(MIN_BITS);
        // Round up to multiple of 64.
        let num_bits = (raw_bits + 63) & !63;
        let num_words = num_bits / 64;
        BloomFilter {
            bits: vec![0u64; num_words],
            num_bits,
            count: 0,
        }
    }

    /// Derive 3 bit positions from a fingerprint using double hashing.
    ///
    /// The fingerprint is split into two 32-bit halves. The lower half is
    /// h1, the upper half is h2. Probe i = (h1 + i * h2) % num_bits.
    #[inline]
    fn probe_positions(&self, fp: Fingerprint) -> [usize; NUM_HASHES] {
        let val = fp.0;
        let h1 = (val & 0xFFFF_FFFF) as u64;
        let h2 = (val >> 32) as u64;
        let m = self.num_bits as u64;
        let mut positions = [0usize; NUM_HASHES];
        for i in 0..NUM_HASHES {
            // wrapping_add/wrapping_mul to avoid overflow
            let probe = h1.wrapping_add((i as u64).wrapping_mul(h2));
            positions[i] = (probe % m) as usize;
        }
        positions
    }

    /// Insert a fingerprint into the Bloom filter.
    ///
    /// Sets the corresponding bits. Does not check for prior membership.
    #[inline]
    pub(in crate::check::model_checker) fn insert(&mut self, fp: Fingerprint) {
        let positions = self.probe_positions(fp);
        for pos in positions {
            let word = pos / 64;
            let bit = pos % 64;
            self.bits[word] |= 1u64 << bit;
        }
        self.count += 1;
    }

    /// Check whether a fingerprint might be in the filter.
    ///
    /// Returns `true` if all bits are set (may be a false positive).
    /// Returns `false` if any bit is unset (definitely not present).
    #[inline]
    #[must_use]
    pub(in crate::check::model_checker) fn maybe_contains(&self, fp: Fingerprint) -> bool {
        let positions = self.probe_positions(fp);
        for pos in positions {
            let word = pos / 64;
            let bit = pos % 64;
            if self.bits[word] & (1u64 << bit) == 0 {
                return false;
            }
        }
        true
    }

    /// Number of elements inserted.
    #[must_use]
    pub(in crate::check::model_checker) fn count(&self) -> usize {
        self.count
    }

    /// Total number of bits in the filter.
    #[must_use]
    pub(in crate::check::model_checker) fn num_bits(&self) -> usize {
        self.num_bits
    }

    /// Memory usage in bytes.
    #[must_use]
    pub(in crate::check::model_checker) fn memory_bytes(&self) -> usize {
        self.bits.len() * std::mem::size_of::<u64>()
    }

    /// Approximate false positive rate at current fill level.
    ///
    /// FPR ≈ (1 - e^(-kn/m))^k where k=3, n=count, m=num_bits.
    #[must_use]
    pub(in crate::check::model_checker) fn estimated_fpr(&self) -> f64 {
        if self.count == 0 {
            return 0.0;
        }
        let k = NUM_HASHES as f64;
        let n = self.count as f64;
        let m = self.num_bits as f64;
        (1.0 - (-k * n / m).exp()).powf(k)
    }
}

/// Two-level dedup combining a Bloom filter with an exact hash set.
///
/// The Bloom filter provides fast O(1) definitive negative responses for
/// states that are definitely new. The exact set is only consulted on
/// Bloom positives to distinguish true duplicates from false positives.
///
/// # Usage
///
/// ```ignore
/// let mut dedup = BloomDedup::new(1_000_000);
/// let fp = Fingerprint(0x1234);
/// if dedup.check_and_insert(fp) {
///     // State is new — enqueue for exploration
/// } else {
///     // State is a duplicate — skip
/// }
/// ```
///
/// Part of #4172: Two-level Bloom filter dedup for compiled BFS.
pub(in crate::check::model_checker) struct BloomDedup {
    /// Fast approximate filter — checked first.
    bloom: BloomFilter,
    /// Exact set — checked only on Bloom positives.
    exact: std::collections::HashSet<Fingerprint>,
    /// Statistics: total checks performed.
    total_checks: u64,
    /// Statistics: Bloom filter said "not present" (definitive new).
    bloom_negatives: u64,
    /// Statistics: Bloom filter said "maybe present" (checked exact set).
    bloom_positives: u64,
    /// Statistics: Bloom positive confirmed as true duplicate by exact set.
    true_duplicates: u64,
    /// Statistics: Bloom positive was a false positive (state was new).
    false_positives: u64,
}

impl BloomDedup {
    /// Create a new two-level dedup structure sized for `capacity` states.
    #[must_use]
    pub(in crate::check::model_checker) fn new(capacity: usize) -> Self {
        BloomDedup {
            bloom: BloomFilter::new(capacity),
            exact: std::collections::HashSet::with_capacity(capacity),
            total_checks: 0,
            bloom_negatives: 0,
            bloom_positives: 0,
            true_duplicates: 0,
            false_positives: 0,
        }
    }

    /// Check if a fingerprint has been seen, and insert it if new.
    ///
    /// Returns `true` if the state is **new** (not previously seen).
    /// Returns `false` if the state is a **duplicate** (already seen).
    ///
    /// Two-level logic:
    /// 1. Bloom says "not present" → definitely new → insert in both → return true.
    /// 2. Bloom says "maybe present" → check exact set:
    ///    a. Exact set contains it → true duplicate → return false.
    ///    b. Exact set does not contain it → false positive → insert in exact → return true.
    #[inline]
    pub(in crate::check::model_checker) fn check_and_insert(&mut self, fp: Fingerprint) -> bool {
        self.total_checks += 1;

        if !self.bloom.maybe_contains(fp) {
            // Bloom negative: definitely new.
            self.bloom_negatives += 1;
            self.bloom.insert(fp);
            self.exact.insert(fp);
            return true;
        }

        // Bloom positive: might be a duplicate, check exact set.
        self.bloom_positives += 1;

        if self.exact.contains(&fp) {
            // True duplicate.
            self.true_duplicates += 1;
            false
        } else {
            // False positive: state is actually new.
            self.false_positives += 1;
            self.bloom.insert(fp); // Already set, but consistent
            self.exact.insert(fp);
            true
        }
    }

    /// Check if a fingerprint has been seen (read-only).
    ///
    /// Returns `true` if the state has been seen (is a duplicate).
    /// Returns `false` if the state is new.
    ///
    /// Does NOT insert the fingerprint. Use `check_and_insert` for
    /// combined check+insert.
    #[inline]
    #[must_use]
    pub(in crate::check::model_checker) fn contains(&self, fp: Fingerprint) -> bool {
        if !self.bloom.maybe_contains(fp) {
            return false;
        }
        self.exact.contains(&fp)
    }

    /// Number of unique states tracked.
    #[must_use]
    pub(in crate::check::model_checker) fn len(&self) -> usize {
        self.exact.len()
    }

    /// Whether the dedup set is empty.
    #[must_use]
    pub(in crate::check::model_checker) fn is_empty(&self) -> bool {
        self.exact.is_empty()
    }

    /// Report dedup statistics to stderr.
    pub(in crate::check::model_checker) fn report_stats(&self) {
        if self.total_checks == 0 {
            return;
        }
        let bloom_hit_rate = if self.total_checks > 0 {
            self.bloom_negatives as f64 / self.total_checks as f64
        } else {
            0.0
        };
        eprintln!(
            "[bloom-dedup] {} checks: {} bloom-neg ({:.1}%), {} bloom-pos, \
             {} true-dup, {} false-pos, FPR={:.3}%, {} unique states, bloom={} KB",
            self.total_checks,
            self.bloom_negatives,
            bloom_hit_rate * 100.0,
            self.bloom_positives,
            self.true_duplicates,
            self.false_positives,
            self.bloom.estimated_fpr() * 100.0,
            self.exact.len(),
            self.bloom.memory_bytes() / 1024,
        );
    }

    /// Get the Bloom filter's estimated false positive rate.
    #[must_use]
    pub(in crate::check::model_checker) fn estimated_fpr(&self) -> f64 {
        self.bloom.estimated_fpr()
    }

    /// Total checks performed.
    #[must_use]
    pub(in crate::check::model_checker) fn total_checks(&self) -> u64 {
        self.total_checks
    }

    /// Checks where Bloom filter definitively said "new" (fast path).
    #[must_use]
    pub(in crate::check::model_checker) fn bloom_negatives(&self) -> u64 {
        self.bloom_negatives
    }

    /// Bloom filter memory usage in bytes.
    #[must_use]
    pub(in crate::check::model_checker) fn bloom_memory_bytes(&self) -> usize {
        self.bloom.memory_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ====================================================================
    // BloomFilter unit tests
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bloom_empty_contains_nothing() {
        let bloom = BloomFilter::new(1000);
        for i in 0u64..100 {
            assert!(
                !bloom.maybe_contains(Fingerprint(i)),
                "empty bloom should not contain any fingerprint"
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bloom_insert_then_contains() {
        let mut bloom = BloomFilter::new(1000);
        let fps: Vec<Fingerprint> = (0u64..100).map(|i| Fingerprint(i * 7919 + 42)).collect();

        for &fp in &fps {
            bloom.insert(fp);
        }

        // All inserted fingerprints MUST be found (zero false negatives).
        for &fp in &fps {
            assert!(
                bloom.maybe_contains(fp),
                "inserted fingerprint {:?} must be found (zero false negatives)",
                fp
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bloom_zero_false_negatives_large() {
        // Insert 10K fingerprints, verify all are found.
        let mut bloom = BloomFilter::new(20_000);
        let fps: Vec<Fingerprint> = (0u64..10_000)
            .map(|i| Fingerprint(i.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1)))
            .collect();

        for &fp in &fps {
            bloom.insert(fp);
        }

        for (idx, &fp) in fps.iter().enumerate() {
            assert!(
                bloom.maybe_contains(fp),
                "false negative at index {}: fingerprint {:?} was inserted but not found",
                idx, fp
            );
        }
        assert_eq!(bloom.count(), 10_000);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bloom_false_positive_rate_bounded() {
        // Insert 10K fingerprints, check 10K non-inserted fingerprints.
        // With 10 bits/element and k=3, expected FPR ≈ 0.82%.
        // We allow up to 3% to account for statistical variance.
        let mut bloom = BloomFilter::new(10_000);
        for i in 0u64..10_000 {
            bloom.insert(Fingerprint(i));
        }

        let mut false_positives = 0u64;
        let test_count = 10_000u64;
        for i in 10_000u64..20_000 {
            if bloom.maybe_contains(Fingerprint(i)) {
                false_positives += 1;
            }
        }

        let fpr = false_positives as f64 / test_count as f64;
        assert!(
            fpr < 0.03,
            "false positive rate {:.2}% exceeds 3% threshold ({} false positives / {} tests)",
            fpr * 100.0,
            false_positives,
            test_count,
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bloom_min_size() {
        // Even with capacity=0, bloom should use MIN_BITS.
        let bloom = BloomFilter::new(0);
        assert!(bloom.num_bits() >= MIN_BITS);
        assert_eq!(bloom.count(), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bloom_scales_with_capacity() {
        let small = BloomFilter::new(1_000);
        let large = BloomFilter::new(1_000_000);
        assert!(
            large.num_bits() > small.num_bits(),
            "larger capacity should produce more bits"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bloom_memory_bytes() {
        let bloom = BloomFilter::new(1_000_000);
        // 1M * 10 bits = 10M bits = ~1.25 MB
        let memory = bloom.memory_bytes();
        assert!(memory > 0);
        assert!(
            memory <= 2 * 1024 * 1024,
            "1M-element bloom should use ~1.25 MB, got {} bytes",
            memory
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bloom_estimated_fpr_empty() {
        let bloom = BloomFilter::new(1000);
        assert_eq!(bloom.estimated_fpr(), 0.0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bloom_estimated_fpr_increases_with_fill() {
        let mut bloom = BloomFilter::new(10_000);
        let fpr_0 = bloom.estimated_fpr();

        for i in 0u64..5_000 {
            bloom.insert(Fingerprint(i));
        }
        let fpr_half = bloom.estimated_fpr();

        for i in 5_000u64..10_000 {
            bloom.insert(Fingerprint(i));
        }
        let fpr_full = bloom.estimated_fpr();

        assert!(fpr_0 < fpr_half, "FPR should increase as filter fills");
        assert!(fpr_half < fpr_full, "FPR should increase further");
    }

    // ====================================================================
    // BloomDedup unit tests
    // ====================================================================

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dedup_empty() {
        let dedup = BloomDedup::new(1000);
        assert!(dedup.is_empty());
        assert_eq!(dedup.len(), 0);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dedup_insert_new_returns_true() {
        let mut dedup = BloomDedup::new(1000);
        assert!(
            dedup.check_and_insert(Fingerprint(42)),
            "first insert should return true (new)"
        );
        assert_eq!(dedup.len(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dedup_insert_duplicate_returns_false() {
        let mut dedup = BloomDedup::new(1000);
        assert!(dedup.check_and_insert(Fingerprint(42)));
        assert!(
            !dedup.check_and_insert(Fingerprint(42)),
            "second insert of same fingerprint should return false (duplicate)"
        );
        assert_eq!(dedup.len(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dedup_distinct_fingerprints_all_new() {
        let mut dedup = BloomDedup::new(1000);
        for i in 0u64..100 {
            let fp = Fingerprint(i.wrapping_mul(0x9E3779B97F4A7C15));
            assert!(
                dedup.check_and_insert(fp),
                "distinct fingerprint {} should be new",
                i
            );
        }
        assert_eq!(dedup.len(), 100);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dedup_all_duplicates_detected() {
        let mut dedup = BloomDedup::new(1000);

        // Insert 100 fingerprints.
        let fps: Vec<Fingerprint> = (0u64..100)
            .map(|i| Fingerprint(i.wrapping_mul(0x517CC1B727220A95)))
            .collect();
        for &fp in &fps {
            assert!(dedup.check_and_insert(fp));
        }

        // Re-insert all — every one must be detected as duplicate.
        for &fp in &fps {
            assert!(
                !dedup.check_and_insert(fp),
                "re-inserted fingerprint {:?} must be detected as duplicate",
                fp
            );
        }
        assert_eq!(dedup.len(), 100);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dedup_contains_read_only() {
        let mut dedup = BloomDedup::new(1000);
        let fp = Fingerprint(0xDEADBEEF);

        assert!(!dedup.contains(fp), "should not contain before insert");
        dedup.check_and_insert(fp);
        assert!(dedup.contains(fp), "should contain after insert");

        // Verify contains doesn't insert.
        let fp2 = Fingerprint(0xCAFEBABE);
        assert!(!dedup.contains(fp2));
        assert!(!dedup.contains(fp2)); // Still not contained.
        assert_eq!(dedup.len(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dedup_statistics_tracking() {
        let mut dedup = BloomDedup::new(10_000);

        // Insert 1000 unique fingerprints.
        for i in 0u64..1000 {
            dedup.check_and_insert(Fingerprint(i));
        }

        // Re-check all 1000 as duplicates.
        for i in 0u64..1000 {
            dedup.check_and_insert(Fingerprint(i));
        }

        assert_eq!(dedup.total_checks(), 2000);
        assert_eq!(dedup.len(), 1000);

        // bloom_negatives should be at least 1 (the first insert of each unique).
        // Can't be exact because some first-inserts might be bloom positives
        // (from false positives on the bloom filter).
        assert!(
            dedup.bloom_negatives() > 0,
            "should have some bloom negatives"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dedup_zero_false_negatives_large() {
        // The critical correctness property: the dedup structure must NEVER
        // report a previously-inserted fingerprint as "new" (which would
        // cause a state to be explored twice, violating BFS correctness).
        let mut dedup = BloomDedup::new(50_000);

        let fps: Vec<Fingerprint> = (0u64..10_000)
            .map(|i| Fingerprint(i.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(0x7F4A7C15)))
            .collect();

        // Insert all.
        for &fp in &fps {
            assert!(dedup.check_and_insert(fp));
        }

        // Verify all are detected as duplicates. Zero tolerance for false negatives.
        for (idx, &fp) in fps.iter().enumerate() {
            assert!(
                !dedup.check_and_insert(fp),
                "CRITICAL: false negative at index {}: fingerprint {:?} was inserted but \
                 check_and_insert returned true (new). This would cause double-exploration \
                 in BFS and incorrect state counts.",
                idx, fp
            );
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dedup_interleaved_new_and_duplicate() {
        // Simulate a BFS pattern: some successors are new, some are duplicates.
        let mut dedup = BloomDedup::new(1000);

        // Level 0: all new.
        for i in 0u64..10 {
            assert!(dedup.check_and_insert(Fingerprint(i)));
        }

        // Level 1: mix of new and revisited.
        for i in 5u64..15 {
            let expected_new = i >= 10;
            let result = dedup.check_and_insert(Fingerprint(i));
            assert_eq!(
                result, expected_new,
                "fingerprint {} should be {} but was {}",
                i,
                if expected_new { "new" } else { "duplicate" },
                if result { "new" } else { "duplicate" },
            );
        }

        assert_eq!(dedup.len(), 15);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dedup_report_stats_does_not_panic() {
        let mut dedup = BloomDedup::new(100);
        // Empty report.
        dedup.report_stats();

        // Non-empty report.
        for i in 0u64..50 {
            dedup.check_and_insert(Fingerprint(i));
        }
        dedup.report_stats();
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_dedup_fpr_bounded_at_scale() {
        // Insert 100K states, then check 100K non-inserted states.
        // The false positive rate should be reasonable (< 5%).
        let mut dedup = BloomDedup::new(100_000);

        for i in 0u64..100_000 {
            dedup.check_and_insert(Fingerprint(i));
        }

        let mut false_positives = 0u64;
        let test_count = 100_000u64;
        for i in 100_000u64..200_000 {
            if dedup.contains(Fingerprint(i)) {
                false_positives += 1;
            }
        }

        let fpr = false_positives as f64 / test_count as f64;
        assert!(
            fpr < 0.05,
            "false positive rate {:.2}% exceeds 5% at 100K elements ({} false positives)",
            fpr * 100.0,
            false_positives,
        );
    }
}
