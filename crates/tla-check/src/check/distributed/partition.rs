// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(dead_code)]

//! Fingerprint-space partitioning for distributed BFS.
//!
//! Maps each 64-bit [`Fingerprint`] to a partition index, determining which
//! worker owns a state for deduplication and successor processing.
//!
//! Two schemes:
//! - **Modulo**: `fp % num_partitions` — simple, deterministic, zero overhead.
//!   Suitable for fixed-size deployments where partition count is known at start.
//! - **Consistent hashing (ring)**: Virtual-node ring with binary search lookup.
//!   Supports dynamic scaling (add/remove nodes) with minimal key redistribution.
//!   Not used in the thread-based PoC but provided for future network transport.

use crate::state::Fingerprint;

/// Fingerprint-space partitioning scheme.
///
/// Determines which partition (and thus which worker thread) owns a given
/// fingerprint for deduplication and BFS processing.
#[derive(Debug, Clone)]
pub(crate) enum PartitionScheme {
    /// Simple modulo partitioning: `fp.0 % num_partitions`.
    ///
    /// Properties:
    /// - O(1) lookup
    /// - Deterministic: same fp always maps to same partition
    /// - Uniform distribution (FNV-1a fingerprints are well-distributed)
    /// - Fixed partition count — cannot add/remove partitions dynamically
    Modulo { num_partitions: usize },

    /// Consistent hashing ring with virtual nodes.
    ///
    /// Each physical partition gets `vnodes_per_partition` points on a u64 ring.
    /// Lookup: binary search for the first ring point >= fp, wrapping around.
    ///
    /// Properties:
    /// - O(log(V)) lookup where V = total virtual nodes
    /// - Adding/removing a partition redistributes ~1/N keys (not all keys)
    /// - Requires sorted ring construction at setup time
    ConsistentHash {
        /// Sorted ring of (ring_position, partition_index) pairs.
        ring: Vec<(u64, usize)>,
        /// Number of physical partitions.
        num_partitions: usize,
    },
}

impl PartitionScheme {
    /// Create a modulo partition scheme with the given number of partitions.
    ///
    /// # Panics
    /// Panics if `num_partitions` is zero.
    pub(crate) fn modulo(num_partitions: usize) -> Self {
        assert!(num_partitions > 0, "num_partitions must be > 0");
        PartitionScheme::Modulo { num_partitions }
    }

    /// Create a consistent-hashing partition scheme.
    ///
    /// Uses FNV-1a to place `vnodes_per_partition` virtual nodes per partition
    /// on the u64 ring. Higher vnode counts give better load balance at the
    /// cost of larger ring (and thus slower lookup).
    ///
    /// # Panics
    /// Panics if `num_partitions` is zero or `vnodes_per_partition` is zero.
    pub(crate) fn consistent_hash(num_partitions: usize, vnodes_per_partition: usize) -> Self {
        assert!(num_partitions > 0, "num_partitions must be > 0");
        assert!(vnodes_per_partition > 0, "vnodes_per_partition must be > 0");

        let mut ring = Vec::with_capacity(num_partitions * vnodes_per_partition);
        for partition in 0..num_partitions {
            for vnode in 0..vnodes_per_partition {
                // Hash (partition, vnode) pair to get ring position.
                // Use FNV-1a to match the fingerprint hash family.
                let mut h: u64 = 0xcbf29ce484222325; // FNV offset basis
                let p_bytes = (partition as u64).to_le_bytes();
                let v_bytes = (vnode as u64).to_le_bytes();
                for &b in p_bytes.iter().chain(v_bytes.iter()) {
                    h ^= b as u64;
                    h = h.wrapping_mul(0x100000001b3); // FNV prime
                }
                ring.push((h, partition));
            }
        }
        ring.sort_unstable_by_key(|&(pos, _)| pos);

        PartitionScheme::ConsistentHash {
            ring,
            num_partitions,
        }
    }

    /// Map a fingerprint to its owning partition index.
    #[inline]
    pub(crate) fn partition_for_fp(&self, fp: Fingerprint) -> usize {
        match self {
            PartitionScheme::Modulo { num_partitions } => (fp.0 as usize) % num_partitions,
            PartitionScheme::ConsistentHash { ring, .. } => {
                // Binary search for the first ring point >= fp.0
                match ring.binary_search_by_key(&fp.0, |&(pos, _)| pos) {
                    Ok(idx) => ring[idx].1,
                    Err(idx) => {
                        if idx < ring.len() {
                            ring[idx].1
                        } else {
                            // Wrap around to first ring entry
                            ring[0].1
                        }
                    }
                }
            }
        }
    }

    /// Number of partitions in the scheme.
    pub(crate) fn num_partitions(&self) -> usize {
        match self {
            PartitionScheme::Modulo { num_partitions } => *num_partitions,
            PartitionScheme::ConsistentHash { num_partitions, .. } => *num_partitions,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_modulo_partition_deterministic() {
        let scheme = PartitionScheme::modulo(4);
        // Same fp always maps to same partition
        let fp = Fingerprint(12345);
        let p1 = scheme.partition_for_fp(fp);
        let p2 = scheme.partition_for_fp(fp);
        assert_eq!(p1, p2);
    }

    #[test]
    fn test_modulo_partition_range() {
        let scheme = PartitionScheme::modulo(4);
        // All partitions within [0, 4)
        for i in 0..1000u64 {
            let p = scheme.partition_for_fp(Fingerprint(i));
            assert!(p < 4, "partition {p} out of range for fp {i}");
        }
    }

    #[test]
    fn test_modulo_partition_distribution() {
        let scheme = PartitionScheme::modulo(4);
        let mut counts = [0usize; 4];
        // Use well-distributed fingerprints (simulating FNV output)
        for i in 0..10000u64 {
            // Mix the bits to simulate real fingerprint distribution
            let fp = Fingerprint(i.wrapping_mul(0x517cc1b727220a95));
            counts[scheme.partition_for_fp(fp)] += 1;
        }
        // Each partition should get roughly 2500. Allow 20% variance.
        for (idx, &count) in counts.iter().enumerate() {
            assert!(
                count > 2000 && count < 3000,
                "partition {idx} got {count} states (expected ~2500)"
            );
        }
    }

    #[test]
    fn test_consistent_hash_partition_range() {
        let scheme = PartitionScheme::consistent_hash(4, 100);
        for i in 0..1000u64 {
            let p = scheme.partition_for_fp(Fingerprint(i));
            assert!(p < 4, "partition {p} out of range for fp {i}");
        }
    }

    #[test]
    fn test_consistent_hash_partition_deterministic() {
        let scheme = PartitionScheme::consistent_hash(4, 100);
        let fp = Fingerprint(99999);
        let p1 = scheme.partition_for_fp(fp);
        let p2 = scheme.partition_for_fp(fp);
        assert_eq!(p1, p2);
    }

    #[test]
    fn test_consistent_hash_distribution() {
        let scheme = PartitionScheme::consistent_hash(4, 1024);
        let mut counts = [0usize; 4];
        for i in 0..10000u64 {
            let fp = Fingerprint(i.wrapping_mul(0x517cc1b727220a95));
            counts[scheme.partition_for_fp(fp)] += 1;
        }
        // Consistent hashing with 1024 vnodes per partition.
        // Allow wide variance -- inherently less uniform than modulo.
        for (idx, &count) in counts.iter().enumerate() {
            assert!(
                count > 500 && count < 5000,
                "partition {idx} got {count} states (expected ~2500)"
            );
        }
    }

    #[test]
    fn test_num_partitions() {
        let modulo = PartitionScheme::modulo(8);
        assert_eq!(modulo.num_partitions(), 8);

        let ch = PartitionScheme::consistent_hash(6, 50);
        assert_eq!(ch.num_partitions(), 6);
    }

    #[test]
    #[should_panic(expected = "num_partitions must be > 0")]
    fn test_modulo_zero_panics() {
        PartitionScheme::modulo(0);
    }

    #[test]
    #[should_panic(expected = "num_partitions must be > 0")]
    fn test_consistent_hash_zero_partitions_panics() {
        PartitionScheme::consistent_hash(0, 100);
    }
}
