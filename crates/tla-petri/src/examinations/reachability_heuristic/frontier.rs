// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Frontier storage primitives for heuristic best-first search.
//!
//! Contains the scored marking wrapper for the priority queue and an inline
//! Bloom filter for approximate visited-state tracking.

use std::rc::Rc;

use crate::petri_net::TransitionIdx;

// ---------------------------------------------------------------------------
// Queue-owned trace chains and scored frontier entries
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub(super) struct TraceNode {
    pub(super) parent: Option<Rc<TraceNode>>,
    pub(super) via: TransitionIdx,
}

#[derive(Debug, Clone)]
pub(super) struct ScoredNode {
    pub(super) score: u64,
    pub(super) marking: Vec<u64>,
    pub(super) trace: Option<Rc<TraceNode>>,
}

impl PartialEq for ScoredNode {
    fn eq(&self, other: &Self) -> bool {
        self.score == other.score
    }
}

impl Eq for ScoredNode {}

impl PartialOrd for ScoredNode {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ScoredNode {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.score.cmp(&other.score)
    }
}

// ---------------------------------------------------------------------------
// Inline Bloom Filter
// ---------------------------------------------------------------------------

/// Simple Bloom filter using two hash functions for approximate set membership.
///
/// Uses ~10 bits per expected entry. False positives are safe for witness
/// search (we skip a state, but never report a false witness).
pub(super) struct BloomFilter {
    bits: Vec<u64>,
    num_bits: usize,
    hasher_state: (u64, u64),
}

impl BloomFilter {
    pub(super) fn new(expected_entries: usize) -> Self {
        // ~10 bits per entry for ~1% false positive rate.
        let num_bits = (expected_entries * 10).max(64);
        let num_words = num_bits.div_ceil(64);
        // Use two random seeds for the two hash functions.
        let hasher_state = (0x517c_c1b7_2722_0a95_u64, 0x6c62_272e_07bb_0142_u64);
        BloomFilter {
            bits: vec![0u64; num_words],
            num_bits,
            hasher_state,
        }
    }

    pub(super) fn insert(&mut self, marking: &[u64]) {
        let (h1, h2) = self.hash_pair(marking);
        let idx1 = (h1 as usize) % self.num_bits;
        let idx2 = (h2 as usize) % self.num_bits;
        self.bits[idx1 / 64] |= 1u64 << (idx1 % 64);
        self.bits[idx2 / 64] |= 1u64 << (idx2 % 64);
    }

    pub(super) fn probably_contains(&self, marking: &[u64]) -> bool {
        let (h1, h2) = self.hash_pair(marking);
        let idx1 = (h1 as usize) % self.num_bits;
        let idx2 = (h2 as usize) % self.num_bits;
        (self.bits[idx1 / 64] & (1u64 << (idx1 % 64))) != 0
            && (self.bits[idx2 / 64] & (1u64 << (idx2 % 64))) != 0
    }

    fn hash_pair(&self, marking: &[u64]) -> (u64, u64) {
        let h1 = self.hash_with_seed(marking, self.hasher_state.0);
        let h2 = self.hash_with_seed(marking, self.hasher_state.1);
        (h1, h2)
    }

    fn hash_with_seed(&self, marking: &[u64], seed: u64) -> u64 {
        // FNV-1a inspired hash with seed mixing.
        let mut h = seed;
        for &token in marking {
            h ^= token;
            h = h.wrapping_mul(0x100000001b3);
        }
        h
    }
}
