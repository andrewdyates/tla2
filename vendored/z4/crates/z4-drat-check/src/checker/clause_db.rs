// Copyright 2026 Andrew Yates
// Hash-based clause database for the DRAT proof checker.
// XOR hash for order-independent clause matching, power-of-two buckets.

use crate::literal::Literal;

use super::{DratChecker, Watch};

impl DratChecker {
    pub(super) fn hash_clause(clause: &[Literal]) -> u64 {
        let mut h: u64 = 0;
        for &lit in clause {
            h ^= (lit.index() as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
        }
        h
    }

    pub(super) fn bucket_idx(&self, hash: u64) -> usize {
        assert!(
            self.hash_buckets.len().is_power_of_two(),
            "BUG: hash_buckets.len() = {} is not a power of two",
            self.hash_buckets.len()
        );
        (hash as usize) & (self.hash_buckets.len() - 1)
    }

    pub(super) fn maybe_rehash(&mut self) {
        if self.live_clauses <= self.hash_buckets.len() {
            return;
        }
        let new_cap = match self.hash_buckets.len().checked_mul(2) {
            Some(c) => c,
            None => return, // usize overflow — keep current capacity
        };
        let mut new_buckets = vec![Vec::new(); new_cap];
        let mask = new_cap - 1;
        for bucket in &self.hash_buckets {
            for &cidx in bucket {
                if let Some(ref clause) = self.clauses[cidx] {
                    let hash = Self::hash_clause(clause);
                    new_buckets[(hash as usize) & mask].push(cidx);
                }
            }
        }
        self.hash_buckets = new_buckets;
    }

    pub(super) fn insert_clause(&mut self, clause: Vec<Literal>) -> usize {
        let cidx = self.clauses.len();
        if clause.is_empty() {
            // Empty clause cannot be hashed or watched. Caller should handle
            // the empty-clause case (UNSAT) before reaching insert_clause.
            // Previously a debug_assert that silently passed in release builds,
            // leaving a corrupt entry in the hash table (no watch literals,
            // zero-hash bucket collision).
            self.clauses.push(Some(clause));
            return cidx;
        }
        for &lit in &clause {
            self.ensure_capacity(lit.variable().index());
        }
        if clause.len() >= 2 {
            let (c0, c1) = (clause[0], clause[1]);
            self.watches[c0.index()].push(Watch {
                blocking: c1,
                clause_idx: cidx,
                core: false,
            });
            self.watches[c1.index()].push(Watch {
                blocking: c0,
                clause_idx: cidx,
                core: false,
            });
        }
        let bucket = self.bucket_idx(Self::hash_clause(&clause));
        self.hash_buckets[bucket].push(cidx);
        self.live_clauses += 1;
        self.clauses.push(Some(clause));
        self.maybe_rehash();
        cidx
    }

    /// Find a clause index matching the given literal set (order-independent).
    pub(crate) fn find_clause_idx(&self, clause: &[Literal]) -> Option<usize> {
        let hash = Self::hash_clause(clause);
        let bucket = self.bucket_idx(hash);
        for &cidx in &self.hash_buckets[bucket] {
            if let Some(ref stored) = self.clauses[cidx] {
                if stored.len() == clause.len() && clause.iter().all(|lit| stored.contains(lit)) {
                    return Some(cidx);
                }
            }
        }
        None
    }
}
