// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Symmetry reduction operations for `State`.
//!
//! Extracted from `state.rs` (#3607). Contains permutation application and
//! canonical fingerprinting under symmetry groups.

use std::cmp::Ordering;
use std::sync::Arc;

#[cfg(debug_assertions)]
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};

use crate::value::{FuncValue, MVPerm};
use crate::Value;
use tla_core::kani_types::OrdMap;

use super::value_hash::compute_fingerprint_from_min_vals;
use super::{Fingerprint, State};

// Profiling counters for symmetry fingerprinting — debug builds only
#[cfg(debug_assertions)]
static SYMMETRY_FP_CALLS: AtomicU64 = AtomicU64::new(0);
#[cfg(debug_assertions)]
static SYMMETRY_FP_US: AtomicU64 = AtomicU64::new(0);

/// Print and reset symmetry fingerprinting statistics.
/// In release builds, this is a no-op (counters don't exist).
#[cfg(debug_assertions)]
pub(crate) fn print_symmetry_stats() {
    let calls = SYMMETRY_FP_CALLS.swap(0, AtomicOrdering::Relaxed);
    let us = SYMMETRY_FP_US.swap(0, AtomicOrdering::Relaxed);
    if calls > 0 {
        eprintln!(
            "=== Symmetry Fingerprint Profile ===\n  Calls: {}\n  Time: {:.3}s\n  Avg: {:.1}µs/call",
            calls,
            us as f64 / 1_000_000.0,
            us as f64 / calls as f64
        );
    }
}
#[cfg(not(debug_assertions))]
pub(crate) fn print_symmetry_stats() {}

impl State {
    /// Compute the canonical fingerprint under symmetry permutations
    ///
    /// For symmetry reduction, we need to identify symmetric states as equivalent.
    /// This is done by finding the lexicographically smallest permuted state
    /// and returning its fingerprint (TLC-compatible algorithm).
    ///
    /// IMPORTANT: We find lexmin(S, P1(S), P2(S), ...) then fingerprint it.
    /// NOT min(fp(S), fp(P1(S)), ...) - fingerprint order != lexicographic order!
    ///
    /// If `perms` is empty, returns the regular fingerprint.
    /// Results are cached for efficiency when called multiple times on the same state.
    ///
    /// # Algorithm
    ///
    /// Implements TLC's interleaved permute-compare pattern (TLCStateMut.java:212-247):
    /// - Permutes one variable at a time, comparing immediately
    /// - Early exits (`continue 'next_perm`) when permuted > min
    /// - Reuses work buffers instead of allocating per permutation
    ///
    /// This is critical for performance: most states skip most permutations after
    /// comparing just 1-2 variables, avoiding O(|perms| × |vars|) work.
    pub fn fingerprint_with_symmetry(&self, perms: &[FuncValue]) -> Fingerprint {
        if perms.is_empty() {
            return self.fingerprint();
        }

        // Return cached value if available
        if let Some(&cached) = self.canonical_fingerprint.get() {
            return cached;
        }

        #[cfg(debug_assertions)]
        let start = std::time::Instant::now();
        #[cfg(debug_assertions)]
        SYMMETRY_FP_CALLS.fetch_add(1, AtomicOrdering::Relaxed);

        // TLC-style algorithm: interleaved permute-compare with early exit
        let var_count = self.vars.len();

        // Convert to Vec for indexed access (OrdMap iterates in sorted order)
        let vars_vec: Vec<(&Arc<str>, &Value)> = self.vars.iter().collect();

        // Pre-allocate work buffers - reused across permutations (TLC optimization)
        let mut min_vals: Vec<Value> = vars_vec.iter().map(|(_, v)| (*v).clone()).collect();
        let mut work_vals: Vec<Value> = Vec::with_capacity(var_count);

        'next_perm: for perm in perms {
            work_vals.clear();
            let mut cmp = Ordering::Equal;

            for (i, (_, value)) in vars_vec.iter().enumerate() {
                let permuted = value.permute(perm);

                // TLC pattern: compare as we go, early exit if greater
                if cmp == Ordering::Equal {
                    cmp = permuted.cmp(&min_vals[i]);
                    if cmp == Ordering::Greater {
                        // This permutation can't be minimum - skip remaining vars
                        continue 'next_perm;
                    }
                }
                // Always store (needed if this becomes new minimum)
                work_vals.push(permuted);
            }

            // If this permutation is strictly less than current min, swap buffers
            if cmp == Ordering::Less {
                std::mem::swap(&mut min_vals, &mut work_vals);
            }
        }

        // Compute fingerprint from the minimum values
        // Uses same algorithm as compute_fingerprint but with our Vec
        let canonical_fp = compute_fingerprint_from_min_vals(&vars_vec, &min_vals);

        // Cache the result (ignore if another thread beat us to it)
        let _ = self.canonical_fingerprint.set(canonical_fp);

        #[cfg(debug_assertions)]
        SYMMETRY_FP_US.fetch_add(start.elapsed().as_micros() as u64, AtomicOrdering::Relaxed);
        canonical_fp
    }

    /// Compute the canonical fingerprint using MVPerm for O(1) lookups (Part of #358).
    ///
    /// This is 10x faster than `fingerprint_with_symmetry()` for specs with many
    /// model values because MVPerm uses array indexing instead of binary search.
    pub fn fingerprint_with_symmetry_fast(&self, mvperms: &[MVPerm]) -> Fingerprint {
        if mvperms.is_empty() {
            return self.fingerprint();
        }

        // Return cached value if available
        if let Some(&cached) = self.canonical_fingerprint.get() {
            return cached;
        }

        #[cfg(debug_assertions)]
        let start = std::time::Instant::now();
        #[cfg(debug_assertions)]
        SYMMETRY_FP_CALLS.fetch_add(1, AtomicOrdering::Relaxed);

        // TLC-style algorithm: interleaved permute-compare with early exit
        let var_count = self.vars.len();

        // Convert to Vec for indexed access (OrdMap iterates in sorted order)
        let vars_vec: Vec<(&Arc<str>, &Value)> = self.vars.iter().collect();

        // Pre-allocate work buffers - reused across permutations (TLC optimization)
        let mut min_vals: Vec<Value> = vars_vec.iter().map(|(_, v)| (*v).clone()).collect();
        let mut work_vals: Vec<Value> = Vec::with_capacity(var_count);

        'next_perm: for mvperm in mvperms {
            work_vals.clear();
            let mut cmp = Ordering::Equal;

            for (i, (_, value)) in vars_vec.iter().enumerate() {
                // O(1) permutation via MVPerm instead of O(log n) binary search
                let permuted = value.permute_fast(mvperm);

                // TLC pattern: compare as we go, early exit if greater
                if cmp == Ordering::Equal {
                    cmp = permuted.cmp(&min_vals[i]);
                    if cmp == Ordering::Greater {
                        // This permutation can't be minimum - skip remaining vars
                        continue 'next_perm;
                    }
                }
                // Always store (needed if this becomes new minimum)
                work_vals.push(permuted);
            }

            // If this permutation is strictly less than current min, swap buffers
            if cmp == Ordering::Less {
                std::mem::swap(&mut min_vals, &mut work_vals);
            }
        }

        // Compute fingerprint from the minimum values
        // Uses same algorithm as compute_fingerprint but with our Vec
        let canonical_fp = compute_fingerprint_from_min_vals(&vars_vec, &min_vals);

        // Cache the result (ignore if another thread beat us to it)
        let _ = self.canonical_fingerprint.set(canonical_fp);

        #[cfg(debug_assertions)]
        SYMMETRY_FP_US.fetch_add(start.elapsed().as_micros() as u64, AtomicOrdering::Relaxed);
        canonical_fp
    }

    /// Apply a permutation to all values in this state
    ///
    /// Returns a new state with all model values permuted according to the given
    /// permutation function. Used for symmetry reduction.
    pub fn permute(&self, perm: &FuncValue) -> State {
        let permuted_vars: OrdMap<Arc<str>, Value> = self
            .vars
            .iter()
            .map(|(name, value)| (name.clone(), value.permute(perm)))
            .collect();
        State::from_vars(permuted_vars)
    }

    /// Apply a permutation using MVPerm for O(1) lookups (Part of #358).
    pub fn permute_fast(&self, mvperm: &MVPerm) -> State {
        let permuted_vars: OrdMap<Arc<str>, Value> = self
            .vars
            .iter()
            .map(|(name, value)| (name.clone(), value.permute_fast(mvperm)))
            .collect();
        State::from_vars(permuted_vars)
    }
}
