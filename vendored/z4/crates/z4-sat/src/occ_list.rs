// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared occurrence list for SAT inprocessing (subsumption, BCE, BVE).
//!
//! Tracks which clauses contain each literal. Used during preprocessing
//! and inprocessing passes to efficiently find clauses that share literals.

use crate::literal::Literal;

/// Occurrence list mapping literals to clause indices.
///
/// For each literal (indexed by `2*var + polarity`), stores the set of
/// clause indices that contain that literal.
#[derive(Debug, Clone)]
pub(crate) struct OccList {
    /// For each literal index, the list of clause indices containing that literal.
    pub(crate) occ: Vec<Vec<usize>>,
}

impl OccList {
    /// Create a new occurrence list for `num_vars` variables.
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            occ: vec![Vec::new(); num_vars * 2],
        }
    }

    /// Ensure the occurrence list can index literals for `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        let target = num_vars.saturating_mul(2);
        if self.occ.len() < target {
            self.occ.resize_with(target, Vec::new);
        }
    }

    /// Add a clause to occurrence lists for all its literals.
    pub(crate) fn add_clause(&mut self, clause_idx: usize, literals: &[Literal]) {
        for &lit in literals {
            let idx = lit.index();
            if idx < self.occ.len() {
                self.occ[idx].push(clause_idx);
            }
        }
    }

    /// Remove a clause from occurrence lists for all its literals.
    ///
    /// O(L * max_occ) where L = clause length, max_occ = longest occurrence list.
    /// Uses linear scan to find position, then `swap_remove` for O(1) removal.
    pub(crate) fn remove_clause(&mut self, clause_idx: usize, literals: &[Literal]) {
        for &lit in literals {
            let idx = lit.index();
            if idx < self.occ.len() {
                if let Some(pos) = self.occ[idx].iter().position(|&c| c == clause_idx) {
                    self.occ[idx].swap_remove(pos);
                }
            }
        }
    }

    /// Get clause indices containing a literal.
    pub(crate) fn get(&self, lit: Literal) -> &[usize] {
        let idx = lit.index();
        if idx < self.occ.len() {
            &self.occ[idx]
        } else {
            &[]
        }
    }

    /// Get number of clauses containing a literal.
    pub(crate) fn count(&self, lit: Literal) -> usize {
        self.get(lit).len()
    }

    /// Swap the element at `pos` to the front of the occurrence list for `lit`.
    ///
    /// Used by CCE's CLA move-to-front heuristic: when a clause kills the
    /// intersection early, move it to front so future iterations abort faster.
    /// CaDiCaL cover.cpp:286-292.
    pub(crate) fn swap_to_front(&mut self, lit: Literal, pos: usize) {
        let idx = lit.index();
        if idx < self.occ.len() && pos > 0 && pos < self.occ[idx].len() {
            self.occ[idx].swap(0, pos);
        }
    }

    /// Sort each non-empty occurrence list using a caller-provided key function.
    ///
    /// Used by CCE to sort occurrence lists by clause size ascending
    /// so that CLA intersects smaller clauses first (CaDiCaL cover.cpp:608).
    pub(crate) fn sort_each_by_key<F>(&mut self, key_fn: F)
    where
        F: Fn(usize) -> usize,
    {
        for list in &mut self.occ {
            if list.len() > 1 {
                list.sort_unstable_by_key(|&clause_idx| key_fn(clause_idx));
            }
        }
    }

    /// Clear all occurrence lists.
    pub(crate) fn clear(&mut self) {
        for list in &mut self.occ {
            list.clear();
        }
    }
}

#[cfg(test)]
#[path = "occ_list_tests.rs"]
mod tests;
