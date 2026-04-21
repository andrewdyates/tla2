// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conflict analysis (1UIP learning)
//!
//! Implements the First Unique Implication Point (1UIP) scheme for
//! conflict-driven clause learning.

use crate::literal::Literal;
use crate::solver::VarData;

/// Result of conflict analysis
#[derive(Debug, Clone)]
pub(crate) struct ConflictResult {
    /// The learned clause (first literal is the asserting literal)
    pub(crate) learned_clause: Vec<Literal>,
    /// The backtrack level
    pub(crate) backtrack_level: u32,
    /// The LBD (Literal Block Distance) of the learned clause
    pub(crate) lbd: u32,
    /// Resolution chain (clause IDs used to derive the learned clause)
    /// Used for LRAT proof generation. Empty if LRAT is not enabled.
    pub(crate) resolution_chain: Vec<u64>,
    /// OTFS Branch B: when set, the strengthened clause already exists in the
    /// clause DB and should be used as the driving clause directly. The caller
    /// must skip `add_learned_clause` and use this ClauseRef for `enqueue`.
    /// CaDiCaL reference: analyze.cpp:1109-1127.
    pub(crate) otfs_driving_clause: Option<crate::watched::ClauseRef>,
}

/// Conflict analyzer
#[derive(Debug, Default)]
pub(crate) struct ConflictAnalyzer {
    /// Indices to clear in VarData.flags seen bit (sparse clear optimization).
    /// Seen marks are stored in VarData.flags for cache locality (#6994).
    pub(crate) seen_to_clear: Vec<usize>,
    /// Debug-only count of currently marked variables.
    ///
    /// Keeps postcondition checks O(1) instead of scanning the full vector
    /// after every conflict.
    #[cfg(debug_assertions)]
    seen_true_count: usize,
    /// Temporary learned clause being built (without the UIP)
    learned: Vec<Literal>,
    /// The asserting literal (UIP negated)
    asserting_lit: Option<Literal>,
    /// Resolution chain (clause IDs used during analysis)
    pub(crate) resolution_chain: Vec<u64>,
    /// Workspace for LBD computation (reused to avoid allocations)
    lbd_seen: Vec<bool>,
    /// Indices to clear in lbd_seen after LBD computation
    lbd_to_clear: Vec<usize>,
    /// Reusable buffer for clause literals during conflict analysis
    clause_buf: Vec<Literal>,
}

impl ConflictAnalyzer {
    /// Create a new conflict analyzer
    pub(crate) fn new(_num_vars: usize) -> Self {
        Self {
            seen_to_clear: Vec::new(),
            #[cfg(debug_assertions)]
            seen_true_count: 0,
            learned: Vec::new(),
            asserting_lit: None,
            resolution_chain: Vec::new(),
            lbd_seen: Vec::new(),
            lbd_to_clear: Vec::new(),
            clause_buf: Vec::new(),
        }
    }

    /// Ensure the analyzer can track `num_vars` variables.
    /// Seen marks are now stored in VarData.flags, so no resizing needed here.
    pub(crate) fn ensure_num_vars(&mut self, _num_vars: usize) {}

    /// Clear the analyzer state for a new conflict.
    /// Uses sparse clear - O(marked) instead of O(num_vars).
    /// Seen marks are stored in `var_data[i].flags` for cache locality (#6994).
    pub(crate) fn clear(&mut self, var_data: &mut [VarData]) {
        // Sparse clear - only reset indices that were actually marked
        for &idx in &self.seen_to_clear {
            #[cfg(debug_assertions)]
            if var_data[idx].is_seen() {
                self.seen_true_count = self
                    .seen_true_count
                    .checked_sub(1)
                    .expect("seen_true_count underflow during sparse clear");
            }
            var_data[idx].set_seen(false);
        }
        self.seen_to_clear.clear();
        self.learned.clear();
        self.asserting_lit = None;
        self.resolution_chain.clear();
        // CaDiCaL analyze.cpp:1200-1210 -- postcondition: all seen marks are
        // cleared after sparse clear.
        #[cfg(debug_assertions)]
        debug_assert_eq!(
            self.seen_true_count, 0,
            "BUG: seen marks not fully cleared after ConflictAnalyzer::clear(); \
             missing mark/unmark bookkeeping or stale seen_to_clear entries"
        );
    }

    /// Add a clause ID to the resolution chain (for LRAT proofs).
    /// No dedup at this level — the same clause ID may legitimately appear
    /// at multiple positions when reached via different stages (1UIP,
    /// minimize, unit chain). Dedup is applied at the proof output boundary
    /// in `ProofManager::emit_add` (#5248).
    #[inline]
    pub(crate) fn add_to_chain(&mut self, clause_id: u64) {
        self.resolution_chain.push(clause_id);
    }

    /// Mark a variable as seen and track for sparse clear.
    /// Seen mark stored in `var_data[var].flags` for cache locality (#6994).
    #[inline]
    pub(crate) fn mark_seen(&mut self, var: usize, var_data: &mut [VarData]) {
        debug_assert!(
            var < var_data.len(),
            "BUG: mark_seen variable index {var} out of bounds (num_vars={})",
            var_data.len()
        );
        if !var_data[var].is_seen() {
            var_data[var].set_seen(true);
            self.seen_to_clear.push(var);
            #[cfg(debug_assertions)]
            {
                self.seen_true_count += 1;
            }
        }
    }

    /// Unmark a variable as seen.
    /// Not used in production (CaDiCaL keeps seen flags until end of analysis),
    /// but retained for test coverage of the mark/unmark lifecycle.
    #[inline]
    #[cfg(test)]
    pub(crate) fn unmark_seen(&mut self, var: usize, var_data: &mut [VarData]) {
        debug_assert!(
            var < var_data.len(),
            "BUG: unmark_seen variable index {var} out of bounds (num_vars={})",
            var_data.len()
        );
        if var_data[var].is_seen() {
            var_data[var].set_seen(false);
            #[cfg(debug_assertions)]
            {
                self.seen_true_count = self
                    .seen_true_count
                    .checked_sub(1)
                    .expect("seen_true_count underflow during unmark");
            }
        }
    }

    /// Check if a variable is seen.
    #[inline]
    pub(crate) fn is_seen(&self, var: usize, var_data: &[VarData]) -> bool {
        debug_assert!(
            var < var_data.len(),
            "BUG: is_seen variable index {var} out of bounds (num_vars={})",
            var_data.len()
        );
        var_data[var].is_seen()
    }

    /// Access the analyzed variable list (all vars marked during analysis).
    /// Used for post-analysis sorted VMTF bumping (CaDiCaL analyze.cpp:189-194).
    #[inline]
    pub(crate) fn analyzed_vars(&self) -> &[usize] {
        &self.seen_to_clear
    }

    /// Rollback the analyzed variable list to a saved size.
    ///
    /// CaDiCaL analyze.cpp:410-417: when reason bumping exceeds its limit,
    /// clear the `seen` flag for all variables added since `saved_size` and
    /// truncate the list. This prevents the extra reason-side variables from
    /// being bumped in `bump_analyzed_variables()`.
    pub(crate) fn rollback_analyzed(&mut self, saved_size: usize, var_data: &mut [VarData]) {
        debug_assert!(
            saved_size <= self.seen_to_clear.len(),
            "BUG: rollback_analyzed saved_size ({saved_size}) > current len ({})",
            self.seen_to_clear.len()
        );
        for i in saved_size..self.seen_to_clear.len() {
            let var = self.seen_to_clear[i];
            debug_assert!(var_data[var].is_seen(), "BUG: rollback var {var} not seen");
            var_data[var].set_seen(false);
            #[cfg(debug_assertions)]
            {
                self.seen_true_count = self
                    .seen_true_count
                    .checked_sub(1)
                    .expect("seen_true_count underflow during rollback");
            }
        }
        self.seen_to_clear.truncate(saved_size);
    }

    /// Add a literal to the learned clause
    #[inline]
    pub(crate) fn add_to_learned(&mut self, lit: Literal) {
        debug_assert!(
            !self.learned.contains(&lit),
            "BUG: duplicate literal {} added to learned clause",
            lit.to_dimacs()
        );
        debug_assert!(
            self.asserting_lit != Some(lit),
            "BUG: learned literal {} duplicates the asserting literal",
            lit.to_dimacs()
        );
        self.learned.push(lit);
    }

    /// Set the asserting literal (the 1UIP negated)
    #[inline]
    pub(crate) fn set_asserting_literal(&mut self, lit: Literal) {
        debug_assert!(
            self.asserting_lit.is_none(),
            "BUG: asserting literal set twice (was {:?}, now {})",
            self.asserting_lit.map(Literal::to_dimacs),
            lit.to_dimacs()
        );
        self.asserting_lit = Some(lit);
    }

    /// Retain only learned literals where the predicate returns true.
    /// Compacts in-place without heap allocation (like `Vec::retain`).
    #[inline]
    pub(crate) fn retain_learned(&mut self, mut f: impl FnMut(Literal) -> bool) {
        self.learned.retain(|&lit| f(lit));
    }

    /// Replace the learned clause with a new set of literals (used by shrink).
    pub(crate) fn replace_learned(&mut self, lits: &[Literal]) {
        self.learned.clear();
        self.learned.extend_from_slice(lits);
    }

    /// Get the asserting literal (1UIP negated)
    #[inline]
    pub(crate) fn asserting_literal(&self) -> Literal {
        self.asserting_lit
            .expect("asserting_literal called before set")
    }

    /// Get learned literal count (avoids borrow when iterating by index)
    #[inline]
    pub(crate) fn learned_count(&self) -> usize {
        self.learned.len()
    }

    /// Get learned literal at index (avoids borrow when iterating by index)
    #[inline]
    pub(crate) fn learned_at(&self, i: usize) -> Literal {
        self.learned[i]
    }

    /// Get mutable access to the clause buffer for reuse in conflict analysis
    #[inline]
    pub(crate) fn clause_buf_mut(&mut self) -> &mut Vec<Literal> {
        &mut self.clause_buf
    }

    /// Compute the backtrack level from the learned clause.
    /// This is the second-highest decision level among the literals,
    /// or 0 if the learned clause is unit.
    pub(crate) fn compute_backtrack_level(&self, var_data: &[VarData]) -> u32 {
        if self.learned.is_empty() {
            // Unit learned clause - backtrack to level 0
            return 0;
        }

        // Find the highest level among non-asserting literals
        let mut max_level = 0;
        for &lit in &self.learned {
            let var_level = var_data[lit.variable().index()].level;
            if var_level > max_level {
                max_level = var_level;
            }
        }
        max_level
    }

    /// Compute LBD for an arbitrary clause (e.g. OTFS strengthened, or bump recompute).
    /// Counts ALL distinct levels including level 0, matching CaDiCaL's `recompute_glue`
    /// (analyze.cpp:206-219) which also counts all levels without subtraction.
    /// Uses the same sparse-clear workspace as `compute_lbd`.
    ///
    /// Currently used only in tests; will be called from OTFS strengthening and
    /// ChrBT LBD recompute (#6998) once those land.
    #[cfg(test)]
    pub(crate) fn compute_lbd_for_clause(&mut self, lits: &[Literal], var_data: &[VarData]) -> u32 {
        if self.lbd_seen.len() < var_data.len() + 1 {
            self.lbd_seen.resize(var_data.len() + 1, false);
        }
        let mut count = 0u32;
        for &lit in lits {
            let lvl = var_data[lit.variable().index()].level as usize;
            if !self.lbd_seen[lvl] {
                self.lbd_seen[lvl] = true;
                self.lbd_to_clear.push(lvl);
                count += 1;
            }
        }
        for &idx in &self.lbd_to_clear {
            self.lbd_seen[idx] = false;
        }
        self.lbd_to_clear.clear();
        count.max(1)
    }

    /// Compute the LBD (Literal Block Distance / glue) of the learned clause.
    ///
    /// Matches CaDiCaL's convention (analyze.cpp:1193): `glue = levels.size() - 1`.
    /// CaDiCaL counts all distinct levels during analysis (including the conflict
    /// level), then subtracts 1. The conflict level is always present since at
    /// least one literal in the conflict is at the current decision level.
    /// The subtraction excludes this level, measuring how many "decision blocks"
    /// below the conflict the clause depends on.
    ///
    /// All CaDiCaL tier thresholds (reducetier1glue=2, reducetier2glue=6) are
    /// calibrated to this convention. Z4's CORE_LBD=2 and TIER1_LBD=6 must use
    /// the same convention to classify clauses equivalently.
    pub(crate) fn compute_lbd(&mut self, var_data: &[VarData]) -> u32 {
        let mut count = 0u32;

        // Ensure workspace is large enough for all decision levels
        if self.lbd_seen.len() < var_data.len() + 1 {
            self.lbd_seen.resize(var_data.len() + 1, false);
        }

        // Add asserting literal's level (this is the conflict level)
        if let Some(lit) = self.asserting_lit {
            let lvl = var_data[lit.variable().index()].level as usize;
            if !self.lbd_seen[lvl] {
                self.lbd_seen[lvl] = true;
                self.lbd_to_clear.push(lvl);
                count += 1;
            }
        }

        // Add other literals' levels
        for &lit in &self.learned {
            let lvl = var_data[lit.variable().index()].level as usize;
            if !self.lbd_seen[lvl] {
                self.lbd_seen[lvl] = true;
                self.lbd_to_clear.push(lvl);
                count += 1;
            }
        }

        // Clear workspace for next call
        for &idx in &self.lbd_to_clear {
            self.lbd_seen[idx] = false;
        }
        self.lbd_to_clear.clear();

        // CaDiCaL: glue = levels.size() - 1 (analyze.cpp:1193). Subtract 1 to
        // exclude the conflict level. The asserting literal is always present,
        // so count >= 1 for non-empty clauses, making the subtraction safe.
        // Unit clauses get glue 0; glue < clause_size (analyze.cpp:1199).
        count.saturating_sub(1)
    }

    /// Get the final conflict result.
    /// Builds the learned clause in-place (UIP prepend + mem::take) to reuse
    /// the Vec's heap capacity across conflicts. CaDiCaL: persistent `clause`
    /// member in internal.hpp, cleared but never freed between conflicts.
    pub(crate) fn get_result(&mut self, backtrack_level: u32, lbd: u32) -> ConflictResult {
        debug_assert!(
            self.asserting_lit.is_some(),
            "BUG: get_result called without asserting literal set"
        );

        // Prepend asserting literal to self.learned in-place.
        // insert(0, lit) shifts elements right by 1 — O(n) on a warm cache line
        // (just written during analysis), replacing the O(n) memcpy that previously
        // created a fresh Vec. Net cost: same O(n) work, zero malloc.
        if let Some(lit) = self.asserting_lit {
            self.learned.insert(0, lit);
        }

        // Transfer ownership of the Vec's heap allocation — no copy, no alloc.
        // Capacity is returned via return_learned_buf() after arena insertion.
        let learned_clause = std::mem::take(&mut self.learned);

        ConflictResult {
            learned_clause,
            backtrack_level,
            lbd,
            resolution_chain: std::mem::take(&mut self.resolution_chain),
            otfs_driving_clause: None,
        }
    }

    /// Return a consumed learned clause buffer for capacity reuse across conflicts.
    /// Called after arena insertion copies the data. CaDiCaL: clause.clear()
    /// in analyze.cpp:1092 preserves the vector's heap capacity.
    pub(crate) fn return_learned_buf(&mut self, mut buf: Vec<Literal>) {
        buf.clear();
        self.learned = buf;
    }

    /// Return a consumed resolution chain buffer for capacity reuse.
    pub(crate) fn return_chain_buf(&mut self, mut buf: Vec<u64>) {
        buf.clear();
        self.resolution_chain = buf;
    }

    #[cfg(test)]
    pub(crate) fn learned_capacity(&self) -> usize {
        self.learned.capacity()
    }

    #[cfg(test)]
    pub(crate) fn resolution_chain_capacity(&self) -> usize {
        self.resolution_chain.capacity()
    }

    /// Heap-backed buffer bytes used by conflict analysis state.
    ///
    /// Excludes the inline `ConflictAnalyzer` struct itself so callers can
    /// count the parent solver shell exactly once.
    #[cfg(test)]
    pub(crate) fn buffer_bytes(&self) -> usize {
        use std::mem::size_of;

        fn packed_bool_vec_bytes(capacity: usize) -> usize {
            capacity.div_ceil(8)
        }

        self.seen_to_clear.capacity() * size_of::<usize>()
            + self.learned.capacity() * size_of::<Literal>()
            + self.resolution_chain.capacity() * size_of::<u64>()
            + packed_bool_vec_bytes(self.lbd_seen.capacity())
            + self.lbd_to_clear.capacity() * size_of::<usize>()
            + self.clause_buf.capacity() * size_of::<Literal>()
    }

    /// Resize internal buffers for variable compaction.
    /// Clear stale seen flags in var_data BEFORE emptying seen_to_clear.
    /// Without this, compact() orphans seen=true flags in var_data entries,
    /// causing counter underflow in subsequent conflict analysis (#7331).
    pub(crate) fn compact(&mut self, var_data: &mut [VarData]) {
        // Sparse-clear: reset seen flags using OLD indices (before remap).
        for &idx in &self.seen_to_clear {
            if idx < var_data.len() {
                var_data[idx].set_seen(false);
            }
        }
        self.seen_to_clear.clear();
        #[cfg(debug_assertions)]
        {
            self.seen_true_count = 0;
        }
        self.learned.clear();
        self.asserting_lit = None;
        self.resolution_chain.clear();
        self.lbd_seen.clear();
        self.lbd_to_clear.clear();
        self.clause_buf.clear();
    }
}

/// Reorder learned clause so lits[1] is at backtrack level (for 2WL correctness).
/// Production path: inline in `add_learned_clause`. This is for tests/Kani only.
pub(crate) fn reorder_for_watches(
    clause: &mut [Literal],
    var_data: &[VarData],
    backtrack_level: u32,
) {
    if clause.len() < 2 {
        return;
    }

    // Find a literal at the backtrack level (not the first one)
    for i in 2..clause.len() {
        if var_data[clause[i].variable().index()].level == backtrack_level {
            clause.swap(1, i);
            return;
        }
    }

    // If no exact match, find the highest level (should be at position 1)
    let mut max_idx = 1;
    let mut max_level = var_data[clause[1].variable().index()].level;
    for i in 2..clause.len() {
        let lit_level = var_data[clause[i].variable().index()].level;
        if lit_level > max_level {
            max_level = lit_level;
            max_idx = i;
        }
    }
    if max_idx != 1 {
        clause.swap(1, max_idx);
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "conflict_tests.rs"]
mod tests;

#[cfg(kani)]
#[path = "conflict_verification.rs"]
mod verification;
