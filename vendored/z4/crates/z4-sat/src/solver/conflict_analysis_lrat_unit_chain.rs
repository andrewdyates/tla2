// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LRAT proof ID queries and level-0 unit chain collection.
//!
//! Proof ID lookup (unit, level-0, cached), BFS transitive closure on
//! level-0 variables, and reverse-trail unit chain collection for LRAT
//! hint construction. Extracted from `conflict_analysis_lrat.rs` to keep
//! each file under 500 lines.

use super::*;
use crate::kani_compat::{det_hash_set_new, DetHashSet};

impl Solver {
    /// Reverse LRAT hints and drop zeros.
    ///
    /// LRAT checkers consume hints in listed order, while Z4 collects them in
    /// analysis order, so we reverse first. Deduplication of duplicate clause
    /// IDs is handled at the proof output boundary in `ProofManager::emit_add`
    /// (#5248), not here — post-hoc dedup at this level breaks multi-stage
    /// ordering that the LRAT checker requires (#5194). Sentinel value 0 is
    /// filtered.
    pub(super) fn lrat_reverse_hints(hints: &[u64]) -> Vec<u64> {
        hints.iter().rev().copied().filter(|&h| h != 0).collect()
    }

    #[inline]
    pub(crate) fn unit_proof_id_of_var_index(&self, var_index: usize) -> Option<u64> {
        self.unit_proof_id
            .get(var_index)
            .copied()
            .filter(|&id| id != 0)
    }

    #[inline]
    pub(crate) fn lrat_hint_id_visible(&self, clause_id: u64) -> bool {
        if clause_id == 0 || !self.cold.lrat_enabled {
            return clause_id != 0;
        }
        match self.proof_manager.as_ref() {
            Some(manager) => manager.lrat_id_visible_in_file(clause_id),
            None => true,
        }
    }

    #[inline]
    pub(crate) fn visible_unit_proof_id_of_var_index(&self, var_index: usize) -> Option<u64> {
        self.unit_proof_id_of_var_index(var_index)
            .filter(|&id| self.lrat_hint_id_visible(id))
    }

    #[inline]
    fn visible_level0_proof_id_of_var_index(&self, var_index: usize) -> Option<u64> {
        self.cold
            .level0_proof_id
            .get(var_index)
            .copied()
            .filter(|&id| self.lrat_hint_id_visible(id))
    }

    #[inline]
    pub(super) fn cached_conflict_clause_id(&self, conflict_ref: ClauseRef) -> u64 {
        let direct = self.clause_id(conflict_ref);
        if direct != 0 {
            return direct;
        }
        if self.last_conflict_clause_ref == Some(conflict_ref) {
            return self.last_conflict_clause_id;
        }
        0
    }

    /// Check if a variable has an LRAT proof ID preserved by ClearLevel0.
    ///
    /// When BVE deletes a reason clause via ClearLevel0, `reason[vi]` is set
    /// to None but `level0_proof_id[vi]` preserves the clause ID for LRAT
    /// chain construction (#4617).
    #[inline]
    pub(super) fn has_level0_proof_id(&self, var_index: usize) -> bool {
        var_index < self.cold.level0_proof_id.len() && self.cold.level0_proof_id[var_index] != 0
    }

    /// Check whether a level-0 variable has LRAT provenance from any source:
    /// reason clause, visible unit_proof_id, or visible level0_proof_id
    /// (#6257, #6270).
    ///
    /// Use this as the BFS seed/expansion condition for LRAT hint collection.
    /// After #6257, unit clauses are enqueued with reason=None but their proof
    /// ID is stored in unit_proof_id, so `reason[vi].is_some() ||
    /// has_level0_proof_id(vi)` is insufficient.
    #[inline]
    pub(super) fn has_any_proof_id(&self, var_index: usize) -> bool {
        if self.cold.lrat_enabled {
            is_clause_reason(self.var_data[var_index].reason)
                || self.visible_unit_proof_id_of_var_index(var_index).is_some()
                || self
                    .visible_level0_proof_id_of_var_index(var_index)
                    .is_some()
        } else {
            is_clause_reason(self.var_data[var_index].reason)
                || (var_index < self.unit_proof_id.len() && self.unit_proof_id[var_index] != 0)
                || self.has_level0_proof_id(var_index)
        }
    }

    /// Get the LRAT proof ID for a level-0 variable.
    ///
    /// In LRAT mode, does NOT fall back to multi-literal reason clause IDs.
    /// Using a multi-literal reason as a hint causes RUP failure because the
    /// hint clause has 2+ non-falsified literals under the RUP assumption.
    /// Callers should still prefer `ensure_level0_unit_proof_ids()` so that
    /// level-0 implied variables have materialized unit proofs. As a fallback,
    /// this method accepts unit reason clauses directly when no materialized
    /// proof ID exists yet (#7108).
    ///
    /// In non-LRAT mode (DRAT), prefers reason clause IDs for RUP compatibility.
    #[inline]
    pub(super) fn level0_var_proof_id(&self, var_index: usize) -> Option<u64> {
        if self.cold.lrat_enabled {
            // LRAT mode: only return unit clause proof IDs.
            if let Some(id) = self.visible_level0_proof_id_of_var_index(var_index) {
                return Some(id);
            }
            if let Some(pid) = self.visible_unit_proof_id_of_var_index(var_index) {
                return Some(pid);
            }
            // Fall back to reason clause ID ONLY for unit clauses (len 1).
            // Multi-literal reasons are rejected because they have 2+
            // non-falsified literals under RUP assumption. Unit clauses
            // have exactly one literal and are valid LRAT hints (#7108).
            let reason_raw = self.var_data[var_index].reason;
            if is_clause_reason(reason_raw) {
                let ci = reason_raw as usize;
                if ci < self.arena.len() && self.arena.len_of(ci) == 1 {
                    let id = self.clause_id(ClauseRef(reason_raw));
                    if id != 0 {
                        return Some(id);
                    }
                }
            }
            None
        } else {
            // DRAT mode: reason clause → level0_proof_id → unit_proof_id.
            let reason_raw = self.var_data[var_index].reason;
            if is_clause_reason(reason_raw) {
                let id = self.clause_id(ClauseRef(reason_raw));
                if id != 0 {
                    return Some(id);
                }
            }
            if self.has_level0_proof_id(var_index) {
                return Some(self.cold.level0_proof_id[var_index]);
            }
            if let Some(pid) = self.unit_proof_id_of_var_index(var_index) {
                return Some(pid);
            }
            None
        }
    }

    /// Check if a variable's reason clause is satisfied by the RUP assumption.
    ///
    /// Returns `true` if the reason clause (or the variable itself for deleted
    /// reason clauses) contains a literal from `rup_satisfied`. Such hint
    /// clauses must be excluded from LRAT chains (#5026).
    fn is_reason_rup_satisfied(&self, var_idx: usize, rup_satisfied: &DetHashSet<Literal>) -> bool {
        if rup_satisfied.is_empty() {
            return false;
        }
        if let Some(reason_ref) = self.var_reason(var_idx) {
            let ci = reason_ref.0 as usize;
            let clen = self.arena.len_of(ci);
            for j in 0..clen {
                if rup_satisfied.contains(&self.arena.literal(ci, j)) {
                    return true;
                }
            }
            false
        } else {
            // No reason clause (ClearLevel0 or decision). Check if the variable
            // itself is referenced by rup_satisfied (its original reason clause
            // was deleted but would have contained the satisfied literal).
            rup_satisfied
                .iter()
                .any(|&sl| sl.variable().index() == var_idx)
        }
    }

    /// Phase 1 only: BFS transitive closure on level-0 variables.
    ///
    /// Seeds must already be marked with `LRAT_A` in `minimize_flags` and pushed
    /// to `lrat_to_clear`. After return, `minimize_flags[v] & LRAT_A != 0` for
    /// all transitively reachable level-0 variables and their indices are in
    /// `lrat_to_clear`.
    ///
    /// Variables marked with `LRAT_B` are excluded from BFS expansion (used by
    /// replace_clause to skip new clause literals the RUP checker already knows).
    ///
    /// Does NOT clean up `LRAT_A` or `lrat_to_clear`; caller is responsible.
    fn bfs_level0_transitive_closure(&mut self) {
        let num_vars = self.var_data.len();
        let mut head = 0;
        while head < self.min.lrat_to_clear.len() {
            let vi = self.min.lrat_to_clear[head];
            head += 1;
            let Some(reason_ref) = self.var_reason(vi) else {
                // Include ClearLevel0 victims whose reason was cleared by BVE —
                // no clause to BFS through, but level0_proof_id preserves the
                // clause ID for Phase 2 (#4617, #5014).
                continue;
            };
            let ci = reason_ref.0 as usize;
            if ci >= self.arena.len() {
                continue;
            }
            let clen = self.arena.len_of(ci);
            for i in 0..clen {
                let reason_lit = self.arena.literal(ci, i);
                let rv = reason_lit.variable().index();
                if rv != vi
                    && rv < num_vars
                    && self.var_data[rv].level == 0
                    && self.min.minimize_flags[rv] & (LRAT_A | LRAT_B) == 0
                    && self.has_any_proof_id(rv)
                {
                    self.min.minimize_flags[rv] |= LRAT_A;
                    self.min.lrat_to_clear.push(rv);
                }
            }
        }
    }

    /// BFS transitive closure on level-0 variables, then reverse-trail scan
    /// to collect LRAT proof IDs in RUP processing order.
    ///
    /// **Protocol:** Before calling, the caller must:
    /// 1. Mark seed variables: `minimize_flags[v] |= LRAT_A` for each seed.
    /// 2. Push seeds into `lrat_to_clear` (used as BFS queue + cleanup list).
    /// 3. Optionally mark exclusions with `minimize_flags[v] |= LRAT_B` (e.g.,
    ///    new clause literals in replace_clause that the RUP checker already knows).
    ///    Caller is responsible for `LRAT_B` cleanup afterward.
    ///
    /// Returns proof IDs in reverse-trail order (ready for LRAT hint chain).
    /// Cleans up `LRAT_A` and `lrat_to_clear` before returning.
    ///
    /// CaDiCaL reference: analyze.cpp:253-268 (analyze_literal) + 1240-1246.
    pub(super) fn collect_level0_unit_chain(&mut self) -> Vec<u64> {
        self.collect_level0_unit_chain_filtered(&det_hash_set_new())
    }

    /// Shared implementation for `collect_level0_unit_chain` and
    /// `append_lrat_unit_chain`. Runs BFS Phase 1, then Phase 2 reverse-trail
    /// scan with an optional RUP-satisfied filter (#5271 dedup).
    ///
    /// When `rup_satisfied` is empty the filter is a no-op
    /// (`is_reason_rup_satisfied` short-circuits on empty sets).
    pub(super) fn collect_level0_unit_chain_filtered(
        &mut self,
        rup_satisfied: &DetHashSet<Literal>,
    ) -> Vec<u64> {
        let num_vars = self.var_data.len();

        // Phase 1: BFS transitive closure on level-0 variables.
        self.bfs_level0_transitive_closure();

        // Phase 2: Scan the trail in REVERSE order for level-0 variables.
        // Collect proof IDs via 3-tier fallback: reason → unit_proof_id → level0_proof_id.
        //
        // RUP-satisfied filter (#5026): Skip hints whose clause is trivially
        // satisfied by the RUP assumption — strict checkers reject such hints.
        //
        // LRAT vs DRAT distinction (#7108): In DRAT mode, level0_var_proof_id
        // may return multi-literal reason clause IDs, and the reason clause may
        // contain a literal satisfied by the RUP assumption. In LRAT mode,
        // level0_var_proof_id returns unit proof IDs (single-literal clauses).
        // A unit clause [x] is RUP-satisfied only if x itself is in
        // rup_satisfied — not if the original reason clause contains a
        // satisfied literal. Checking the reason clause incorrectly filters
        // out unit hints that are necessary for the chain.
        // CaDiCaL reference: analyze.cpp unit_chain has no RUP filter — unit
        // IDs are always included unconditionally.
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        let mut chain: Vec<u64> = Vec::new();
        for i in (0..level0_end).rev() {
            let lit = self.trail[i];
            let var_idx = lit.variable().index();
            if var_idx < num_vars && self.min.minimize_flags[var_idx] & LRAT_A != 0 {
                // In LRAT mode, the hint is a unit clause [lit]. Check if lit
                // itself is RUP-satisfied (already true under the RUP assumption).
                // If so, skip it — the checker already knows this variable.
                // In DRAT mode, check if the reason clause is RUP-satisfied.
                let skip = if self.cold.lrat_enabled {
                    // Unit clause [lit] is satisfied if lit ∈ rup_satisfied.
                    !rup_satisfied.is_empty() && rup_satisfied.contains(&lit)
                } else {
                    self.is_reason_rup_satisfied(var_idx, rup_satisfied)
                };
                if !skip {
                    // Hidden TrustedTransform units are never valid external
                    // LRAT hints because ProofManager strips them from the
                    // file output. Callers must materialize visible unit
                    // proofs before collecting a chain that needs them.
                    if let Some(id) = self.level0_var_proof_id(var_idx) {
                        chain.push(id);
                    }
                }
            }
        }

        // Sparse cleanup: reset only touched indices.
        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] &= !LRAT_A;
        }
        self.min.lrat_to_clear.clear();

        chain
    }

    /// Append LRAT unit chain for conflict analysis learned clause.
    ///
    /// Seeds `LRAT_A` in `minimize_flags` from `level0_vars`, then delegates to
    /// `collect_level0_unit_chain_filtered` with the RUP-satisfied filter.
    /// Collected proof IDs are appended to `self.conflict` chain.
    ///
    /// CaDiCaL reference: analyze.cpp:253-268 (analyze_literal) + 1240-1246.
    pub(super) fn append_lrat_unit_chain(
        &mut self,
        level0_vars: &[usize],
        rup_satisfied: &DetHashSet<Literal>,
    ) {
        // CaDiCaL analyze.cpp:433: all level-0 vars must actually be at level 0
        debug_assert!(
            level0_vars
                .iter()
                .all(|&v| v < self.var_data.len() && self.var_data[v].level == 0),
            "BUG: append_lrat_unit_chain called with non-level-0 variable"
        );
        let num_vars = self.var_data.len();

        // Seed LRAT_A from level0_vars.
        for &v in level0_vars {
            if v < num_vars && self.min.minimize_flags[v] & LRAT_A == 0 {
                self.min.minimize_flags[v] |= LRAT_A;
                self.min.lrat_to_clear.push(v);
            }
        }

        // Delegate to shared BFS + reverse-trail-scan implementation (#5271).
        let chain = self.collect_level0_unit_chain_filtered(rup_satisfied);
        for id in chain {
            self.conflict.add_to_chain(id);
        }
    }

    /// Materialize level-0 unit proof IDs before LRAT hint collection.
    ///
    /// Alias for `materialize_level0_unit_proofs`. Called by probe, backbone,
    /// condition, and decompose before hint collection to ensure all level-0
    /// implied variables have proper unit proof IDs (#7108).
    pub(super) fn ensure_level0_unit_proof_ids(&mut self) {
        self.materialize_level0_unit_proofs();
    }
}
