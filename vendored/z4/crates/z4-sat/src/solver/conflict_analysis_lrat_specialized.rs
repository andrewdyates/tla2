// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Specialized LRAT helpers for level-0, probe, and empty-clause flows.

use super::*;
use crate::kani_compat::det_hash_set_new;

impl Solver {
    /// Record the BCP resolution chain for a level-0 conflict (#4176).
    ///
    /// At decision level 0, all propagated literals are implied by unit clauses
    /// and BCP. Standard 1UIP conflict analysis assumes decision_level > 0 and
    /// has debug_asserts that fail at level 0 (backtrack_level < decision_level).
    ///
    /// This method walks the conflict clause and reason clauses backward through
    /// the trail, collecting all clause IDs involved. The result is stored as an
    /// empty learned clause with resolution hints in the clause trace, enabling
    /// SatProofManager to reconstruct the resolution DAG.
    pub(super) fn record_level0_conflict_chain(&mut self, conflict_ref: ClauseRef) {
        debug_assert_eq!(
            self.decision_level, 0,
            "record_level0_conflict_chain called at non-zero decision level"
        );
        debug_assert!(
            {
                let ci = conflict_ref.0 as usize;
                let lits = self.arena.literals(ci);
                lits.iter().all(|lit| self.lit_val(*lit) < 0)
            },
            "BUG: level-0 conflict clause {} has non-false literal",
            conflict_ref.0
        );

        if self.cold.clause_trace.is_none() && !self.cold.lrat_enabled {
            self.has_empty_clause = true;
            if self.cold.empty_clause_scope_depth == 0 {
                self.cold.empty_clause_scope_depth = self.cold.scope_selectors.len();
            }
            return;
        }

        if self.cold.lrat_enabled {
            self.materialize_level0_unit_proofs();

            let ci = conflict_ref.0 as usize;
            let conflict_lits = self.arena.literals(ci).to_vec();
            let num_vars = self.var_data.len();

            for &idx in &self.min.lrat_to_clear {
                self.min.minimize_flags[idx] &= !LRAT_A;
            }
            self.min.lrat_to_clear.clear();
            for &lit in &conflict_lits {
                let vi = lit.variable().index();
                if vi < num_vars && self.min.minimize_flags[vi] & LRAT_A == 0 {
                    self.min.minimize_flags[vi] |= LRAT_A;
                    self.min.lrat_to_clear.push(vi);
                }
            }

            let unit_chain = self.collect_level0_unit_chain_filtered(&det_hash_set_new());
            let mut conflict_id = self.cached_conflict_clause_id(conflict_ref);

            if conflict_id == 0 && self.proof_manager.is_some() {
                let tt_id = self
                    .proof_emit_add(&conflict_lits, &[], ProofAddKind::TrustedTransform)
                    .unwrap_or(0);
                if tt_id != 0 {
                    if ci < self.cold.clause_ids.len() {
                        self.cold.clause_ids[ci] = tt_id;
                    }
                    conflict_id = tt_id;
                }
            }

            let mut proof_hints: Vec<u64> =
                unit_chain.into_iter().rev().filter(|&h| h != 0).collect();
            if conflict_id != 0 {
                proof_hints.push(conflict_id);
            }

            let trace_chain =
                self.collect_resolution_chain(conflict_ref, None, &det_hash_set_new());
            self.mark_empty_clause_with_hints_and_trace(&proof_hints, trace_chain);
        } else {
            let chain = self.collect_resolution_chain(conflict_ref, None, &det_hash_set_new());
            self.mark_empty_clause_with_hints_and_trace(&chain, chain.clone());
        }
    }

    /// Collect LRAT hints for a probing conflict at level 1.
    ///
    /// When probing literal `probe_lit` at level 1 causes `conflict_ref`, this
    /// collects the hint chain that allows the LRAT checker to verify the
    /// derived unit clause `{¬probe_lit}`.
    ///
    /// The LRAT checker verifies by RUP: it assumes the negation of the derived
    /// clause (i.e., assumes `probe_lit` is true), then processes hints in order.
    /// Each hint clause must become unit or conflict under accumulated
    /// assignments. To achieve this, we collect:
    ///
    /// 1. Level-0 unit proof IDs (establish base assignment in forward trail order)
    /// 2. Level-1 reason clause IDs (in trail order = BCP propagation order)
    /// 3. The conflict clause (all-falsified under accumulated assignment)
    ///
    /// This is a forward BCP trace, NOT a 1UIP resolution chain. The LRAT
    /// checker needs to replay the exact propagation sequence that led to
    /// conflict, not the algebraic resolution derivation. (#7108)
    ///
    /// Must be called BEFORE backtracking so that level-1 trail entries and
    /// their reason clauses are still accessible.
    pub(super) fn collect_probe_conflict_lrat_hints(
        &mut self,
        conflict_ref: ClauseRef,
        probe_lit: Literal,
        forced_unit: Option<Literal>,
    ) -> Vec<u64> {
        if !self.cold.lrat_enabled {
            return Vec::new();
        }

        debug_assert_eq!(
            self.decision_level, 1,
            "collect_probe_conflict_lrat_hints must be called at decision level 1"
        );
        let probe_var = probe_lit.variable().index();
        debug_assert!(
            self.var_is_assigned(probe_var),
            "collect_probe_conflict_lrat_hints probe literal {probe_lit:?} is unassigned",
        );
        debug_assert!(
            {
                let ci = conflict_ref.0 as usize;
                let lits = self.arena.literals(ci);
                lits.iter().all(|lit| self.lit_val(*lit) < 0)
            },
            "BUG: probe conflict clause {} has non-false literal",
            conflict_ref.0
        );

        self.materialize_level0_unit_proofs();

        let mut rup_satisfied = det_hash_set_new();
        rup_satisfied.insert(probe_lit);
        if let Some(forced) = forced_unit {
            rup_satisfied.insert(forced.negated());
        }
        let num_vars = self.var_data.len();
        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] &= !LRAT_A;
        }
        self.min.lrat_to_clear.clear();

        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        for i in 0..level0_end {
            let lit = self.trail[i];
            let vi = lit.variable().index();
            if vi < num_vars
                && vi != probe_var
                && self.min.minimize_flags[vi] & LRAT_A == 0
                && self.has_any_proof_id(vi)
            {
                self.min.minimize_flags[vi] |= LRAT_A;
                self.min.lrat_to_clear.push(vi);
            }
        }

        let mut level0_chain = self.collect_level0_unit_chain_filtered(&rup_satisfied);
        level0_chain.reverse();

        let level1_start = level0_end;
        let mut level1_hints: Vec<u64> = Vec::new();
        let mut seen = det_hash_set_new();
        for h in &level0_chain {
            seen.insert(*h);
        }
        for i in level1_start..self.trail.len() {
            let lit = self.trail[i];
            let vi = lit.variable().index();
            if vi == probe_var {
                continue;
            }
            let reason_raw = self.var_data[vi].reason;
            if is_clause_reason(reason_raw) {
                let reason_ref = ClauseRef(reason_raw);
                let reason_id = self.clause_id(reason_ref);
                if reason_id != 0 && !seen.contains(&reason_id) {
                    let ci = reason_ref.0 as usize;
                    let clen = self.arena.len_of(ci);
                    let contains_rup_satisfied =
                        (0..clen).any(|j| rup_satisfied.contains(&self.arena.literal(ci, j)));
                    if !contains_rup_satisfied {
                        level1_hints.push(reason_id);
                        seen.insert(reason_id);
                    }
                }
            }
        }

        let conflict_id = self.cached_conflict_clause_id(conflict_ref);
        if conflict_id != 0 && !seen.contains(&conflict_id) {
            level1_hints.push(conflict_id);
        }

        let mut hints = level0_chain;
        hints.extend(level1_hints);
        hints
    }

    /// Collect LRAT hints for the empty clause when a conflict clause has
    /// all literals false at level 0.
    ///
    /// Uses materialized unit proof IDs + conflict clause ID rather than
    /// raw reason clause IDs from collect_resolution_chain. Reason clauses
    /// are multi-literal and fail LRAT RUP verification because the checker
    /// has no base assignments to make them unit. (#7108)
    pub(super) fn collect_empty_clause_hints_for_conflict(
        &mut self,
        conflict_ref: ClauseRef,
        _clause_lits: &[Literal],
    ) -> Vec<u64> {
        if !self.cold.lrat_enabled {
            return Vec::new();
        }
        self.materialize_level0_unit_proofs();

        let ci = conflict_ref.0 as usize;
        let conflict_lits = self.arena.literals(ci).to_vec();
        let num_vars = self.var_data.len();

        for &idx in &self.min.lrat_to_clear {
            self.min.minimize_flags[idx] &= !LRAT_A;
        }
        self.min.lrat_to_clear.clear();
        for &lit in &conflict_lits {
            let vi = lit.variable().index();
            if vi < num_vars && self.min.minimize_flags[vi] & LRAT_A == 0 {
                self.min.minimize_flags[vi] |= LRAT_A;
                self.min.lrat_to_clear.push(vi);
            }
        }

        let unit_chain = self.collect_level0_unit_chain_filtered(&det_hash_set_new());
        let conflict_id = self.cached_conflict_clause_id(conflict_ref);
        let mut hints: Vec<u64> = unit_chain.into_iter().rev().filter(|&h| h != 0).collect();
        if conflict_id != 0 {
            hints.push(conflict_id);
        }
        hints
    }

    /// Collect LRAT hints for the empty clause when a unit clause contradicts
    /// an existing level-0 assignment.
    ///
    /// `unit_proof_id`: proof ID of the contradicting unit clause.
    /// `contradicted_var`: variable index whose assignment is contradicted.
    pub(super) fn collect_empty_clause_hints_for_unit_contradiction(
        &mut self,
        unit_proof_id: u64,
        contradicted_var: usize,
    ) -> Vec<u64> {
        if !self.cold.lrat_enabled {
            return Vec::new();
        }
        self.materialize_level0_unit_proofs();
        let mut hints = Vec::new();
        if let Some(existing_pid) = self.level0_var_proof_id(contradicted_var) {
            hints.push(existing_pid);
        }
        if self.lrat_hint_id_visible(unit_proof_id) && !hints.contains(&unit_proof_id) {
            hints.push(unit_proof_id);
        }
        // Empty-clause derivation from contradictory units needs two distinct,
        // externally visible hints. If the incoming unit proof is hidden
        // (TrustedTransform) or duplicates the existing assignment proof,
        // degrade to the empty-hints path rather than emit a broken LRAT step.
        if hints.len() < 2 {
            return Vec::new();
        }
        hints
    }
}
