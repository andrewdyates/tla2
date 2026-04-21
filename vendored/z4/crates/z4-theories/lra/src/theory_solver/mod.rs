// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `LraSolver`.
//!
//! The three large methods (`register_atom`, `check`, `propagate`) are
//! implemented in sibling submodules as inherent methods on `LraSolver`
//! and delegated from the trait impl here. Short delegator and
//! lifecycle methods stay inline.

use super::*;

mod check;
mod propagation;
mod registration;

impl TheorySolver for LraSolver {
    fn register_atom(&mut self, atom: TermId) {
        self.register_atom_impl(atom)
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.assert_literal_impl(literal, value)
    }

    fn check(&mut self) -> TheoryResult {
        self.check_impl()
    }

    /// Lightweight BCP-time check: runs simplex but defers disequality/model-only
    /// work to the final full check.
    fn check_during_propagate(&mut self) -> TheoryResult {
        self.check_during_propagate_impl()
    }

    /// The BCP-time check skips disequality/model-equality work, so the eager
    /// solver must run one final full check before accepting SAT.
    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        self.propagate_impl()
    }

    fn push(&mut self) {
        self.push_inner();
    }

    fn pop(&mut self) {
        self.pop_inner();
    }

    fn reset(&mut self) {
        self.reset_inner();
    }

    fn soft_reset(&mut self) {
        self.soft_reset_inner();
    }

    fn take_bound_refinements(&mut self) -> Vec<BoundRefinementRequest> {
        std::mem::take(&mut self.pending_bound_refinements)
    }

    fn supports_farkas_semantic_check(&self) -> bool {
        true
    }

    fn propagate_equalities(&mut self) -> EqualityPropagationResult {
        self.propagate_equalities_inner()
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        self.assert_shared_equality_inner(lhs, rhs, reason);
    }

    fn assert_shared_disequality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        self.assert_shared_disequality_inner(lhs, rhs, reason);
    }

    fn mark_propagation_rejected(&mut self, lit: TermId, reason_data: u64) {
        // Clear the propagated_atoms cache entry so the same atom can be
        // re-derived with better reasons on the next propagation round.
        // reason_data encodes the boolean polarity as u64.
        self.propagated_atoms.remove(&(lit, reason_data != 0));
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        vec![
            ("lra_checks", self.check_count),
            ("lra_conflicts", self.conflict_count),
            ("lra_propagations", self.propagation_count),
            ("lra_prop_throttle_skips", self.propagation_throttle_skips),
            ("lra_bcp_simplex_skips", self.bcp_simplex_skips),
            ("lra_reasons_eager", self.eager_reason_count),
            ("lra_reasons_deferred", self.deferred_reason_count),
            ("lra_simplex_sat", self.simplex_sat_count),
            (
                "lra_compound_use_vars",
                self.compound_use_index.len() as u64,
            ),
            (
                "lra_compound_wake_dirty_hits",
                self.last_compound_wake_dirty_hits as u64,
            ),
            (
                "lra_compound_wake_candidates",
                self.last_compound_wake_candidates as u64,
            ),
            (
                "lra_compound_queued",
                self.last_compound_propagations_queued as u64,
            ),
        ]
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        // Look up the parsed atom info to evaluate against the simplex model.
        let info = self.atom_cache.get(&atom)?.as_ref()?;

        // Evaluate the expression in the current simplex model.
        // expr is normalized so "expr = 0" for eq/distinct, "expr <= 0" for inequalities.
        let mut val = info.expr.constant.to_big();
        for &(var, ref coeff) in &info.expr.coeffs {
            let vi = var as usize;
            let var_info = self.vars.get(vi)?;
            val += coeff.mul_bigrational(&var_info.value.rational());
        }

        // Equality atoms: (= x y) is true iff expr evaluates to 0 in the model.
        // Guides DPLL to try the model-consistent polarity first, reducing
        // backtracking on benchmarks with many equality atoms (#4919 Phase F).
        if info.is_eq {
            return Some(val.is_zero());
        }

        // Distinct atoms: (distinct x y) is true iff expr != 0 in the model.
        if info.is_distinct {
            return Some(!val.is_zero());
        }

        // Inequality atoms: suggest polarity consistent with the model.
        // is_le=true: atom asserts "expr <= 0" (or "expr < 0" if strict)
        // is_le=false: atom asserts "expr >= 0" (or "expr > 0" if strict)
        if info.is_le {
            if info.strict {
                if val.is_negative() {
                    Some(true) // expr < 0 satisfied
                } else if val.is_positive() {
                    Some(false) // expr > 0, atom is false
                } else {
                    // val == 0, strict atom is exactly on boundary
                    None
                }
            } else if !val.is_positive() {
                Some(true) // expr <= 0 satisfied
            } else {
                Some(false) // expr > 0, atom is false
            }
        } else {
            // is_le=false: atom asserts expr >= 0 (or expr > 0 if strict)
            if info.strict {
                if val.is_positive() {
                    Some(true) // expr > 0 satisfied
                } else if val.is_negative() {
                    Some(false) // expr < 0, atom is false
                } else {
                    None // val == 0, strict boundary
                }
            } else if !val.is_negative() {
                Some(true) // expr >= 0 satisfied
            } else {
                Some(false) // expr < 0, atom is false
            }
        }
    }

    fn supports_theory_aware_branching(&self) -> bool {
        // Disabled: A/B testing on 100 SMT-COMP QF_LRA benchmarks (10s timeout)
        // showed 48/100 (disabled) vs 46/100 (enabled). Theory-aware branching
        // overrides VSIDS variable selection, which is too aggressive — Z3 only
        // uses LP-consistent *phase* selection (PS_THEORY/get_phase), not variable
        // ordering. suggest_phase() already provides LP-consistent polarity when
        // VSIDS picks a theory variable (solve.rs:704), matching Z3's approach.
        // Regressions: sc-6.induction3.cvc.smt2 (sat→timeout),
        //              windowreal-no_t_deadlock-16.smt2 (unsat→timeout).
        false
    }

    fn sort_atom_index(&mut self) {
        for atoms in self.atom_index.values_mut() {
            atoms.sort_by(|a, b| a.bound_value.cmp(&b.bound_value));
        }
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        self.generate_bound_axiom_terms_inner()
    }

    fn generate_incremental_bound_axioms(&self, atom: TermId) -> Vec<(TermId, bool, TermId, bool)> {
        self.generate_incremental_bound_axioms_inner(atom)
    }

    /// Reconstruct an `LraSolver` from a structural snapshot previously created
    /// by `export_structural_snapshot` (#6590).
    fn restore_from_structural_snapshot(
        terms: &TermStore,
        snapshot: Box<dyn std::any::Any>,
    ) -> Result<Self, Box<dyn std::any::Any>> {
        Self::restore_from_structural_snapshot_inner(terms, snapshot)
    }

    /// Export full structural state for fast reconstruction across split-loop
    /// iterations (#6590).
    ///
    /// Captures all fields that `soft_reset()` preserves: tableau rows, variable
    /// mappings, atom cache, atom/compound indices, slack state, and column index.
    /// The snapshot is consumed by `import_structural_snapshot` on a fresh
    /// `LraSolver` to skip all `register_atom` parsing and indexing work.
    fn export_structural_snapshot(&self) -> Option<Box<dyn std::any::Any>> {
        self.export_structural_snapshot_inner()
    }

    /// Import structural state from a previous LraSolver instance (#6590).
    ///
    /// Restores all structural fields and then performs soft-reset-equivalent
    /// initialization (clear bounds, populate touched_rows, etc.) so the solver
    /// is ready for `register_atom` (which will be a no-op for known atoms)
    /// followed by `assert_literal` / `check`.
    fn import_structural_snapshot(&mut self, snapshot: Box<dyn std::any::Any>) {
        self.import_structural_snapshot_inner(snapshot);
    }
}
