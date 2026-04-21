// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Combined LIA + LRA theory solver for QF_LIRA.
//!
//! This solver routes literals to LIA or LRA based on the sorts of their operands:
//! - Int-sorted comparisons/equalities go to LIA
//! - Real-sorted comparisons/equalities go to LRA
//! - The SAT solver handles the Boolean combination
//!
//! # Cross-Sort Value Propagation (#4915)
//!
//! When `to_real(x)` appears in a Real constraint, LRA (after the `to_real`
//! identity fix) shares the same TermId for `x` as LIA. After LIA determines
//! a tight bound (e.g., `x = 1`), this value must be forwarded to LRA so it
//! can detect conflicts with Real constraints on the same variable.
//!
//! Standard N-O propagation only exchanges equalities between variables with
//! the same value (not variable-constant bindings). The `propagate_cross_sort_values`
//! method supplements this with direct tight-bound forwarding.

mod cross_sort;
mod model;

use num_bigint::BigInt;
use z4_core::term::{Constant, TermData};
use z4_core::{TermId, TermStore, TheoryResult, TheorySolver};
use z4_lia::LiaSolver;
use z4_lra::LraSolver;

use crate::combined_solvers::check_loops::{
    assert_fixpoint_convergence, debug_nelson_oppen, defer_non_local_result,
    propagate_equalities_to, triage_lia_result, triage_lra_result_deferred,
};
use crate::term_helpers::{involves_int_arithmetic, involves_real_arithmetic};

/// Combined LIA + LRA theory solver for QF_LIRA.
pub(crate) struct LiraSolver<'a> {
    /// Reference to term store for inspecting literal sorts
    pub(super) terms: &'a TermStore,
    /// LIA solver for integer arithmetic
    pub(super) lia: LiaSolver<'a>,
    /// LRA solver for real arithmetic
    pub(super) lra: LraSolver,
    /// Already-propagated cross-sort (variable, value) pairs for deduplication.
    /// Uses BigInt keys to avoid i64 truncation collisions on large values (#6150).
    pub(super) propagated_cross_sort: hashbrown::HashSet<(TermId, BigInt)>,
    /// Trail for incremental pop of propagated_cross_sort entries.
    pub(super) cross_sort_trail: Vec<CrossSortTrailEntry>,
    /// Int-sorted terms that occur in literals actually asserted to the Real side.
    pub(super) asserted_real_int_terms: hashbrown::HashSet<TermId>,
    /// Trail for incremental pop of asserted_real_int_terms.
    pub(super) asserted_real_int_term_trail: Vec<AssertedRealIntTermTrailEntry>,
    /// Scope depth counter for push/pop symmetry checking (#4714, #4995).
    pub(super) scope_depth: usize,
}

pub(super) enum CrossSortTrailEntry {
    ScopeMarker,
    Propagated(TermId, BigInt),
}

pub(super) enum AssertedRealIntTermTrailEntry {
    ScopeMarker,
    Term(TermId),
}

impl<'a> LiraSolver<'a> {
    /// Create a new combined LIA+LRA solver
    pub(crate) fn new(terms: &'a TermStore) -> Self {
        let mut lia = LiaSolver::new(terms);
        lia.set_combined_theory_mode(true);
        let mut lra = LraSolver::new(terms);
        lra.set_combined_theory_mode(true);
        Self {
            terms,
            lia,
            lra,
            propagated_cross_sort: hashbrown::HashSet::new(),
            cross_sort_trail: Vec::new(),
            asserted_real_int_terms: hashbrown::HashSet::new(),
            asserted_real_int_term_trail: Vec::new(),
            scope_depth: 0,
        }
    }

    fn record_asserted_real_int_term(&mut self, term: TermId) {
        if self.asserted_real_int_terms.insert(term) {
            self.asserted_real_int_term_trail
                .push(AssertedRealIntTermTrailEntry::Term(term));
        }
    }

    pub(crate) fn take_learned_state(
        &mut self,
    ) -> (
        Vec<z4_lia::StoredCut>,
        hashbrown::HashSet<z4_lia::HnfCutKey>,
    ) {
        self.lia.take_learned_state()
    }

    pub(crate) fn import_learned_state(
        &mut self,
        cuts: Vec<z4_lia::StoredCut>,
        seen: hashbrown::HashSet<z4_lia::HnfCutKey>,
    ) {
        self.lia.import_learned_state(cuts, seen);
    }

    pub(crate) fn take_dioph_state(&mut self) -> z4_lia::DiophState {
        self.lia.take_dioph_state()
    }

    pub(crate) fn import_dioph_state(&mut self, state: z4_lia::DiophState) {
        self.lia.import_dioph_state(state);
    }

    #[expect(dead_code, reason = "used by incremental split-loop conflict macros")]
    pub(crate) fn collect_all_bound_conflicts(
        &self,
        skip_first: bool,
    ) -> Vec<z4_core::TheoryConflict> {
        let mut lia_conflicts = self.lia.collect_all_bound_conflicts(false);
        let lra_conflicts = self.lra.collect_all_bound_conflicts(false);
        if skip_first && !lia_conflicts.is_empty() {
            lia_conflicts.remove(0);
        }
        if skip_first && lia_conflicts.is_empty() {
            return lra_conflicts.into_iter().skip(1).collect();
        }
        lia_conflicts.into_iter().chain(lra_conflicts).collect()
    }

    /// Track Int-sorted terms that occur in literals routed to the Real solver.
    ///
    /// `register_atom()` intentionally over-registers atoms in LRA so metadata like
    /// `to_int` survives until check-time. Cross-sort propagation cannot treat
    /// registration artifacts as proof that an Int term actually participates in a
    /// Real assertion, so this set is populated only from `assert_literal()`.
    fn track_asserted_real_int_terms(&mut self, literal: TermId) {
        let mut visited: hashbrown::HashSet<TermId> = hashbrown::HashSet::new();
        let mut stack = vec![literal];

        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }

            if matches!(self.terms.sort(term), z4_core::Sort::Int)
                && !matches!(self.terms.get(term), TermData::Const(Constant::Int(_)))
            {
                self.record_asserted_real_int_term(term);
            }

            stack.extend(self.terms.children(term));
        }
    }

    /// Replay learned cuts into the LRA solver (#6665).
    ///
    /// Forwards to the standalone LRA solver. The LIA solver's internal LRA
    /// state is managed separately by LIA's own replay_learned_cuts.
    pub(crate) fn replay_learned_cuts(&mut self) {
        self.lra.replay_learned_cuts();
        self.lia.replay_learned_cuts();
    }

    /// Get the standalone LRA solver for bound conflict collection (#6665).
    pub(crate) fn lra_solver(&self) -> &LraSolver {
        &self.lra
    }
}

impl TheorySolver for LiraSolver<'_> {
    fn register_atom(&mut self, atom: TermId) {
        self.lia.register_atom(atom);
        self.lra.register_atom(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        // Route to LIA if it involves Int arithmetic
        let is_int = involves_int_arithmetic(self.terms, literal);
        let is_real = involves_real_arithmetic(self.terms, literal);
        if is_int {
            self.lia.assert_literal(literal, value);
        }

        // Route to LRA if it involves Real arithmetic
        if is_real {
            self.track_asserted_real_int_terms(literal);
            self.lra.assert_literal(literal, value);
        }

        // Sort routing invariant: same as AUFLIRA — a single literal should
        // not match both Int and Real sort predicates.
        debug_assert!(
            !(is_int && is_real),
            "BUG: LIRA assert_literal: literal {literal:?} routed to BOTH LIA and LRA"
        );
    }

    fn check(&mut self) -> TheoryResult {
        let debug = debug_nelson_oppen();
        const MAX_ITERATIONS: usize = 100;
        let mut pending_cross_sort_split: Option<TheoryResult> = None;

        for iteration in 0..MAX_ITERATIONS {
            // LIA: splits deferred until cross-sort propagation completes (#4915).
            let lia_result = self.lia.check();
            let lia_is_unknown = matches!(&lia_result, TheoryResult::Unknown);
            let (deferred_lia_result, lia_early) = triage_lia_result(lia_result);
            if let Some(early) = lia_early {
                return early;
            }
            let lia_eq_count = match propagate_equalities_to(
                &mut self.lia,
                &mut self.lra,
                debug,
                "LIRA-LIA",
                iteration,
            ) {
                Ok(n) => n,
                Err(conflict) => return conflict,
            };

            // LRA: check before cross-sort so term_to_var is populated.
            //
            // #7448: Use triage_lra_result_deferred instead of triage_lra_result.
            // triage_lra_result early-returns NeedModelEquality/NeedDisequalitySplit,
            // which skips cross-sort propagation entirely. For Big-M patterns
            // like (* 1000000.0 (to_real phase)), LRA discovers model equalities
            // before cross-sort can bridge LIA's integer bounds to LRA. Without
            // deferral, the loop cycles NeedModelEquality → encode → re-check
            // without ever propagating phase's integrality, producing Unknown.
            let lra_result = self.lra.check();
            let lra_is_unknown = matches!(&lra_result, TheoryResult::Unknown);
            let (deferred_lra_result, lra_early) = triage_lra_result_deferred(lra_result);
            if let Some(early) = lra_early {
                return early;
            }
            let lra_eq_count = match propagate_equalities_to(
                &mut self.lra,
                &mut self.lia,
                debug,
                "LIRA-LRA",
                iteration,
            ) {
                Ok(n) => n,
                Err(conflict) => return conflict,
            };

            // Cross-sort value/bound propagation LIA → LRA (#4915, #5947).
            let (cross_sort_count, cross_sort_split) = self.propagate_cross_sort_values(debug);
            if cross_sort_split.is_some() {
                pending_cross_sort_split = cross_sort_split;
            }

            // Cross-sort propagation for to_int terms: LRA → LIA (#5944).
            // After LRA determines x's value, compute floor(x) and assert
            // to_int(x) = floor(x) as tight bounds in LIA's internal solver.
            let to_int_count = self.propagate_to_int_values(debug);

            if lia_eq_count == 0 && lra_eq_count == 0 && cross_sort_count == 0 && to_int_count == 0
            {
                if lia_is_unknown || lra_is_unknown {
                    return TheoryResult::Unknown;
                }
                if debug && iteration > 0 {
                    safe_eprintln!("[N-O LIRA] Fixpoint after {} iterations", iteration + 1);
                }
                if let Some(split) = deferred_lia_result {
                    return split;
                }
                // #7448: return deferred LRA results (NeedModelEquality,
                // NeedDisequalitySplit, NeedExpressionSplit) at fixpoint,
                // after cross-sort propagation has had a chance to run.
                if let Some(lra_deferred) = deferred_lra_result {
                    return lra_deferred;
                }
                // #5947: return cross-sort split at fixpoint for tight bounds.
                if let Some(split) = pending_cross_sort_split {
                    return split;
                }
                assert_fixpoint_convergence("LIRA", &mut [&mut self.lia, &mut self.lra]);
                return TheoryResult::Sat;
            }
            // Non-convergence is a solver bug — panic in all build modes.
            assert!(
                iteration < MAX_ITERATIONS - 1,
                "BUG: LIRA N-O loop did not converge in {MAX_ITERATIONS} iterations"
            );
        }
        TheoryResult::Unknown
    }

    fn check_during_propagate(&mut self) -> TheoryResult {
        let lia_result = defer_non_local_result(self.lia.check_during_propagate());
        if !matches!(lia_result, TheoryResult::Sat) {
            return lia_result;
        }

        let lra_result = defer_non_local_result(self.lra.check_during_propagate());
        if !matches!(lra_result, TheoryResult::Sat) {
            return lra_result;
        }

        TheoryResult::Sat
    }

    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    delegate_propagate!(lia, lra);

    fn supports_farkas_semantic_check(&self) -> bool {
        true
    }

    fn push(&mut self) {
        self.scope_depth += 1;
        self.lia.push();
        self.lra.push();
        self.cross_sort_trail.push(CrossSortTrailEntry::ScopeMarker);
        self.asserted_real_int_term_trail
            .push(AssertedRealIntTermTrailEntry::ScopeMarker);
    }

    fn pop(&mut self) {
        if self.scope_depth == 0 {
            // Graceful no-op: pop at depth 0 is a caller error but not fatal.
            return;
        }
        self.scope_depth -= 1;
        self.lia.pop();
        self.lra.pop();
        while let Some(entry) = self.cross_sort_trail.pop() {
            match entry {
                CrossSortTrailEntry::ScopeMarker => break,
                CrossSortTrailEntry::Propagated(term, key) => {
                    self.propagated_cross_sort.remove(&(term, key));
                }
            }
        }
        while let Some(entry) = self.asserted_real_int_term_trail.pop() {
            match entry {
                AssertedRealIntTermTrailEntry::ScopeMarker => break,
                AssertedRealIntTermTrailEntry::Term(term) => {
                    self.asserted_real_int_terms.remove(&term);
                }
            }
        }
    }

    fn reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: LiraSolver::reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.lia.reset();
        self.lra.reset();
        self.propagated_cross_sort.clear();
        self.cross_sort_trail.clear();
        self.asserted_real_int_terms.clear();
        self.asserted_real_int_term_trail.clear();
    }

    fn soft_reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: LiraSolver::soft_reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.lia.soft_reset();
        self.lra.soft_reset();
        self.propagated_cross_sort.clear();
        self.cross_sort_trail.clear();
        self.asserted_real_int_terms.clear();
        self.asserted_real_int_term_trail.clear();
    }

    fn supports_theory_aware_branching(&self) -> bool {
        self.lra.supports_theory_aware_branching()
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        self.lra.suggest_phase(atom)
    }

    fn sort_atom_index(&mut self) {
        self.lra.sort_atom_index();
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        self.lra.generate_bound_axiom_terms()
    }

    fn generate_incremental_bound_axioms(&self, atom: TermId) -> Vec<(TermId, bool, TermId, bool)> {
        self.lra.generate_incremental_bound_axioms(atom)
    }
}
