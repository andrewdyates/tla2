// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Generic Nelson-Oppen theory combiner.
//!
//! Replaces bespoke combined solver adapters with a single implementation
//! of the Nelson-Oppen fixpoint loop, parameterized by which sub-solvers
//! participate. Each theory is optional except EUF (always present).
//!
//! # Supported Combinations
//!
//! | LIA | LRA | Arrays | Replaces           | Logic     |
//! |-----|-----|--------|--------------------|-----------|
//! |     |     | yes    | ArrayEufSolver     | QF_AX     |
//! | yes |     |        | UfLiaSolver        | QF_UFLIA  |
//! |     | yes |        | UfLraSolver        | QF_UFLRA  |
//! | yes |     | yes    | AufLiaSolver       | QF_AUFLIA |
//! |     | yes | yes    | AufLraSolver       | QF_AUFLRA |

// Wave 1: TheoryCombiner now used in production dispatch (#6332).

use z4_arrays::ArraySolver;
use z4_core::{Sort, TermData, TermId, TermStore, TheoryResult, TheorySolver};
use z4_euf::EufSolver;
use z4_lia::LiaSolver;
use z4_lra::LraSolver;

use super::check_loops::defer_non_local_result;
use super::interface_bridge::InterfaceBridge;
use crate::term_helpers::{
    arg_involves_select_or_store, involves_array, involves_int_arithmetic,
    involves_real_arithmetic, is_select_or_store, is_select_real_equality, is_uf_int_equality,
    is_uf_real_equality,
};

/// A centralized Nelson-Oppen theory combiner.
///
/// Implements the Nelson-Oppen fixpoint loop once, parameterized by which
/// sub-solvers participate. EUF is always present; LIA, LRA, and Arrays
/// are optional.
///
/// This replaces the bespoke per-logic adapters (`UfLiaSolver`, `AufLiaSolver`,
/// etc.) with a single implementation of the check loop, equality propagation,
/// push/pop, and assert_literal routing. Fixing a bug in the N-O loop fixes
/// it for ALL logic combinations simultaneously.
pub struct TheoryCombiner<'a> {
    pub(super) terms: &'a TermStore,
    pub(super) euf: EufSolver<'a>,
    pub(super) lia: Option<LiaSolver<'a>>,
    pub(super) lra: Option<LraSolver>,
    pub(super) arrays: Option<ArraySolver<'a>>,
    /// Monotonic counter for mutations visible to the array sub-solver.
    ///
    /// Used to skip redundant `arrays.check()` calls in the N-O loop when the
    /// array state has not changed since the last successful, no-new-equalities
    /// array pass (#6820).
    pub(super) array_epoch: u64,
    /// Array epoch at which `arrays.check()` last returned `Sat` and emitted no
    /// new equalities. When equal to `array_epoch`, the next N-O iteration can
    /// skip the array step entirely.
    pub(super) array_quiescent_epoch: Option<u64>,
    pub(super) interface: Option<InterfaceBridge>,
    pub(super) scope_depth: usize,
    pub(super) label: &'static str,
    pub(super) arith_prop_label: &'static str,
    pub(super) euf_prop_label: &'static str,
    pub(super) arr_prop_label: &'static str,
}

impl<'a> TheoryCombiner<'a> {
    // --- Constructors ---

    /// Create a combiner for EUF + Arrays (replaces ArrayEufSolver, QF_AX).
    pub fn array_euf(terms: &'a TermStore) -> Self {
        let mut arrays = ArraySolver::new(terms);
        arrays.set_defer_expensive_checks(true);
        Self {
            terms,
            euf: EufSolver::new(terms),
            lia: None,
            lra: None,
            arrays: Some(arrays),
            array_epoch: 0,
            array_quiescent_epoch: None,
            interface: None,
            scope_depth: 0,
            label: "AX",
            arith_prop_label: "",
            euf_prop_label: "AX-EUF",
            arr_prop_label: "AX-ARR",
        }
    }

    /// Create a combiner for EUF + LIA (replaces UfLiaSolver, QF_UFLIA).
    pub fn uf_lia(terms: &'a TermStore) -> Self {
        let mut lia = LiaSolver::new(terms);
        lia.set_combined_theory_mode(true);
        Self {
            terms,
            euf: EufSolver::new(terms),
            lia: Some(lia),
            lra: None,
            arrays: None,
            array_epoch: 0,
            array_quiescent_epoch: None,
            interface: Some(InterfaceBridge::new()),
            scope_depth: 0,
            label: "UFLIA",
            arith_prop_label: "UFLIA-LIA",
            euf_prop_label: "UFLIA-EUF",
            arr_prop_label: "",
        }
    }

    /// Create a combiner for EUF + LRA (replaces UfLraSolver, QF_UFLRA).
    pub fn uf_lra(terms: &'a TermStore) -> Self {
        let mut lra = LraSolver::new(terms);
        lra.set_combined_theory_mode(true);
        Self {
            terms,
            euf: EufSolver::new(terms),
            lia: None,
            lra: Some(lra),
            arrays: None,
            array_epoch: 0,
            array_quiescent_epoch: None,
            interface: Some(InterfaceBridge::new()),
            scope_depth: 0,
            label: "UFLRA",
            arith_prop_label: "UFLRA-LRA",
            euf_prop_label: "UFLRA-EUF",
            arr_prop_label: "",
        }
    }

    /// Create a combiner for EUF + LIA + Arrays (replaces AufLiaSolver, QF_AUFLIA).
    pub fn auf_lia(terms: &'a TermStore) -> Self {
        let mut lia = LiaSolver::new(terms);
        lia.set_combined_theory_mode(true);
        let mut arrays = ArraySolver::new(terms);
        arrays.set_defer_expensive_checks(true);
        Self {
            terms,
            euf: EufSolver::new(terms),
            lia: Some(lia),
            lra: None,
            arrays: Some(arrays),
            array_epoch: 0,
            array_quiescent_epoch: None,
            interface: Some(InterfaceBridge::new()),
            scope_depth: 0,
            label: "AUFLIA",
            arith_prop_label: "AUFLIA-LIA",
            euf_prop_label: "AUFLIA-EUF",
            arr_prop_label: "AUFLIA-ARR",
        }
    }

    /// Create a combiner for EUF + LRA + Arrays (replaces AufLraSolver, QF_AUFLRA).
    pub fn auf_lra(terms: &'a TermStore) -> Self {
        let mut lra = LraSolver::new(terms);
        lra.set_combined_theory_mode(true);
        let mut arrays = ArraySolver::new(terms);
        arrays.set_defer_expensive_checks(true);
        Self {
            terms,
            euf: EufSolver::new(terms),
            lia: None,
            lra: Some(lra),
            arrays: Some(arrays),
            array_epoch: 0,
            array_quiescent_epoch: None,
            interface: Some(InterfaceBridge::new()),
            scope_depth: 0,
            label: "AUFLRA",
            arith_prop_label: "AUFLRA-LRA",
            euf_prop_label: "AUFLRA-EUF",
            arr_prop_label: "AUFLRA-ARR",
        }
    }

    // Model extraction and LIA state preservation: see combiner_models.rs

    // Private N-O check helpers: see combiner_check.rs
    // (evaluate_bridge, handle_fixpoint, propagate_array_indices, etc.)

    /// Check if a term is tracked as an interface arithmetic term.
    #[cfg(test)]
    pub(crate) fn has_interface_term(&self, term: TermId) -> bool {
        self.interface
            .as_ref()
            .is_some_and(|ib| ib.contains_arith_term(&term))
    }

    pub(super) fn mark_arrays_dirty(&mut self) {
        if self.arrays.is_some() {
            self.array_epoch = self.array_epoch.wrapping_add(1);
            self.array_quiescent_epoch = None;
        }
    }

    fn suggest_phase_with_arrays(&self, atom: TermId) -> Option<bool> {
        if let TermData::App(ref sym, ref args) = self.terms.get(atom) {
            if sym.name() == "=" && args.len() == 2 {
                if matches!(self.terms.sort(args[0]), Sort::Array(_)) {
                    return None;
                }
                let lhs_is_simple = !is_select_or_store(self.terms, args[0]);
                let rhs_is_simple = !is_select_or_store(self.terms, args[1]);
                if lhs_is_simple && rhs_is_simple {
                    return Some(false);
                }
            }
        }
        if let TermData::App(ref sym, ref args) = self.terms.get(atom) {
            let name = sym.name();
            if (name == "<=" || name == ">=" || name == "<" || name == ">")
                && args.len() == 2
                && (arg_involves_select_or_store(self.terms, args[0])
                    || arg_involves_select_or_store(self.terms, args[1]))
            {
                return None;
            }
        }
        if let Some(lia) = &self.lia {
            return lia.suggest_phase(atom);
        }
        if let Some(lra) = &self.lra {
            return lra.suggest_phase(atom);
        }
        None
    }
}

impl TheorySolver for TheoryCombiner<'_> {
    fn register_atom(&mut self, atom: TermId) {
        if let Some(lia) = &mut self.lia {
            lia.register_atom(atom);
        }
        if let Some(lra) = &mut self.lra {
            lra.register_atom(atom);
        }
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.euf.assert_literal(literal, value);
        if let Some(arrays) = &mut self.arrays {
            arrays.assert_literal(literal, value);
            // #6820: only invalidate array quiescence when the literal
            // can change the array solver's equality / disequality state.
            // This includes array terms plus equality/distinct literals on
            // non-array operands (for example index equalities such as
            // `(= i j)`), while pure non-equality SAT literals remain safe
            // to skip.
            if involves_array(self.terms, literal) {
                self.mark_arrays_dirty();
            }
        }
        if let Some(lia) = &mut self.lia {
            if involves_int_arithmetic(self.terms, literal) {
                lia.assert_literal(literal, value);
            } else if let Some((lhs, rhs)) = is_uf_int_equality(self.terms, literal) {
                if value {
                    let reason = z4_core::TheoryLit::new(literal, true);
                    lia.assert_shared_equality(lhs, rhs, &[reason]);
                } else {
                    let reason = z4_core::TheoryLit::new(literal, false);
                    lia.assert_shared_disequality(lhs, rhs, &[reason]);
                }
            }
            if let Some(interface) = &mut self.interface {
                interface.track_interface_term(self.terms, literal);
                interface.collect_int_constants(self.terms, literal);
                interface.track_uf_arith_args(self.terms, literal);
            }
        } else if let Some(lra) = &mut self.lra {
            if self.arrays.is_some() {
                if let Some((lhs, rhs)) = is_select_real_equality(self.terms, literal) {
                    let reason = z4_core::TheoryLit::new(literal, value);
                    if value {
                        lra.assert_shared_equality(lhs, rhs, &[reason]);
                    } else {
                        lra.assert_shared_disequality(lhs, rhs, &[reason]);
                    }
                    if let Some(interface) = &mut self.interface {
                        interface.track_interface_term(self.terms, literal);
                        interface.collect_real_constants(self.terms, literal);
                        interface.track_uf_arith_args(self.terms, literal);
                    }
                    return;
                }
            }
            if involves_real_arithmetic(self.terms, literal) {
                lra.assert_literal(literal, value);
            } else if let Some((lhs, rhs)) = is_uf_real_equality(self.terms, literal) {
                if value {
                    let reason = z4_core::TheoryLit::new(literal, true);
                    lra.assert_shared_equality(lhs, rhs, &[reason]);
                } else {
                    let reason = z4_core::TheoryLit::new(literal, false);
                    lra.assert_shared_disequality(lhs, rhs, &[reason]);
                }
            }
            if let Some(interface) = &mut self.interface {
                interface.track_interface_term(self.terms, literal);
                interface.collect_real_constants(self.terms, literal);
                interface.track_uf_arith_args(self.terms, literal);
            }
        }
    }

    fn check(&mut self) -> TheoryResult {
        self.nelson_oppen_check()
    }

    fn check_during_propagate(&mut self) -> TheoryResult {
        if let Some(lia) = &mut self.lia {
            let result = defer_non_local_result(lia.check_during_propagate());
            if !matches!(result, TheoryResult::Sat) {
                return result;
            }
        } else if let Some(lra) = &mut self.lra {
            let result = defer_non_local_result(lra.check_during_propagate());
            if !matches!(result, TheoryResult::Sat) {
                return result;
            }
        }

        let euf_result = defer_non_local_result(self.euf.check_during_propagate());
        if !matches!(euf_result, TheoryResult::Sat) {
            return euf_result;
        }

        if let Some(arrays) = &mut self.arrays {
            let result = defer_non_local_result(arrays.check_during_propagate());
            if !matches!(result, TheoryResult::Sat) {
                return result;
            }
        }

        TheoryResult::Sat
    }

    fn needs_final_check_after_sat(&self) -> bool {
        true
    }

    fn propagate(&mut self) -> Vec<z4_core::TheoryPropagation> {
        let mut props = self.euf.propagate();
        if let Some(lia) = &mut self.lia {
            props.extend(lia.propagate());
        }
        if let Some(lra) = &mut self.lra {
            props.extend(lra.propagate());
        }
        if let Some(arrays) = &mut self.arrays {
            props.extend(arrays.propagate());
        }
        props
    }

    fn push(&mut self) {
        self.scope_depth += 1;
        self.euf.push();
        if let Some(lia) = &mut self.lia {
            lia.push();
        }
        if let Some(lra) = &mut self.lra {
            lra.push();
        }
        if let Some(arrays) = &mut self.arrays {
            arrays.push();
        }
        if self.arrays.is_some() {
            self.mark_arrays_dirty();
        }
        if let Some(interface) = &mut self.interface {
            interface.push();
        }
    }

    fn pop(&mut self) {
        if self.scope_depth == 0 {
            // Graceful no-op: pop at depth 0 is a caller error but not fatal.
            return;
        }
        self.scope_depth -= 1;
        self.euf.pop();
        if let Some(lia) = &mut self.lia {
            lia.pop();
        }
        if let Some(lra) = &mut self.lra {
            lra.pop();
        }
        if let Some(arrays) = &mut self.arrays {
            arrays.pop();
        }
        if self.arrays.is_some() {
            self.mark_arrays_dirty();
        }
        if let Some(interface) = &mut self.interface {
            interface.pop();
        }
    }

    fn reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: TheoryCombiner({})::reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.label,
            self.scope_depth,
        );
        self.euf.reset();
        if let Some(lia) = &mut self.lia {
            lia.reset();
        }
        if let Some(lra) = &mut self.lra {
            lra.reset();
        }
        if let Some(arrays) = &mut self.arrays {
            arrays.reset();
        }
        if self.arrays.is_some() {
            self.mark_arrays_dirty();
        }
        if let Some(interface) = &mut self.interface {
            interface.reset();
        }
    }

    fn soft_reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: TheoryCombiner({})::soft_reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.label,
            self.scope_depth,
        );
        self.euf.soft_reset();
        if let Some(lia) = &mut self.lia {
            lia.soft_reset();
        }
        if let Some(lra) = &mut self.lra {
            lra.soft_reset();
        }
        if let Some(arrays) = &mut self.arrays {
            arrays.soft_reset();
        }
        if self.arrays.is_some() {
            self.mark_arrays_dirty();
        }
        if let Some(interface) = &mut self.interface {
            interface.reset();
        }
    }

    fn supports_theory_aware_branching(&self) -> bool {
        if self.arrays.is_some() {
            return true;
        }
        if let Some(lia) = &self.lia {
            return lia.supports_theory_aware_branching();
        }
        if let Some(lra) = &self.lra {
            return lra.supports_theory_aware_branching();
        }
        false
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        if self.arrays.is_some() {
            return self.suggest_phase_with_arrays(atom);
        }
        if let Some(lia) = &self.lia {
            return lia.suggest_phase(atom);
        }
        if let Some(lra) = &self.lra {
            return lra.suggest_phase(atom);
        }
        None
    }

    fn sort_atom_index(&mut self) {
        if let Some(lia) = &mut self.lia {
            lia.sort_atom_index();
        }
        if let Some(lra) = &mut self.lra {
            lra.sort_atom_index();
        }
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        if let Some(lia) = &self.lia {
            return lia.generate_bound_axiom_terms();
        }
        if let Some(lra) = &self.lra {
            return lra.generate_bound_axiom_terms();
        }
        Vec::new()
    }

    fn generate_incremental_bound_axioms(&self, atom: TermId) -> Vec<(TermId, bool, TermId, bool)> {
        if let Some(lia) = &self.lia {
            return lia.generate_incremental_bound_axioms(atom);
        }
        if let Some(lra) = &self.lra {
            return lra.generate_incremental_bound_axioms(atom);
        }
        Vec::new()
    }

    fn note_applied_theory_lemma(&mut self, clause: &[z4_core::TheoryLit]) {
        // Forward to arrays sub-solver for dedup tracking.
        // #6694 fix: the array solver's pop() now clears applied_theory_lemmas,
        // so backtracking no longer causes stale dedup entries.
        if let Some(arrays) = &mut self.arrays {
            arrays.note_applied_theory_lemma(clause);
        }
    }

    fn supports_farkas_semantic_check(&self) -> bool {
        self.lra.is_some()
    }

    fn registered_atom_count(&self) -> usize {
        let mut count = self.euf.registered_atom_count();
        if let Some(lia) = &self.lia {
            count += lia.registered_atom_count();
        }
        if let Some(lra) = &self.lra {
            count += lra.registered_atom_count();
        }
        count
    }

    fn explain_propagation(&mut self, lit: TermId, reason_data: u64) -> Option<Vec<TermId>> {
        if let Some(lia) = &mut self.lia {
            if let Some(result) = lia.explain_propagation(lit, reason_data) {
                return Some(result);
            }
        }
        if let Some(lra) = &mut self.lra {
            if let Some(result) = lra.explain_propagation(lit, reason_data) {
                return Some(result);
            }
        }
        self.euf.explain_propagation(lit, reason_data)
    }

    fn mark_propagation_rejected(&mut self, lit: TermId, reason_data: u64) {
        if let Some(lia) = &mut self.lia {
            lia.mark_propagation_rejected(lit, reason_data);
        }
        if let Some(lra) = &mut self.lra {
            lra.mark_propagation_rejected(lit, reason_data);
        }
        self.euf.mark_propagation_rejected(lit, reason_data);
    }

    fn note_conflict_atom(&mut self, atom: TermId) {
        if let Some(lia) = &mut self.lia {
            lia.note_conflict_atom(atom);
        }
        if let Some(lra) = &mut self.lra {
            lra.note_conflict_atom(atom);
        }
        self.euf.note_conflict_atom(atom);
    }
}
