// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `NraSolver`.
//!
//! Implements the DPLL(T) theory interface for the nonlinear real arithmetic theory.

use super::*;

impl TheorySolver for NraSolver<'_> {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        // Undo any tentative patch before asserting new literals —
        // assertions must go into the real scope, not the patch scope.
        self.undo_tentative_patch();

        let (term, val) = match self.terms.get(literal) {
            TermData::Not(inner) => (*inner, !value),
            _ => (literal, value),
        };

        self.asserted.push((term, val));
        self.collect_nonlinear_terms(term);

        if let Some((subject, constraint)) = sign::extract_sign_constraint(self.terms, term, val) {
            sign::record_sign_constraint(
                self.terms,
                &self.aux_to_monomial,
                &mut self.sign_constraints,
                &mut self.var_sign_constraints,
                subject,
                constraint,
                term,
            );
        }

        self.lra.assert_literal(literal, value);
    }

    fn check(&mut self) -> TheoryResult {
        self.check_count += 1;
        // Undo any stale tentative patch from a previous check —
        // the SAT solver may have backtracked or asserted new literals.
        self.undo_tentative_patch();
        maybe_grow_nra_stack(|| self.nra_check_loop())
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        let props = self.lra.propagate();
        self.propagation_count += props.len() as u64;
        props
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        let mut stats = vec![
            ("nra_checks", self.check_count),
            ("nra_conflicts", self.conflict_count),
            ("nra_propagations", self.propagation_count),
            ("nra_tangent_lemmas", self.tangent_lemma_count),
            ("nra_patches", self.patch_count),
            ("nra_sign_cuts", self.sign_cut_count),
        ];
        stats.extend(self.lra.collect_statistics());
        stats
    }

    fn push(&mut self) {
        // Undo tentative patch scope before creating a new real scope
        self.undo_tentative_patch();
        self.scopes
            .push((self.asserted.len(), self.div_purifications.len()));
        self.sign_constraint_snapshots.push((
            self.sign_constraints.clone(),
            self.var_sign_constraints.clone(),
        ));
        self.lra.push();
    }

    fn pop(&mut self) {
        // Undo tentative patch scope before popping the real scope
        self.undo_tentative_patch();
        if let Some((assert_mark, div_mark)) = self.scopes.pop() {
            self.asserted.truncate(assert_mark);
            self.div_purifications.truncate(div_mark);
        }
        if let Some((sc, vsc)) = self.sign_constraint_snapshots.pop() {
            self.sign_constraints = sc;
            self.var_sign_constraints = vsc;
        }
        self.lra.pop();
    }

    fn reset(&mut self) {
        self.monomials.clear();
        self.aux_to_monomial.clear();
        self.sign_constraints.clear();
        self.var_sign_constraints.clear();
        self.sign_constraint_snapshots.clear();
        self.div_purifications.clear();
        self.asserted.clear();
        self.scopes.clear();
        self.tentative_depth = 0;
        self.lra.reset();
    }

    fn supports_farkas_semantic_check(&self) -> bool {
        self.lra.supports_farkas_semantic_check()
    }

    fn propagate_equalities(&mut self) -> z4_core::EqualityPropagationResult {
        self.lra.propagate_equalities()
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        self.lra.assert_shared_equality(lhs, rhs, reason);
    }

    fn assert_shared_disequality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        self.lra.assert_shared_disequality(lhs, rhs, reason);
    }

    fn internalize_atom(&mut self, term: TermId) {
        self.lra.internalize_atom(term);
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        self.lra.suggest_phase(atom)
    }
}
