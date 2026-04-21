// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TheorySolver` trait implementation for `ArraySolver`.
//!
//! Implements the DPLL(T) theory interface for the array theory.
//! Check logic is in `theory_check.rs`, propagation in `theory_propagate.rs`.

use super::*;

impl TheorySolver for ArraySolver<'_> {
    fn assert_literal(&mut self, literal: TermId, value: bool) {
        let (term, val) = z4_core::unwrap_not(self.terms, literal, value);
        let previous = self.assigns.get(&term).copied();
        self.record_assignment(term, val);

        // #6546 Packet 4: direct asserted array equalities must drive the same
        // incremental ROW2 queueing path as shared equalities. Without this,
        // `a = b` learned/assumed at the SAT layer leaves `array_vars`
        // unmerged and misses the eager `(store(b, i, v), select(a, j))`
        // registrations that `notify_equality()` performs.
        if !val || previous == Some(true) {
            return;
        }

        let TermData::App(sym, args) = self.terms.get(term) else {
            return;
        };
        if sym.name() != "=" || args.len() != 2 {
            return;
        }
        if !matches!(self.terms.sort(args[0]), Sort::Array(_))
            || !matches!(self.terms.sort(args[1]), Sort::Array(_))
        {
            return;
        }

        self.notify_equality(args[0], args[1]);
    }

    fn assert_shared_equality(&mut self, lhs: TermId, rhs: TermId, reason: &[TheoryLit]) {
        // Forward to assert_external_equality for the eq-graph and also
        // trigger notify_equality for eager ROW2 axiom queuing (#6546).
        self.assert_external_equality(lhs, rhs);
        let _ = reason; // reason tracked via external_eqs for eq_adj
        self.notify_equality(lhs, rhs);
    }

    fn check(&mut self) -> TheoryResult {
        self.check_impl()
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        vec![
            ("arrays_checks", self.check_count),
            ("arrays_conflicts", self.conflict_count),
            ("arrays_propagations", self.propagation_count),
        ]
    }

    fn note_applied_theory_lemma(&mut self, clause: &[TheoryLit]) {
        self.applied_theory_lemmas.insert(clause.to_vec());
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        self.propagate_impl()
    }

    /// Discover equalities implied by array axioms for Nelson-Oppen propagation (#4665).
    ///
    /// Delegates to `propagation.rs`. See [`Self::propagate_equalities_impl`].
    fn propagate_equalities(&mut self) -> EqualityPropagationResult {
        self.propagate_equalities_impl()
    }

    fn push(&mut self) {
        self.scopes.push(self.trail.len());
    }

    fn pop(&mut self) {
        let Some(mark) = self.scopes.pop() else {
            return;
        };
        let mut eq_graph_changed = !self.external_eqs.is_empty();
        while self.trail.len() > mark {
            let (term, prev) = self.trail.pop().expect("trail length checked above");
            let current = self.assigns.get(&term).copied();
            if self.is_equality_term(term)
                && Self::equality_assignment_affects_eq_graph(prev, current)
            {
                eq_graph_changed = true;
            }
            match prev {
                Some(v) => {
                    self.assigns.insert(term, v);
                }
                None => {
                    self.assigns.remove(&term);
                }
            }
        }
        // Clear external facts — they're re-derived each check cycle (#4665)
        self.external_diseqs.clear();
        self.external_eqs.clear();
        self.sent_equalities.clear();
        self.sent_propagations.clear();
        // #6694: Clear applied-lemma dedup on pop so backtracking doesn't
        // suppress re-requesting ROW2 axioms in subsequent branches.
        self.applied_theory_lemmas.clear();
        // #6546: Clear event-driven ROW1 queue on backtrack since equalities
        // may no longer hold.
        self.pending_row1.clear();
        self.pending_row2_upward.clear();
        self.pending_self_store.clear();
        self.pending_registered_equalities.clear();
        // NOTE: Do NOT clear requested_model_eqs here. The dedup set persists
        // across pop/push cycles within the same problem to prevent infinite
        // NeedModelEquality loops in the N-O fixpoint. Cleared only in reset().
        self.dirty = true;
        self.assign_dirty = true;
        // #6546: Invalidate prop_eq and upward snapshots so propagate_equalities()
        // and check_row2_upward_with_guidance() re-scan after backtracking.
        self.prop_eq_snapshot = None;
        self.final_check_snapshot = None;
        if eq_graph_changed {
            self.note_eq_graph_changed();
        }
    }

    fn reset(&mut self) {
        let eq_graph_changed = !self.eq_adj.is_empty()
            || self.equiv_class_cache_version.is_some()
            || !self.external_eqs.is_empty();
        self.assigns.clear();
        self.trail.clear();
        self.scopes.clear();
        self.clear_term_caches();
        self.axiom_fingerprints.clear();
        self.row2_fingerprint_indices.clear();
        self.external_diseqs.clear();
        self.external_eqs.clear();
        self.sent_equalities.clear();
        self.sent_propagations.clear();
        self.requested_model_eqs.clear();
        self.applied_theory_lemmas.clear();
        self.dirty = true;
        self.assign_dirty = true;
        self.prop_eq_snapshot = None;
        self.final_check_snapshot = None;
        if eq_graph_changed {
            self.note_eq_graph_changed();
        }
    }
}

impl ArraySolver<'_> {
    /// Validate that a conflict explanation is sound: every literal in the
    /// explanation must be true in the current assignment. If any literal
    /// is false or unassigned, the conflict is spurious (#6741).
    #[cfg(debug_assertions)]
    pub(crate) fn validate_conflict_explanation(&self, reasons: &[TheoryLit]) {
        for (i, lit) in reasons.iter().enumerate() {
            let actual_value = self.assigns.get(&lit.term).copied();
            debug_assert!(
                actual_value == Some(lit.value),
                "Array conflict explanation lit[{i}] unsound: \
                 term={:?} expected={} actual={actual_value:?} \
                 term_data={:?}",
                lit.term,
                lit.value,
                self.terms.get(lit.term)
            );
        }
    }
}
