// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use z4_core::{TermId, TermStore, TheoryResult, TheorySolver};
use z4_euf::{EufModel, EufSolver};
use z4_lia::{LiaModel, LiaSolver};
use z4_seq::{SeqModel, SeqSolver};

use crate::combined_solvers::check_loops::{
    assert_fixpoint_convergence, debug_nelson_oppen, forward_non_sat, propagate_equalities_to,
    triage_lia_result,
};
use crate::combined_solvers::interface_bridge::InterfaceBridge;
use crate::term_helpers::contains_arithmetic_ops;

/// Result of a single Nelson-Oppen iteration.
enum IterResult {
    /// Fixpoint or conflict reached — return this result.
    Done(TheoryResult),
    /// New equalities found — continue iterating.
    Continue,
}

/// Combined EUF + Seq + LIA theory solver for QF_SEQLIA.
///
/// Wraps `EufSolver`, `SeqSolver`, and `LiaSolver` with Nelson-Oppen
/// style theory combination. The SeqSolver handles sequence reasoning
/// (unit injectivity, unit-empty conflicts). LIA handles integer
/// arithmetic including `seq.len` terms (which LIA treats as opaque Int
/// variables). EUF handles congruence reasoning across all sorts.
///
/// Length axioms (e.g., `seq.len(seq.unit(x)) = 1`, `seq.len(s) >= 0`)
/// are injected by the executor before Tseitin encoding, following the
/// same pattern as StringsLiaSolver.
///
/// See #5958 for the soundness bug this solver fixes.
pub(crate) struct UfSeqLiaSolver<'a> {
    /// Reference to term store for inspecting literals.
    terms: &'a TermStore,
    /// EUF solver for equality and congruence reasoning.
    euf: EufSolver<'a>,
    /// Seq solver for sequence-specific axioms.
    seq: SeqSolver<'a>,
    /// LIA solver for linear integer arithmetic (seq.len constraints).
    lia: LiaSolver<'a>,
    /// Shared Nelson-Oppen interface term tracking.
    interface: InterfaceBridge,
    /// Scope depth counter for push/pop symmetry checking (#4995).
    scope_depth: usize,
}

impl<'a> UfSeqLiaSolver<'a> {
    /// Create a new combined EUF+Seq+LIA solver.
    pub(crate) fn new(terms: &'a TermStore) -> Self {
        let mut lia = LiaSolver::new(terms);
        lia.set_combined_theory_mode(true);
        Self {
            terms,
            euf: EufSolver::new(terms),
            seq: SeqSolver::new(terms),
            lia,
            interface: InterfaceBridge::new(),
            scope_depth: 0,
        }
    }

    /// Extract all models for model generation.
    pub(crate) fn extract_models(&mut self) -> (EufModel, SeqModel, Option<LiaModel>) {
        (
            self.euf.extract_model(),
            self.seq.extract_model(),
            self.lia.extract_model(),
        )
    }

    /// Replay learned LIA cuts into the freshly-created theory.
    pub(crate) fn replay_learned_cuts(&mut self) {
        self.lia.replay_learned_cuts();
    }

    /// Identity accessor for split-loop macro compatibility.
    pub(crate) fn lra_solver(&self) -> &Self {
        self
    }

    /// Collect all bound conflicts from the inner LIA solver.
    pub(crate) fn collect_all_bound_conflicts(
        &self,
        skip_first: bool,
    ) -> Vec<z4_core::TheoryConflict> {
        self.lia.collect_all_bound_conflicts(skip_first)
    }

    /// Export learned LIA state for cross-iteration persistence.
    pub(crate) fn take_learned_state(
        &mut self,
    ) -> (
        Vec<z4_lia::StoredCut>,
        hashbrown::HashSet<z4_lia::HnfCutKey>,
    ) {
        self.lia.take_learned_state()
    }

    /// Import learned LIA state from a previous iteration.
    pub(crate) fn import_learned_state(
        &mut self,
        cuts: Vec<z4_lia::StoredCut>,
        seen: hashbrown::HashSet<z4_lia::HnfCutKey>,
    ) {
        self.lia.import_learned_state(cuts, seen);
    }

    /// Export Diophantine solver state for cross-iteration persistence.
    pub(crate) fn take_dioph_state(&mut self) -> z4_lia::DiophState {
        self.lia.take_dioph_state()
    }

    /// Import Diophantine solver state from a previous iteration.
    pub(crate) fn import_dioph_state(&mut self, state: z4_lia::DiophState) {
        self.lia.import_dioph_state(state);
    }

    /// Check EUF's equivalence classes for Seq-specific conflicts.
    ///
    /// Same logic as `UfSeqSolver::check_seq_euf_classes` — detects
    /// transitive unit-empty conflicts and unit injectivity via EUF classes.
    #[allow(clippy::result_large_err)]
    fn check_seq_euf_classes(&mut self) -> Result<usize, TheoryResult> {
        let unit_terms: Vec<TermId> = self.seq.unit_terms().collect();
        let empty_terms: Vec<TermId> = self.seq.empty_terms().collect();
        let mut new_eq_count = 0usize;

        // Check if any unit term shares an EUF class with an empty term.
        for &unit_t in &unit_terms {
            for &empty_t in &empty_terms {
                if self.euf.are_equal(unit_t, empty_t) {
                    let reasons = self.euf.explain(unit_t, empty_t);
                    return Err(TheoryResult::Unsat(reasons));
                }
            }
        }

        // Check unit injectivity via EUF classes.
        for i in 0..unit_terms.len() {
            let a = unit_terms[i];
            for &b in &unit_terms[i + 1..] {
                if self.euf.are_equal(a, b) {
                    if let (Some(elem_a), Some(elem_b)) =
                        (self.seq.unit_element(a), self.seq.unit_element(b))
                    {
                        if elem_a != elem_b && !self.euf.are_equal(elem_a, elem_b) {
                            let reasons = self.euf.explain(a, b);
                            self.seq.assert_shared_equality(elem_a, elem_b, &reasons);
                            self.euf.assert_shared_equality(elem_a, elem_b, &reasons);
                            new_eq_count += 1;
                        }
                    }
                }
            }
        }

        Ok(new_eq_count)
    }

    /// Run one iteration of the Nelson-Oppen fixpoint loop.
    #[allow(clippy::result_large_err)]
    fn check_iteration(&mut self, debug: bool, iteration: usize) -> IterResult {
        // 1. Check Seq for direct conflicts (unit = empty).
        let seq_result = self.seq.check();
        if let Some(r) = forward_non_sat(seq_result) {
            return IterResult::Done(r);
        }

        // 2. Propagate Seq → EUF equalities (unit injectivity).
        let seq_eq = match propagate_equalities_to(
            &mut self.seq,
            &mut self.euf,
            debug,
            "UFSEQLIA-Seq",
            iteration,
        ) {
            Ok(n) => n,
            Err(c) => return IterResult::Done(c),
        };

        // 3. Check LIA — Unsat returns immediately; splits deferred.
        let lia_result = self.lia.check();
        let lia_is_unknown = matches!(&lia_result, TheoryResult::Unknown);
        let (deferred_lia, lia_early) = triage_lia_result(lia_result);
        if let Some(early) = lia_early {
            return IterResult::Done(early);
        }

        // 4. Propagate LIA → EUF equalities.
        let lia_eq = match propagate_equalities_to(
            &mut self.lia,
            &mut self.euf,
            debug,
            "UFSEQLIA-LIA",
            iteration,
        ) {
            Ok(n) => n,
            Err(c) => return IterResult::Done(c),
        };

        // 5. Check EUF.
        if let Some(r) = forward_non_sat(self.euf.check()) {
            return IterResult::Done(r);
        }

        // 6. Check EUF classes for Seq-specific conflicts.
        let class_eq = match self.check_seq_euf_classes() {
            Err(c) => return IterResult::Done(c),
            Ok(n) => n,
        };

        // 7. Propagate EUF → LIA and EUF → Seq equalities.
        let euf_lia = match propagate_equalities_to(
            &mut self.euf,
            &mut self.lia,
            debug,
            "UFSEQLIA-EUF-LIA",
            iteration,
        ) {
            Ok(n) => n,
            Err(c) => return IterResult::Done(c),
        };
        let euf_seq = match propagate_equalities_to(
            &mut self.euf,
            &mut self.seq,
            debug,
            "UFSEQLIA-EUF-Seq",
            iteration,
        ) {
            Ok(n) => n,
            Err(c) => return IterResult::Done(c),
        };

        if seq_eq + lia_eq + class_eq + euf_lia + euf_seq == 0 {
            let _ = (debug, iteration); // used for debug logging
            if lia_is_unknown {
                return IterResult::Done(TheoryResult::Unknown);
            }
            if let Some(split) = deferred_lia {
                return IterResult::Done(split);
            }
            assert_fixpoint_convergence(
                "UFSEQLIA",
                &mut [&mut self.seq, &mut self.lia, &mut self.euf],
            );
            return IterResult::Done(TheoryResult::Sat);
        }
        IterResult::Continue
    }
}

impl TheorySolver for UfSeqLiaSolver<'_> {
    fn register_atom(&mut self, atom: TermId) {
        self.lia.register_atom(atom);
    }

    fn assert_literal(&mut self, literal: TermId, value: bool) {
        self.euf.assert_literal(literal, value);
        self.seq.assert_literal(literal, value);
        if contains_arithmetic_ops(self.terms, literal)
            || crate::term_helpers::contains_seq_len_ops(self.terms, literal)
        {
            self.lia.assert_literal(literal, value);
        }
        // Track interface terms for Nelson-Oppen bridge.
        self.interface.track_interface_term(self.terms, literal);
        self.interface.collect_int_constants(self.terms, literal);
    }

    fn check(&mut self) -> TheoryResult {
        let debug = debug_nelson_oppen() || std::env::var("Z4_DBG_UFSEQLIA").is_ok();
        const MAX_ITERATIONS: usize = 100;

        for iteration in 0..MAX_ITERATIONS {
            match self.check_iteration(debug, iteration) {
                IterResult::Done(result) => return result,
                IterResult::Continue => {}
            }
            // In debug builds, catch non-convergence early. In release,
            // fall through to the Unknown return below (#6197).
            debug_assert!(
                iteration < MAX_ITERATIONS - 1,
                "BUG: UFSEQLIA N-O loop did not converge in {MAX_ITERATIONS} iterations"
            );
        }
        TheoryResult::Unknown
    }

    delegate_propagate!(euf, seq, lia);

    fn supports_theory_aware_branching(&self) -> bool {
        self.lia.supports_theory_aware_branching()
    }

    fn suggest_phase(&self, atom: TermId) -> Option<bool> {
        self.lia.suggest_phase(atom)
    }

    fn sort_atom_index(&mut self) {
        self.lia.sort_atom_index();
    }

    fn generate_bound_axiom_terms(&self) -> Vec<(TermId, bool, TermId, bool)> {
        self.lia.generate_bound_axiom_terms()
    }

    fn generate_incremental_bound_axioms(&self, atom: TermId) -> Vec<(TermId, bool, TermId, bool)> {
        self.lia.generate_incremental_bound_axioms(atom)
    }

    fn push(&mut self) {
        self.scope_depth += 1;
        self.euf.push();
        self.seq.push();
        self.lia.push();
        self.interface.push();
    }

    fn pop(&mut self) {
        debug_assert!(
            self.scope_depth > 0,
            "BUG: UfSeqLiaSolver::pop() called at scope depth 0 (underflow)"
        );
        if self.scope_depth == 0 {
            return;
        }
        self.scope_depth -= 1;
        self.euf.pop();
        self.seq.pop();
        self.lia.pop();
        self.interface.pop();
    }

    fn reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: UfSeqLiaSolver::reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.euf.reset();
        self.seq.reset();
        self.lia.reset();
        self.interface.reset();
    }

    fn soft_reset(&mut self) {
        assert!(
            self.scope_depth == 0,
            "BUG: UfSeqLiaSolver::soft_reset() called with non-zero scope depth {} (unbalanced push/pop)",
            self.scope_depth,
        );
        self.euf.soft_reset();
        self.seq.soft_reset();
        self.lia.soft_reset();
        self.interface.reset();
    }
}
