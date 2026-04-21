// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EUF, DT, and Array+EUF solving.

mod array_congruence;
mod array_fixpoint;
mod array_patterns;
mod array_row;
mod dt;
#[cfg(test)]
mod tests;

use super::super::Executor;
use crate::executor::theories::solve_harness::TheoryModels;
use crate::executor_types::{Result, SolveResult};
use crate::term_helpers::or_implies_eq_endpoints;
#[cfg(not(kani))]
use hashbrown::HashSet;
#[cfg(kani)]
use z4_core::kani_compat::DetHashSet as HashSet;
use z4_core::{TermId, TermStore, TheoryLemmaKind};
use z4_euf::EufSolver;

/// Collect all TermIds transitively reachable from the given root terms (#6726).
/// Used to scope array axiom generation to terms in the current assertion set,
/// excluding dead terms from popped scopes in the append-only TermStore.
pub(crate) fn reachable_term_set(terms: &TermStore, roots: &[TermId]) -> HashSet<TermId> {
    let mut visited = HashSet::with_capacity(roots.len() * 4);
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(t) = stack.pop() {
        if !visited.insert(t) {
            continue;
        }
        for child in terms.children(t) {
            stack.push(child);
        }
    }
    visited
}

/// Controls whether array ROW/ROW2b axioms are generated eagerly during
/// preprocessing or deferred to `ArraySolver::final_check()`.
///
/// Routes backed by `TheoryCombiner` (which includes `ArraySolver` with
/// `set_defer_expensive_checks(true)`) already have runtime lazy ROW
/// handling. Using `LazyRow2FinalCheck` on those routes avoids the
/// O(selects × stores) eager blowup from ROW2b while preserving ROW1
/// clauses that the SAT solver needs for basic store-chain reasoning.
///
/// Matches Z3's architecture: ROW1 (axiom 1) is always eager, ROW2b
/// (axiom 2b upward) is deferred to `final_check_eh` (#6546 Packet 4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::executor) enum ArrayAxiomMode {
    /// Generate all axioms eagerly: structural + ROW1 + ROW2b.
    /// Used by BV-array routes and paths without a lazy `ArraySolver`.
    EagerAll,
    /// Generate structural + ROW1 eagerly; defer ROW2b to
    /// `ArraySolver::final_check()`. Matches Z3's default behavior
    /// where `assert_store_axiom1` is always eager but `assert_store_axiom2`
    /// with `m_array_delay_exp_axiom=true` defers expensive instances.
    /// Used by TheoryCombiner-backed array routes (#6546 Packet 4).
    LazyRow2FinalCheck,
}

impl Executor {
    /// Check whether a term is in scope for array axiom generation (#6726).
    /// Returns `true` when no scope filter is active (non-incremental mode),
    /// when the term was created during the current fixpoint (idx >= start_len),
    /// or when the term is reachable from current assertions.
    #[inline]
    fn term_in_array_scope(&self, term_id: TermId) -> bool {
        match &self.array_axiom_scope {
            None => true,
            Some((reachable, start_len)) => {
                (term_id.0 as usize) >= *start_len || reachable.contains(&term_id)
            }
        }
    }

    fn push_array_axiom_assertion(&mut self, axiom: TermId) {
        self.ctx.assertions.push(axiom);
        if self.produce_proofs_enabled() {
            let _ = self
                .proof_tracker
                .add_theory_lemma_with_kind(
                    vec![axiom],
                    TheoryLemmaKind::ArraySelectStore { index_eq: false },
                );
        }
    }

    /// Solve QF_UF using eager DPLL(T) with theory-SAT interleaving.
    ///
    /// Uses `solve_incremental_split_loop_pipeline!` with `eager_extension: true`
    /// so the EUF solver runs as a TheoryExtension during BCP. This ensures all
    /// theory-relevant equality atoms are assigned by the SAT solver — the lazy
    /// pipeline could leave them unassigned and miss congruence closure conflicts.
    ///
    /// Or-eq-lemma implications (transitivity shortcuts for eq_diamond patterns)
    /// are injected as assertion-level implications that flow through Tseitin
    /// encoding automatically.
    pub(in crate::executor) fn solve_euf(&mut self) -> Result<SolveResult> {
        // Lift ITEs from equalities involving uninterpreted sorts.
        self.ctx.assertions = self.ctx.terms.lift_arithmetic_ite_all(&self.ctx.assertions);

        // Pre-compute or_eq_lemma pairs and inject as assertion-level
        // implications (¬or_term ∨ eq_term). These flow through Tseitin
        // encoding via pipeline_incremental_setup!, ensuring eq_terms become
        // active theory atoms via collect_active_theory_atoms.
        {
            let mut seen = HashSet::<(TermId, TermId)>::new();
            let len = self.ctx.terms.len();
            for idx in 0..len {
                let t = TermId(idx as u32);
                if let Some((a, b)) = or_implies_eq_endpoints(&self.ctx.terms, t) {
                    let eq_term = self.ctx.terms.mk_eq(a, b);
                    if seen.insert((t, eq_term)) {
                        let not_or = self.ctx.terms.mk_not(t);
                        let implication = self.ctx.terms.mk_or(vec![not_or, eq_term]);
                        self.ctx.assertions.push(implication);
                    }
                }
            }
        }

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline;
        self.with_isolated_incremental_state(None, |this| {
            solve_incremental_split_loop_pipeline!(this,
                tag: "EUF",
                persistent_sat_field: persistent_sat,
                create_theory: EufSolver::new(&this.ctx.terms),
                extract_models: |theory| {
                    theory.scope_model_to_roots(&this.ctx.assertions);
                    let euf = theory.extract_model();
                    theory.clear_model_scope();
                    TheoryModels {
                        euf: Some(euf),
                        ..TheoryModels::default()
                    }
                },
                max_splits: 1,
                pre_theory_import: |_theory, _lc, _hc, _ds| {},
                post_theory_export: |_theory| {
                    (vec![], Default::default(), Default::default())
                },
                eager_extension: true,
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.is_some_and(|dl| std::time::Instant::now() >= dl)
                }
            )
        })
    }
}
