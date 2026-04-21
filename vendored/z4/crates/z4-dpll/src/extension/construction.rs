// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! Construction, accessors, and bound-axiom generation for `TheoryExtension`.
//!
//! Extracted from `mod.rs` to keep that file under the 1,200-line target.

use std::cell::Cell;

#[cfg(not(kani))]
use hashbrown::{HashMap, HashSet};
#[cfg(kani)]
use z4_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use z4_core::{
    BoundRefinementRequest, FarkasAnnotation, Symbol, TermData, TermId, TermStore, TheoryLemmaKind,
    TheoryLit, TheorySolver,
};
use z4_sat::{Literal, Variable};

use super::{BoundRefinementHandoff, ProofContext, TheoryAxiomKey, TheoryExtension};
use crate::executor::BoundRefinementReplayKey;
use crate::proof_tracker::ProofTracker;
use crate::{DpllConstructionTimings, DpllEagerStats, PhaseTimer};

/// Returns `Some(LraFarkas)` if both terms are arithmetic comparisons and unit
/// Farkas coefficients validate; `None` otherwise.
pub(crate) fn infer_bound_axiom_arith_kind(
    terms: &TermStore,
    t1: TermId,
    t2: TermId,
    p1: bool,
    p2: bool,
) -> Option<TheoryLemmaKind> {
    // Both terms must be binary arithmetic comparisons.
    let is_arith_cmp = |tid: TermId| -> bool {
        matches!(
            terms.get(tid),
            TermData::App(Symbol::Named(name), args)
                if matches!(name.as_str(), "<=" | "<" | ">=" | ">" | "=") && args.len() == 2
        )
    };
    if !is_arith_cmp(t1) || !is_arith_cmp(t2) {
        return None;
    }

    // Validate unit Farkas coefficients against the conflict (negation of clause).
    let conflict_lits = [
        TheoryLit {
            term: t1,
            value: !p1,
        },
        TheoryLit {
            term: t2,
            value: !p2,
        },
    ];
    let unit_farkas = FarkasAnnotation::from_ints(&[1i64, 1]);
    if z4_core::proof_validation::verify_farkas_conflict_lits_full(
        terms,
        &conflict_lits,
        &unit_farkas,
    )
    .is_err()
    {
        return None;
    }

    Some(TheoryLemmaKind::LraFarkas)
}

impl<'a, T: TheorySolver> TheoryExtension<'a, T> {
    /// Create a new theory extension wrapper.
    pub(crate) fn new(
        theory: &'a mut T,
        var_to_term: &'a HashMap<u32, TermId>,
        term_to_var: &'a HashMap<TermId, u32>,
        theory_atoms: &'a [TermId],
        theory_atom_set: &'a HashSet<TermId>,
        terms: Option<&'a TermStore>,
        diagnostic_trace: Option<&'a crate::diagnostic_trace::DpllDiagnosticWriter>,
    ) -> Self {
        Self::new_with_construction_timings(
            theory,
            var_to_term,
            term_to_var,
            theory_atoms,
            theory_atom_set,
            terms,
            diagnostic_trace,
            None,
        )
    }

    /// Create a theory extension and optionally accumulate constructor timing.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new_with_construction_timings(
        theory: &'a mut T,
        var_to_term: &'a HashMap<u32, TermId>,
        term_to_var: &'a HashMap<TermId, u32>,
        theory_atoms: &'a [TermId],
        theory_atom_set: &'a HashSet<TermId>,
        terms: Option<&'a TermStore>,
        diagnostic_trace: Option<&'a crate::diagnostic_trace::DpllDiagnosticWriter>,
        construction_timings: Option<&mut DpllConstructionTimings>,
    ) -> Self {
        let mut construction_timings = construction_timings;

        // Register all theory atoms with the theory solver for bound propagation.
        // This allows the theory to build an index of atoms per variable,
        // enabling same-variable chain propagation (#4919 RC2).
        {
            let _register_timer = construction_timings
                .as_mut()
                .map(|timings| PhaseTimer::new(&mut timings.extension_register_atoms));
            for &atom in theory_atoms {
                theory.register_atom(atom);
            }

            // Sort atom_index before generating bound axioms (#4919).
            theory.sort_atom_index();
        }

        let (pending_axiom_clauses, pending_axiom_terms, pending_axiom_farkas) = {
            let _axiom_timer = construction_timings
                .as_mut()
                .map(|timings| PhaseTimer::new(&mut timings.extension_bound_axioms));

            // Generate bound ordering axioms (#4919).
            // Reference: Z3 mk_bound_axioms — encodes bound implications as SAT
            // binary clauses so BCP handles them instead of the theory solver.
            let axiom_term_pairs = theory.generate_bound_axiom_terms();
            let mut pending_axiom_clauses = Vec::with_capacity(axiom_term_pairs.len());
            let mut pending_axiom_terms = Vec::with_capacity(axiom_term_pairs.len());
            let mut pending_axiom_farkas: Vec<Option<FarkasAnnotation>> =
                Vec::with_capacity(axiom_term_pairs.len());
            for (t1, p1, t2, p2) in axiom_term_pairs {
                if let (Some(&v1), Some(&v2)) = (term_to_var.get(&t1), term_to_var.get(&t2)) {
                    let l1 = if p1 {
                        Literal::positive(Variable::new(v1))
                    } else {
                        Literal::negative(Variable::new(v1))
                    };
                    let l2 = if p2 {
                        Literal::positive(Variable::new(v2))
                    } else {
                        Literal::negative(Variable::new(v2))
                    };
                    pending_axiom_clauses.push(vec![l1, l2]);
                    pending_axiom_terms.push((t1, p1, t2, p2));
                    pending_axiom_farkas.push(None); // filled during validation below
                }
            }

            // Validate bound axioms (#6242, #6564): verify each clause
            // (t1^p1 ∨ t2^p2) is a tautology by checking that
            // ¬(t1^p1) ∧ ¬(t2^p2) is UNSAT in a fresh LRA solver. Unsound
            // axioms are removed to prevent false-UNSAT.
            //
            // Previously debug-only; promoted to all builds (#6564) because
            // the axiom generator can produce unsound axioms that cause
            // release-only false-UNSAT. Runs once at construction time;
            // acceptable overhead.
            // #6686: Extract Farkas certificates from the validation check.
            // These are attached to proof steps so carcara can verify
            // `la_generic :args (c1 c2)` on bound-axiom theory lemmas.
            if let Some(terms) = terms {
                let mut valid_clauses = Vec::with_capacity(pending_axiom_clauses.len());
                let mut valid_terms = Vec::with_capacity(pending_axiom_terms.len());
                let mut valid_farkas: Vec<Option<FarkasAnnotation>> =
                    Vec::with_capacity(pending_axiom_terms.len());
                let mut rejected = 0usize;
                for (i, (t1, p1, t2, p2)) in pending_axiom_terms.iter().copied().enumerate() {
                    use z4_core::{TheoryResult, TheorySolver};
                    use z4_lra::LraSolver;
                    let mut check_lra = LraSolver::new(terms);
                    // Assert negation of both literals: if UNSAT, clause is tautology
                    check_lra.assert_literal(t1, !p1);
                    check_lra.assert_literal(t2, !p2);
                    match check_lra.check() {
                        TheoryResult::UnsatWithFarkas(conflict) => {
                            valid_clauses.push(pending_axiom_clauses[i].clone());
                            valid_terms.push((t1, p1, t2, p2));
                            valid_farkas.push(conflict.farkas);
                        }
                        TheoryResult::Unsat(_) => {
                            valid_clauses.push(pending_axiom_clauses[i].clone());
                            valid_terms.push((t1, p1, t2, p2));
                            valid_farkas.push(None);
                        }
                        TheoryResult::Sat => {
                            rejected += 1;
                            tracing::warn!(
                                term1 = ?t1,
                                pol1 = p1,
                                term2 = ?t2,
                                pol2 = p2,
                                "Rejected unsound bound axiom (#6242)"
                            );
                        }
                        _ => {
                            valid_clauses.push(pending_axiom_clauses[i].clone());
                            valid_terms.push((t1, p1, t2, p2));
                            valid_farkas.push(None);
                        }
                    }
                }
                if rejected > 0 {
                    tracing::warn!(
                        rejected,
                        total = pending_axiom_clauses.len(),
                        valid = valid_clauses.len(),
                        "Removed unsound bound axioms (#6242, #6564)"
                    );
                }
                pending_axiom_clauses = valid_clauses;
                pending_axiom_terms = valid_terms;
                pending_axiom_farkas = valid_farkas;
            }

            (
                pending_axiom_clauses,
                pending_axiom_terms,
                pending_axiom_farkas,
            )
        };

        if !pending_axiom_clauses.is_empty() {
            tracing::info!(
                bound_axioms = pending_axiom_clauses.len(),
                theory_atoms = theory_atoms.len(),
                "Bound ordering axioms generated (#4919)"
            );
        }

        // Build dense bitset for O(1) theory-variable membership checks.
        // Each bit corresponds to a SAT variable ID. This replaces the
        // double hashmap lookup (var_to_term + theory_atom_set.contains)
        // in the hot trail-scan loop.
        let theory_var_bitset = {
            let max_var_id = var_to_term.keys().copied().max().unwrap_or(0) as usize;
            let num_words = (max_var_id + 64) / 64;
            let mut bitset = vec![0u64; num_words];
            for (&var_id, &term_id) in var_to_term {
                if theory_atom_set.contains(&term_id) {
                    let idx = var_id as usize;
                    bitset[idx / 64] |= 1u64 << (idx % 64);
                }
            }
            bitset
        };

        Self {
            theory,
            terms,
            var_to_term,
            term_to_var,
            theory_atoms,
            theory_atom_set,
            last_trail_pos: 0,
            theory_level: 0,
            debug: crate::debug_dpll_enabled(),
            diagnostic_trace,
            proof: None,
            theory_conflict_count: 0,
            theory_propagation_count: 0,
            partial_clause_count: 0,
            pending_split: None,
            pending_bound_refinements: Vec::new(),
            level_trail_positions: Vec::new(),
            has_checked: false,
            theory_decision_idx: Cell::new(0),
            pending_axiom_clauses,
            pending_axiom_terms,
            pending_axiom_farkas,
            expr_split_seen_count: 0,
            bound_refinement_handoff: BoundRefinementHandoff::FinalCheckOnly,
            zero_propagation_streak: 0,
            deferred_atom_count: 0,
            eager_stats: DpllEagerStats::default(),
            processed_expr_splits: None,
            theory_var_bitset,
            can_propagate_scan_pos: Cell::new(0),
            disable_theory_check: std::env::var("Z4_DISABLE_THEORY_CHECK").is_ok(),
        }
    }

    /// Number of theory conflicts encountered during eager solving (#4705).
    #[must_use]
    pub(crate) fn num_theory_conflicts(&self) -> u64 {
        self.theory_conflict_count
    }

    /// Number of theory propagation clauses added during eager solving (#4705).
    #[must_use]
    pub(crate) fn num_theory_propagations(&self) -> u64 {
        self.theory_propagation_count
    }

    /// Number of partial clause events where `term_to_literal` dropped terms (#5000).
    #[must_use]
    pub(crate) fn num_partial_clauses(&self) -> u64 {
        self.partial_clause_count
    }

    /// Deterministic eager-extension counters accumulated on this instance.
    #[must_use]
    pub(crate) fn eager_stats(&self) -> &DpllEagerStats {
        &self.eager_stats
    }

    /// Drop already-added bound axioms when the eager split loop reuses the
    /// same SAT solver across fresh theory-extension instances.
    pub(crate) fn retain_new_axioms(&mut self, seen_axioms: &mut HashSet<TheoryAxiomKey>) {
        if self.pending_axiom_terms.is_empty() {
            return;
        }

        let mut new_clauses = Vec::with_capacity(self.pending_axiom_clauses.len());
        let mut new_terms = Vec::with_capacity(self.pending_axiom_terms.len());
        let mut new_farkas = Vec::with_capacity(self.pending_axiom_farkas.len());
        for ((clause, (t1, p1, t2, p2)), farkas) in self
            .pending_axiom_clauses
            .drain(..)
            .zip(self.pending_axiom_terms.drain(..))
            .zip(self.pending_axiom_farkas.drain(..))
        {
            if seen_axioms.insert(TheoryAxiomKey::new(t1, p1, t2, p2)) {
                new_clauses.push(clause);
                new_terms.push((t1, p1, t2, p2));
                new_farkas.push(farkas);
            }
        }
        self.pending_axiom_clauses = new_clauses;
        self.pending_axiom_terms = new_terms;
        self.pending_axiom_farkas = new_farkas;
    }

    /// Take a pending split/lemma request stored during eager solving (#4919).
    /// Returns `None` if no split was requested.
    pub(crate) fn take_pending_split(&mut self) -> Option<z4_core::TheoryResult> {
        self.pending_split.take()
    }

    pub(crate) fn take_pending_bound_refinements(&mut self) -> Vec<BoundRefinementRequest> {
        std::mem::take(&mut self.pending_bound_refinements)
    }

    pub(super) fn record_pending_bound_refinements(
        &mut self,
        refinements: Vec<BoundRefinementRequest>,
    ) {
        for refinement in refinements {
            if !self.pending_bound_refinements.contains(&refinement) {
                self.pending_bound_refinements.push(refinement);
            }
        }
    }

    pub(crate) fn with_proof_tracking(
        mut self,
        tracker: &'a mut ProofTracker,
        negations: &'a HashMap<TermId, TermId>,
    ) -> Self {
        self.proof = Some(ProofContext { tracker, negations });
        self
    }

    pub(crate) fn with_inline_bound_refinement_replay(
        mut self,
        known_replays: &'a HashSet<BoundRefinementReplayKey>,
    ) -> Self {
        self.bound_refinement_handoff =
            BoundRefinementHandoff::StopAndReplayInline { known_replays };
        self
    }
}
