// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory consistency checking for `DpllT`.
//!
//! Contains `check_theory_core`, the central theory-check method that handles
//! propagation, conflict detection, Farkas certificate verification, and
//! proof-tracking integration. Extracted from `lib.rs` as part of #6860.

#[cfg(not(kani))]
use hashbrown::HashMap;
use std::time::Instant;
#[cfg(kani)]
use z4_core::kani_compat::DetHashMap as HashMap;

use z4_core::{term::TermData, TermId, TheoryResult, TheorySolver};
use z4_sat::Literal;

#[cfg(debug_assertions)]
use crate::verification::{verify_propagation_semantic, verify_theory_conflict_with_farkas_full};
use crate::verification::{
    self, verify_euf_conflict, verify_theory_conflict, verify_theory_conflict_with_farkas,
    verify_theory_propagation,
};
use crate::{proof_tracker, theory_inference, DpllT, TheoryCheck};

impl<T: TheorySolver> DpllT<'_, T> {
    /// Check theory consistency and handle propagations/conflicts
    ///
    /// DPLL(T) Integration:
    /// When the theory propagates a literal L with reason {R1, R2, ...}, we add
    /// the clause (-R1 ∨ -R2 ∨ ... ∨ L) to the SAT solver. This enables SAT-level
    /// unit propagation to prune the search space using theory deductions.
    ///
    /// Without this, z4 would explore exponentially more branches on benchmarks
    /// like eq_diamond where transitivity propagations are critical.
    pub(crate) fn check_theory(&mut self) -> TheoryCheck {
        self.check_theory_core(None)
    }

    /// Core theory check logic used by `check_theory` and the proof-tracking solve loop.
    ///
    /// When `tracking` is `Some`, records theory conflict steps into the proof tracker.
    pub(crate) fn check_theory_core(
        &mut self,
        mut tracking: Option<(&mut proof_tracker::ProofTracker, &HashMap<TermId, TermId>)>,
    ) -> TheoryCheck {
        let debug = self.debug_dpll;
        let label = if tracking.is_some() {
            "check_theory_with_proof_tracking"
        } else {
            "check_theory"
        };

        // First check for propagations and add them to SAT solver
        let has_diag = self.diagnostic_trace.is_some();
        let propagate_start = has_diag.then(Instant::now);
        let propagations = self.theory.propagate();
        let propagate_duration = propagate_start.map(|s| s.elapsed());
        let mut clauses_added = 0;

        for prop in propagations {
            // Verify propagation structure (#4346)
            verification::log_propagation_debug(&prop, label);
            if let Err(e) = verify_theory_propagation(&prop) {
                debug_assert!(
                    false,
                    "BUG: Theory returned invalid propagation in {label}: {e}\n\
                     Propagated: {:?}={}\nReason: {:?}",
                    prop.literal.term, prop.literal.value, prop.reason
                );
                tracing::warn!("skipping invalid theory propagation in {label}: {e}");
                continue;
            }

            // #8782: Demoted to debug-only. See propagate.rs for root cause analysis.
            #[cfg(debug_assertions)]
            if let Some(terms) = self.terms {
                const SEMANTIC_VERIFY_TERM_LIMIT: usize = 50_000;
                if terms.len() <= SEMANTIC_VERIFY_TERM_LIMIT {
                    if let Err(e) = verify_propagation_semantic(&prop, terms) {
                        tracing::error!(
                            label,
                            error = %e,
                            term = ?prop.literal.term,
                            value = prop.literal.value,
                            reason_count = prop.reason.len(),
                            "BUG(#6242): propagation semantic verification failed; skipping unsound propagation"
                        );
                        continue;
                    }
                }
            }

            {
                // #6546: dynamically register unmapped theory terms so propagation
                // clauses are never dropped as partial.
                let lit = self.term_to_literal_or_register(prop.literal.term, prop.literal.value);
                // Check if this conflicts with current assignment
                if let Some(var) = self.var_for_term(prop.literal.term) {
                    if let Some(value) = self.sat.value(var) {
                        if value != prop.literal.value {
                            // Theory propagated a value but SAT assigned the opposite.
                            // Batch the conflict as a clause (#6546): instead of returning
                            // immediately on the first conflict, collect ALL conflicts so
                            // the SAT solver learns multiple clauses per restart.
                            // #6546: use dynamic registration to avoid partial
                            // clause drops. Array theory terms generated during
                            // check() may not be in term_to_var yet.
                            let mut conflict: Vec<Literal> = prop
                                .reason
                                .iter()
                                .map(|r| self.term_to_literal_or_register(r.term, !r.value))
                                .collect();
                            // Soundness guard (#3826): partial clause check.
                            if conflict.len() < prop.reason.len() {
                                self.partial_clause_count += 1;
                                if self.partial_clause_count >= 100 {
                                    tracing::error!(
                                        count = self.partial_clause_count,
                                        "BUG(#4666): partial clause count overflow — systematic theory-SAT mapping failure"
                                    );
                                }
                                self.emit_theory_check_event(
                                    "propagate",
                                    "unknown",
                                    None,
                                    None,
                                    propagate_duration,
                                );
                                return TheoryCheck::Unknown;
                            }
                            conflict.push(lit);
                            if debug {
                                safe_eprintln!(
                                    "[DPLL] Theory propagation conflict: {} literals",
                                    conflict.len()
                                );
                            }
                            self.emit_theory_check_event(
                                "propagate",
                                "conflict",
                                None,
                                Some(conflict.len()),
                                propagate_duration,
                            );
                            return TheoryCheck::Conflict(conflict);
                        }
                        // Already assigned to the correct value - no clause needed
                        continue;
                    }
                }

                // Literal is not yet assigned - add propagation clause
                // Clause: (¬reason1 ∨ ¬reason2 ∨ ... ∨ propagated_lit)
                // #6546: use dynamic registration to avoid partial clause drops.
                let mut clause: Vec<Literal> = prop
                    .reason
                    .iter()
                    .map(|r| self.term_to_literal_or_register(r.term, !r.value))
                    .collect();
                clause.push(lit);

                if debug {
                    safe_eprintln!(
                        "[DPLL] Adding theory propagation clause: {} literals (propagates {})",
                        clause.len(),
                        if lit.is_positive() { "true" } else { "false" }
                    );
                }

                self.sat.add_clause(clause);
                clauses_added += 1;
            }
        }

        // If we added propagation clauses, signal to re-solve
        if clauses_added > 0 {
            if debug {
                safe_eprintln!("[DPLL] Added {} theory propagation clauses", clauses_added);
            }
            self.emit_theory_check_event(
                "propagate",
                "propagated",
                Some(clauses_added),
                None,
                propagate_duration,
            );
            return TheoryCheck::Propagated(clauses_added);
        }

        self.emit_theory_check_event("propagate", "none", Some(0), None, propagate_duration);

        // Then check consistency (BCP-time hook for combined solvers)
        let check_start = has_diag.then(Instant::now);
        let consistency_result = self.theory.check_during_propagate();
        let consistency_duration = check_start.map(|s| s.elapsed());
        match consistency_result {
            TheoryResult::Sat => {
                self.emit_theory_check_event(
                    "consistency",
                    "sat",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::Sat
            }
            TheoryResult::Unknown => {
                self.emit_theory_check_event(
                    "consistency",
                    "unknown",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::Unknown
            }
            TheoryResult::NeedSplit(split) => {
                self.emit_theory_check_event(
                    "consistency",
                    "need_split",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedSplit(split)
            }
            TheoryResult::NeedDisequalitySplit(split) => {
                self.emit_theory_check_event(
                    "consistency",
                    "need_disequality_split",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedDisequalitySplit(split)
            }
            TheoryResult::NeedExpressionSplit(split) => {
                self.emit_theory_check_event(
                    "consistency",
                    "need_expression_split",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedExpressionSplit(split)
            }
            TheoryResult::NeedStringLemma(lemma) => {
                self.emit_theory_check_event(
                    "consistency",
                    "need_string_lemma",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedStringLemma(lemma)
            }
            TheoryResult::NeedLemmas(lemmas) => {
                if let Some((ref mut tracker, negations)) = tracking {
                    for lemma in &lemmas {
                        let terms = self
                            .theory_clause_to_terms(&lemma.clause, negations)
                            .unwrap_or_else(|| lemma.clause.iter().map(|lit| lit.term).collect());
                        let _ = tracker.add_theory_lemma(terms);
                    }
                }
                self.emit_theory_check_event(
                    "consistency",
                    "need_lemmas",
                    Some(lemmas.len()),
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedLemmas(lemmas)
            }
            TheoryResult::NeedModelEquality(eq) => {
                self.emit_theory_check_event(
                    "consistency",
                    "need_model_equality",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedModelEquality(eq)
            }
            TheoryResult::NeedModelEqualities(eqs) => {
                self.emit_theory_check_event(
                    "consistency",
                    "need_model_equalities",
                    None,
                    None,
                    consistency_duration,
                );
                TheoryCheck::NeedModelEqualities(eqs)
            }
            TheoryResult::Unsat(conflict_terms) => {
                // Temporary debug: print conflict terms for #3826 diagnosis.
                if debug {
                    safe_eprintln!(
                        "[DPLL] Theory UNSAT conflict: {} terms",
                        conflict_terms.len()
                    );
                    for (i, lit) in conflict_terms.iter().enumerate() {
                        if let Some(terms) = self.terms {
                            safe_eprintln!(
                                "[DPLL]   conflict[{}]: term={:?} value={} kind={:?}",
                                i,
                                lit.term,
                                lit.value,
                                terms.get(lit.term)
                            );
                            // Deep print: show sub-terms for equality atoms
                            if let TermData::App(_, args) = terms.get(lit.term) {
                                for &arg in args.iter() {
                                    safe_eprintln!(
                                        "[DPLL]     sub {:?}: {:?}",
                                        arg,
                                        terms.get(arg)
                                    );
                                    if let TermData::App(_, sub_args) = terms.get(arg) {
                                        for &sa in sub_args.iter() {
                                            safe_eprintln!(
                                                "[DPLL]       sub {:?}: {:?}",
                                                sa,
                                                terms.get(sa)
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                // Structural verification in all builds (#3175)
                verification::log_conflict_debug(
                    &conflict_terms,
                    if label == "check_theory" {
                        "DpllT::check_theory Unsat"
                    } else {
                        "DpllT::check_theory_with_proof_tracking Unsat"
                    },
                );
                if let Err(e) = verify_theory_conflict(&conflict_terms) {
                    tracing::error!(
                        context = label,
                        error = %e,
                        conflict_len = conflict_terms.len(),
                        conflict = ?conflict_terms,
                        "BUG: theory conflict verification failed; returning Unknown"
                    );
                    self.emit_theory_check_event(
                        "consistency",
                        "unknown",
                        None,
                        Some(conflict_terms.len()),
                        consistency_duration,
                    );
                    return TheoryCheck::Unknown;
                }
                // EUF semantic re-check (#4704, #4912): re-derive conflict via
                // fresh congruence closure. Matches the Farkas semantic pattern
                // at UnsatWithFarkas. Budget guard skips for large term stores.
                if self.theory.supports_euf_semantic_check() {
                    if let Some(terms) = self.terms {
                        const SEMANTIC_VERIFY_TERM_LIMIT: usize = 50_000;
                        if terms.len() <= SEMANTIC_VERIFY_TERM_LIMIT {
                            if let Err(e) = verify_euf_conflict(&conflict_terms, terms) {
                                tracing::error!(
                                    context = label,
                                    error = %e,
                                    conflict_len = conflict_terms.len(),
                                    "BUG(#4912): EUF semantic conflict verification failed in lazy path; returning Unknown"
                                );
                                self.emit_theory_check_event(
                                    "consistency",
                                    "unknown",
                                    None,
                                    Some(conflict_terms.len()),
                                    consistency_duration,
                                );
                                return TheoryCheck::Unknown;
                            }
                        }
                    }
                }
                if let Some((ref mut tracker, negations)) = tracking {
                    theory_inference::record_theory_conflict_unsat(
                        tracker,
                        self.terms,
                        negations,
                        &conflict_terms,
                    );
                }
                // #6546: dynamically register unmapped terms so conflict clauses
                // are never dropped as partial.
                let clause: Vec<Literal> = conflict_terms
                    .iter()
                    .map(|t| self.term_to_literal_or_register(t.term, !t.value))
                    .collect();
                {
                    self.emit_theory_check_event(
                        "consistency",
                        "conflict",
                        None,
                        Some(clause.len()),
                        consistency_duration,
                    );
                    TheoryCheck::Conflict(clause)
                }
            }
            TheoryResult::UnsatWithFarkas(conflict) => {
                // Structural Farkas verification in all builds (#3175)
                verification::log_conflict_debug(
                    &conflict.literals,
                    if label == "check_theory" {
                        "DpllT::check_theory UnsatWithFarkas"
                    } else {
                        "DpllT::check_theory_with_proof_tracking UnsatWithFarkas"
                    },
                );
                // Graceful degradation (#5536): when Farkas certificate verification
                // fails (structural or semantic), drop the certificate but keep the
                // conflict clause. The conflict literals are derived from sound simplex
                // analysis and are valid for CDCL learning. Only the proof certificate
                // is invalid. This matches extension.rs propagation path behavior.
                let mut farkas_valid = true;
                if let Err(e) = verify_theory_conflict_with_farkas(&conflict) {
                    if e.is_missing_annotation() {
                        // Missing Farkas annotation (#6535): conflict is sound but
                        // proof certificate cannot be recorded.
                        tracing::debug!(
                            context = label,
                            conflict_len = conflict.literals.len(),
                            "Farkas annotation missing; conflict clause is sound, skipping proof cert"
                        );
                    } else {
                        tracing::error!(
                            context = label,
                            error = %e,
                            conflict_len = conflict.literals.len(),
                            conflict = ?conflict.literals,
                            "BUG(#5536): Farkas structural verification failed; using conflict clause without certificate"
                        );
                    }
                    farkas_valid = false;
                }
                // Semantic Farkas verification (#4515). Debug-only: BigRational
                // arithmetic per conflict is too expensive for release (W16-5).
                #[cfg(debug_assertions)]
                if farkas_valid && self.theory.supports_farkas_semantic_check() {
                    if let Some(terms) = self.terms {
                        if let Err(e) = verify_theory_conflict_with_farkas_full(&conflict, terms) {
                            tracing::error!(
                                context = label,
                                error = %e,
                                conflict_len = conflict.literals.len(),
                                conflict = ?conflict.literals,
                                "BUG(#5536): Farkas semantic verification failed; using conflict clause without certificate"
                            );
                            farkas_valid = false;
                        }
                    }
                }
                // Record Farkas proof data only if the certificate is valid
                if farkas_valid {
                    if let Some((ref mut tracker, negations)) = tracking {
                        theory_inference::record_theory_conflict_unsat_with_farkas(
                            tracker, self.terms, negations, &conflict,
                        );
                    }
                }
                // #6546: dynamically register unmapped terms so Farkas conflict
                // clauses are never dropped as partial.
                let clause: Vec<Literal> = conflict
                    .literals
                    .iter()
                    .map(|t| self.term_to_literal_or_register(t.term, !t.value))
                    .collect();
                self.emit_theory_check_event(
                    "consistency",
                    "conflict",
                    None,
                    Some(clause.len()),
                    consistency_duration,
                );
                TheoryCheck::Conflict(clause)
            }
            // All current TheoryResult variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TheoryResult variant in theory_check(): {other:?}"),
        }
    }
}
