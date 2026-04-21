// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! Final theory consistency check for the eager extension.
//!
//! Extracted from `mod.rs` to keep that file under the 1,200-line target.
//! Contains the `check_impl` helper called by the `Extension::check` trait method.

use z4_core::{TheoryResult, TheorySolver};
use z4_sat::ExtCheckResult;

use crate::theory_inference::{
    record_theory_conflict_unsat, record_theory_conflict_unsat_with_farkas,
};
use crate::verification::{
    log_conflict_debug, verify_euf_conflict, verify_theory_conflict,
    verify_theory_conflict_with_farkas,
};
#[cfg(debug_assertions)]
use crate::verification::{verify_conflict_semantic, verify_theory_conflict_with_farkas_full};
use z4_sat::Literal;

use super::TheoryExtension;

impl<T: TheorySolver> TheoryExtension<'_, T> {
    /// Core logic for `Extension::check()`.
    ///
    /// Performs a final theory consistency check and translates the result into
    /// an `ExtCheckResult` that the SAT solver can act on (Sat, Conflict,
    /// AddClauses, Unknown).
    pub(super) fn check_impl(&mut self) -> ExtCheckResult {
        // #5462: combined theories that override needs_final_check_after_sat()
        // defer split/model-equality results from their full check to the
        // post-SAT dispatch in the split-loop macro. Running the full check
        // here is needed for Unsat/UnsatWithFarkas conflict detection, but
        // NeedSplit/NeedModelEquality cannot be handled inside the SAT solve
        // (they'd be reported as Unknown, causing premature SAT termination).
        // For these, store in pending_split and return Sat so the SAT solver
        // hands back the model. The macro's post-SAT code handles the split.
        let needs_final = self.theory.needs_final_check_after_sat();

        match self.theory.check() {
            TheoryResult::Sat => {
                // The theory is satisfied under the current complete assignment.
                // Clear stale pending single-var splits (#6303), but preserve
                // NeedExpressionSplit (#6586, parity with propagate() #4919).
                //
                // Multi-var disequalities (x != y) require expression split atoms
                // (x-y > 0 OR x-y < 0) to be enforced. The LRA theory returns
                // Sat here because it only checks arithmetic constraints — it
                // does not natively enforce disequalities. If we clear the
                // NeedExpressionSplit, the pipeline returns Sat without ever
                // creating the split atoms, producing an unsound result.
                //
                // For single-var splits (NeedSplit, NeedDisequalitySplit), Sat
                // from the final check means the split was resolved or is no
                // longer needed, so clearing is correct.
                //
                // Oscillation prevention: the pipeline's split clause dedup
                // (added_split_clauses HashSet) prevents re-adding the same
                // split clause, and max_splits bounds iteration count.
                //
                // #6662: also clear NeedExpressionSplit if the split has
                // already been encoded in the persistent SAT solver.
                let is_stale_expr_split = matches!(
                    &self.pending_split,
                    Some(TheoryResult::NeedExpressionSplit(s))
                    if self.processed_expr_splits.is_some_and(|ps| ps.contains(&s.disequality_term))
                );
                if is_stale_expr_split
                    || !matches!(
                        &self.pending_split,
                        Some(TheoryResult::NeedExpressionSplit(_))
                    )
                {
                    self.pending_split = None;
                }
                let refinements = self.theory.take_bound_refinements();
                self.record_pending_bound_refinements(refinements);
                ExtCheckResult::Sat
            }
            TheoryResult::Unknown => {
                self.pending_bound_refinements.clear();
                ExtCheckResult::Unknown
            }
            // #6546 Packet 5: inline NeedLemmas in check() — convert to
            // AddClauses so the SAT solver adds the theory lemmas and
            // continues solving instead of returning to the split loop.
            TheoryResult::NeedLemmas(lemmas) => self.handle_check_need_lemmas(lemmas, needs_final),
            TheoryResult::NeedExpressionSplit(split) => {
                if self
                    .processed_expr_splits
                    .is_some_and(|s| s.contains(&split.disequality_term))
                {
                    return ExtCheckResult::Sat;
                }
                self.pending_split = Some(TheoryResult::NeedExpressionSplit(split));
                self.pending_bound_refinements.clear();
                if needs_final {
                    ExtCheckResult::Sat
                } else {
                    ExtCheckResult::Unknown
                }
            }
            TheoryResult::NeedModelEquality(eq) => {
                if self.model_equality_already_encoded(&eq) {
                    return ExtCheckResult::Sat;
                }
                self.pending_split = Some(TheoryResult::NeedModelEquality(eq));
                self.pending_bound_refinements.clear();
                if needs_final {
                    ExtCheckResult::Sat
                } else {
                    ExtCheckResult::Unknown
                }
            }
            TheoryResult::NeedModelEqualities(eqs) => {
                let Some(check_result) = self.filter_stale_model_equalities(eqs) else {
                    return ExtCheckResult::Sat;
                };
                self.pending_split = Some(check_result);
                self.pending_bound_refinements.clear();
                if needs_final {
                    ExtCheckResult::Sat
                } else {
                    ExtCheckResult::Unknown
                }
            }
            check_result @ TheoryResult::NeedSplit(_)
            | check_result @ TheoryResult::NeedDisequalitySplit(_)
            | check_result @ TheoryResult::NeedStringLemma(_) => {
                self.pending_split = Some(check_result);
                self.pending_bound_refinements.clear();
                if needs_final {
                    ExtCheckResult::Sat
                } else {
                    ExtCheckResult::Unknown
                }
            }
            TheoryResult::Unsat(conflict_terms) => self.handle_check_unsat(conflict_terms),
            TheoryResult::UnsatWithFarkas(conflict) => {
                self.handle_check_unsat_with_farkas(conflict)
            }
            // All current TheoryResult variants are handled above.
            // This arm is required by #[non_exhaustive] and catches future variants.
            other => unreachable!("unhandled TheoryResult variant in check(): {other:?}"),
        }
    }

    /// Handle `NeedLemmas` in `check()` — convert to `AddClauses`.
    fn handle_check_need_lemmas(
        &mut self,
        lemmas: Vec<z4_core::TheoryLemma>,
        needs_final: bool,
    ) -> ExtCheckResult {
        let mut sat_clauses = Vec::with_capacity(lemmas.len());
        let mut all_mapped = true;
        for lemma in &lemmas {
            let sat_lits: Vec<Literal> = lemma
                .clause
                .iter()
                .filter_map(|t| self.term_to_literal(t.term, t.value))
                .collect();
            if sat_lits.len() == lemma.clause.len() {
                sat_clauses.push(sat_lits);
            } else {
                all_mapped = false;
                break;
            }
        }
        if all_mapped && !sat_clauses.is_empty() {
            self.eager_stats.inline_lemma_clauses += sat_clauses.len() as u64;
            // Record proof entries for inline lemmas.
            if let Some(ref mut proof_ctx) = self.proof {
                for lemma in &lemmas {
                    let terms: Vec<z4_core::TermId> = lemma
                        .clause
                        .iter()
                        .map(|lit| {
                            if lit.value {
                                lit.term
                            } else {
                                proof_ctx
                                    .negations
                                    .get(&lit.term)
                                    .copied()
                                    .unwrap_or(lit.term)
                            }
                        })
                        .collect();
                    proof_ctx.tracker.add_theory_lemma(terms);
                }
            }
            ExtCheckResult::AddClauses(sat_clauses)
        } else {
            // Fallback: some terms missing from SAT — use pending_split.
            self.pending_split = Some(TheoryResult::NeedLemmas(lemmas));
            self.pending_bound_refinements.clear();
            if needs_final {
                ExtCheckResult::Sat
            } else {
                ExtCheckResult::Unknown
            }
        }
    }

    /// Handle `Unsat` conflict from theory check.
    fn handle_check_unsat(&mut self, conflict_terms: Vec<z4_core::TheoryLit>) -> ExtCheckResult {
        // Structural verification (#3175)
        log_conflict_debug(&conflict_terms, "check() UNSAT");
        if let Err(e) = verify_theory_conflict(&conflict_terms) {
            tracing::error!(
                error = %e,
                conflict_len = conflict_terms.len(),
                "BUG(#4666): theory conflict verification failed in check(); returning Unknown"
            );
            return ExtCheckResult::Unknown;
        }
        // EUF semantic re-check (#4704): same as propagate() path.
        if self.theory.supports_euf_semantic_check() {
            if let Some(terms) = self.terms {
                if let Err(e) = verify_euf_conflict(&conflict_terms, terms) {
                    tracing::error!(
                        theory = std::any::type_name::<T>(),
                        error = %e,
                        conflict_len = conflict_terms.len(),
                        "BUG(#4704): EUF semantic verification failed in check(); returning Unknown"
                    );
                    return ExtCheckResult::Unknown;
                }
            }
        }
        // LRA semantic re-check (#6242): same as propagate() path.
        // Debug-only: fresh solver per conflict is too expensive for release (W16-5).
        #[cfg(debug_assertions)]
        if self.theory.supports_farkas_semantic_check() {
            if let Some(terms) = self.terms {
                if let Err(e) = verify_conflict_semantic(&conflict_terms, terms) {
                    tracing::error!(
                        error = %e,
                        conflict_len = conflict_terms.len(),
                        "BUG(#6242): LRA conflict semantic check failed in check(); returning Unknown"
                    );
                    return ExtCheckResult::Unknown;
                }
            }
        }
        if let Some(proof) = self.proof.as_mut() {
            let _ = record_theory_conflict_unsat(
                proof.tracker,
                self.terms,
                proof.negations,
                &conflict_terms,
            );
        }

        let clause: Vec<Literal> = conflict_terms
            .iter()
            .filter_map(|t| self.term_to_literal(t.term, !t.value))
            .collect();
        // Soundness guard (#3826): partial/empty clause → Unknown.
        if clause.len() < conflict_terms.len() {
            self.partial_clause_count += 1;
            if self.partial_clause_count >= 100 {
                tracing::error!(
                    count = self.partial_clause_count,
                    "BUG(#4666): partial clause count overflow — systematic theory-SAT mapping failure"
                );
            }
            tracing::error!(
                mapped = clause.len(),
                total = conflict_terms.len(),
                "BUG(#4666): theory conflict mapped to partial clause in check()"
            );
            ExtCheckResult::Unknown
        } else {
            self.theory_conflict_count += 1;
            ExtCheckResult::Conflict(clause)
        }
    }

    /// Handle `UnsatWithFarkas` conflict from theory check.
    fn handle_check_unsat_with_farkas(
        &mut self,
        conflict: z4_core::TheoryConflict,
    ) -> ExtCheckResult {
        // Structural Farkas verification (#3175)
        log_conflict_debug(&conflict.literals, "check() UnsatWithFarkas");
        let mut farkas_valid = true;
        if let Err(e) = verify_theory_conflict_with_farkas(&conflict) {
            if e.is_missing_annotation() {
                // Missing Farkas annotation (#6535): conflict is sound but
                // proof certificate cannot be recorded.
                tracing::debug!(
                    conflict_len = conflict.literals.len(),
                    "Farkas annotation missing in check(); conflict clause is sound, skipping proof cert"
                );
            } else {
                tracing::error!(
                    error = %e,
                    conflict_len = conflict.literals.len(),
                    "BUG(#4666): Farkas verification failed in check(); using conflict clause without certificate"
                );
            }
            farkas_valid = false;
        }
        // Semantic Farkas verification (#4515). Debug-only: BigRational
        // arithmetic per conflict is too expensive for release builds (W16-5).
        #[cfg(debug_assertions)]
        if farkas_valid && self.theory.supports_farkas_semantic_check() {
            if let Some(terms) = self.terms {
                if let Err(e) = verify_theory_conflict_with_farkas_full(&conflict, terms) {
                    tracing::error!(
                        error = %e,
                        conflict_len = conflict.literals.len(),
                        "BUG(#4666): Farkas semantic verification failed in check(); using conflict clause without certificate"
                    );
                    farkas_valid = false;
                }
            }
        }
        // Record Farkas proof data only if the certificate is valid
        if farkas_valid {
            if let Some(proof) = self.proof.as_mut() {
                let _ = record_theory_conflict_unsat_with_farkas(
                    proof.tracker,
                    self.terms,
                    proof.negations,
                    &conflict,
                );
            }
        }

        // LRA semantic re-check (#6242): same as propagate() path.
        // Debug-only: fresh solver per conflict is too expensive for release (W16-5).
        #[cfg(debug_assertions)]
        if self.theory.supports_farkas_semantic_check() {
            if let Some(terms) = self.terms {
                if let Err(e) = verify_conflict_semantic(&conflict.literals, terms) {
                    tracing::error!(
                        error = %e,
                        conflict_len = conflict.literals.len(),
                        "BUG(#6242): LRA conflict (Farkas) semantic check failed in check(); returning Unknown"
                    );
                    return ExtCheckResult::Unknown;
                }
            }
        }

        // Even when the Farkas certificate is invalid, the conflict
        // literals are still correct — use them (#5534).
        let clause: Vec<Literal> = conflict
            .literals
            .iter()
            .filter_map(|t| self.term_to_literal(t.term, !t.value))
            .collect();
        // Soundness guard (#3826): partial/empty clause → Unknown.
        if clause.len() < conflict.literals.len() {
            self.partial_clause_count += 1;
            if self.partial_clause_count >= 100 {
                tracing::error!(
                    count = self.partial_clause_count,
                    "BUG(#4666): partial clause count overflow — systematic theory-SAT mapping failure"
                );
            }
            tracing::error!(
                mapped = clause.len(),
                total = conflict.literals.len(),
                "BUG(#4666): Farkas conflict mapped to partial clause in check()"
            );
            ExtCheckResult::Unknown
        } else {
            self.theory_conflict_count += 1;
            ExtCheckResult::Conflict(clause)
        }
    }
}
