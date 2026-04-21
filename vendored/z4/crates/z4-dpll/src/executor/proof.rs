// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof orchestration and API for UNSAT results.
//!
//! Proof checking and quality measurement live in `check`. Farkas synthesis
//! lives in `proof_farkas`. Resolution strategies live in `proof_resolution`.
//! Surface-syntax rewriting lives in `proof_rewrite`.

mod check;

use z4_core::term::TermData;
use z4_core::{Proof, ProofStep, Symbol, TheoryLemmaKind};
use z4_core::{TermId, TermStore};
use z4_frontend::command::Term as FrontendTerm;
use z4_frontend::{Command, CommandResult, OptionValue};
use z4_proof::export_alethe_with_problem_scope_and_overrides;
#[cfg(not(feature = "proof-checker"))]
use z4_proof::{check_proof_partial, PartialProofCheck};

use crate::executor_types::SolveResult;

use super::Executor;

impl Executor {
    /// Build a proof for UNSAT result
    ///
    /// Creates an Alethe-compatible proof with assumptions for each assertion
    /// and a final step deriving the empty clause.
    pub(super) fn build_unsat_proof(&mut self) {
        let mut proof = if self.proof_tracker.num_steps() > 0 {
            let mut tracker_proof = self.proof_tracker.take_proof();
            // (#7913 Phase C) When LIA preprocessing substituted variables,
            // the tracker's Assume terms may be degenerate (e.g. `true`,
            // `false`) rather than the original user assertions. This happens
            // when VariableSubstitution replaces `(= x 3)` -> `(= 3 3)` ->
            // `true`, making the SAT solver see trivial constants instead of
            // the original equality atoms. Detect this by checking if ALL
            // assume terms are boolean constants, and if so replace them with
            // the original problem assertions.
            let true_id = self.ctx.terms.true_term();
            let false_id = self.ctx.terms.false_term();
            let assume_terms: Vec<TermId> = tracker_proof
                .steps
                .iter()
                .filter_map(|s| match s {
                    ProofStep::Assume(t) => Some(*t),
                    _ => None,
                })
                .collect();
            let all_degenerate = !assume_terms.is_empty()
                && assume_terms.iter().all(|t| *t == true_id || *t == false_id);
            if all_degenerate {
                let original_assertions = self.proof_original_problem_assertions();
                if !original_assertions.is_empty() {
                    let non_assume_steps: Vec<_> = tracker_proof
                        .steps
                        .into_iter()
                        .filter(|s| !matches!(s, ProofStep::Assume(_)))
                        .collect();
                    tracker_proof = Proof::new();
                    for (idx, assertion) in original_assertions.into_iter().enumerate() {
                        tracker_proof.add_assume(assertion, Some(format!("h{idx}")));
                    }
                    for step in non_assume_steps {
                        tracker_proof.add_step(step);
                    }
                }
            }
            tracker_proof
        } else {
            let mut proof = Proof::new();
            let problem_assertions = self.proof_problem_assertions();
            let assertions = if problem_assertions.is_empty() {
                self.proof_original_problem_assertions()
            } else {
                problem_assertions
            };
            for (idx, assertion) in assertions.into_iter().enumerate() {
                proof.add_assume(assertion, Some(format!("h{idx}")));
            }
            proof
        };

        // Capture the SAT-level LRAT bytes before SAT proof reconstruction
        // consumes `last_clause_trace`. This is best-effort: traces with
        // truncation or non-contiguous original clause IDs do not export a
        // standalone LRAT certificate.
        self.last_lrat_certificate = self
            .last_clause_trace
            .as_ref()
            .and_then(clause_trace_to_lrat_bytes);

        // Decompose single Generic/trust theory lemmas for combined real
        // conflicts into EUF + arithmetic bridge pairs (#6756 Packet 2).
        // Must run BEFORE ensure_empty_clause_derivation so the two-lemma
        // closer (Packet 3) can find both lemmas.
        Self::decompose_combined_real_conflict_lemmas(&mut self.ctx.terms, &mut proof);

        // Build initial empty clause derivation (pre-rewrite).
        self.ensure_empty_clause_derivation(&mut proof);

        let hidden_equality_assertions = self.collect_hidden_problem_equality_assertions();

        // Reconstruct missing Farkas coefficients for arithmetic theory lemmas
        // (#6757). Must run AFTER ensure_empty_clause_derivation (which may
        // create new TheoryLemma steps via SAT resolution reconstruction) but
        // BEFORE apply_input_syntax_rewrites_to_proof (which can simplify
        // linking equalities like `(= (select a 0) x)` to `true`, destroying
        // the constraint that makes the conjunction infeasible for Farkas).
        super::proof_farkas::reconstruct_missing_farkas_coefficients(
            &mut self.ctx.terms,
            &mut proof,
            &self.ctx.assertions,
            &hidden_equality_assertions,
        );

        if !crate::executor::proof_resolution::proof_structure_is_well_formed(&proof) {
            tracing::warn!("proof contains dangling premise IDs before rewrite");
        }
        self.apply_input_syntax_rewrites_to_proof(&mut proof);

        // Post-rewrite promotion (#6756): theory lemmas that were classified as
        // Generic before surface-syntax rewrites may now have clause terms that
        // match a more specific kind (e.g., LIA integer equality after array
        // select/store rewriting). Re-infer the kind from the rewritten clause.
        Self::promote_generic_theory_lemma_kinds_after_rewrite(&self.ctx.terms, &mut proof);
        // Post-rewrite Farkas for lemmas just promoted from Generic (#6756).
        // Note: may fail for combined-theory clauses where rewriting simplified
        // linking equalities; the pre-rewrite pass above is primary.
        super::proof_farkas::reconstruct_missing_farkas_coefficients(
            &mut self.ctx.terms,
            &mut proof,
            &self.ctx.assertions,
            &hidden_equality_assertions,
        );

        // Term rewriting can merge distinct auxiliary variables into the same
        // surface term, invalidating pre-rewrite resolution chains. Strip
        // stale resolution steps and rebuild from the rewritten proof.
        if !Self::proof_derives_valid_empty_clause(&self.ctx.terms, &proof) {
            crate::executor::proof_resolution::strip_resolution_steps(&mut proof);
            self.ensure_empty_clause_derivation(&mut proof);
            // Reconstruct Farkas for any trust lemmas created by rebuild (#6757).
            super::proof_farkas::reconstruct_missing_farkas_coefficients(
                &mut self.ctx.terms,
                &mut proof,
                &self.ctx.assertions,
                &hidden_equality_assertions,
            );
        }

        crate::executor::proof_resolution::prune_to_empty_clause_derivation(&mut proof);

        // Proof validation (#4393): validates all non-Hole steps via partial
        // checker. Replaces the old check_proof + Hole-skip pattern that skipped
        // entire proofs when ANY Hole step was present.
        #[cfg(feature = "proof-checker")]
        self.run_internal_proof_check(&proof);
        #[cfg(not(feature = "proof-checker"))]
        {
            if self.strict_proofs_enabled() {
                // Strict mode without proof-checker feature: use check_proof_strict.
                match z4_proof::check_proof_strict(&proof, &self.ctx.terms) {
                    Ok(_quality) => {
                        let total = proof.steps.len() as u32;
                        self.proof_check_result = Some(PartialProofCheck {
                            checked_steps: total,
                            skipped_hole_steps: 0,
                            total_steps: total,
                        });
                    }
                    Err(e) => {
                        let total = proof.steps.len() as u32;
                        self.proof_check_result = Some(PartialProofCheck {
                            checked_steps: total,
                            skipped_hole_steps: 0,
                            total_steps: total,
                        });
                        tracing::error!(
                            error = %e,
                            total_steps = total,
                            "strict proof checker rejected UNSAT proof"
                        );
                    }
                }
            } else {
                let (partial, error) = check_proof_partial(&proof, &self.ctx.terms);
                self.proof_check_result = Some(partial.clone());
                if let Some(ref e) = error {
                    tracing::error!(
                        error = %e,
                        result = %partial,
                        "internal proof checker rejected UNSAT proof"
                    );
                }
            }
        }

        // Proof quality metrics (#4176, #4420).
        let quality = self.validate_and_measure_proof(&proof);
        if let Some(ref q) = quality {
            self.populate_proof_quality_stats(q);
        }
        self.last_proof_quality = quality;

        // Postcondition contracts (#4642): proof built successfully.
        debug_assert!(
            !proof.steps.is_empty(),
            "BUG: build_unsat_proof produced an empty proof"
        );
        debug_assert!(
            Self::proof_derives_empty_clause(&proof),
            "BUG: build_unsat_proof produced a proof that does not derive the empty clause"
        );
        #[cfg(feature = "proof-checker")]
        debug_assert!(
            self.proof_check_result.is_some(),
            "BUG: build_unsat_proof did not run internal proof checker"
        );

        self.last_proof = Some(proof);
    }

    /// Decompose single Generic/trust theory lemmas for combined real conflicts
    /// into an EUF lemma plus an arithmetic bridge lemma (#6756 Packet 2).
    ///
    /// The recording-phase `record_real_combined_conflict_packet` can only
    /// succeed when the synthetic conclusion equality already exists in the
    /// term store. This pass runs in the proof builder with `&mut TermStore`
    /// access, so it can create the synthetic terms that the recording phase
    /// could not.
    fn decompose_combined_real_conflict_lemmas(terms: &mut TermStore, proof: &mut Proof) {
        use crate::theory_inference::decompose_generic_combined_real_lemma;

        let mut decomposed = Vec::new();
        for (idx, step) in proof.steps.iter().enumerate() {
            let ProofStep::TheoryLemma { kind, clause, .. } = step else {
                continue;
            };
            if !kind.is_trust() && !matches!(kind, TheoryLemmaKind::Generic) {
                continue;
            }
            if let Some((euf_kind, euf_clause, bridge_clause, bridge_farkas)) =
                decompose_generic_combined_real_lemma(terms, clause)
            {
                decomposed.push((idx, euf_kind, euf_clause, bridge_clause, bridge_farkas));
            }
        }

        // Apply decompositions in reverse order so indices remain valid.
        for (idx, euf_kind, euf_clause, bridge_clause, bridge_farkas) in
            decomposed.into_iter().rev()
        {
            proof.steps[idx] = ProofStep::TheoryLemma {
                theory: String::from("EUF"),
                kind: euf_kind,
                clause: euf_clause,
                farkas: None,
                lia: None,
            };
            proof.add_step(ProofStep::TheoryLemma {
                theory: String::from("LRA"),
                kind: TheoryLemmaKind::LraFarkas,
                clause: bridge_clause,
                farkas: Some(bridge_farkas),
                lia: None,
            });
        }
    }

    /// Promote `TheoryLemmaKind::Generic` proof steps to a more specific kind
    /// when the post-rewrite clause terms allow it (#6756).
    ///
    /// This handles cases where the theory solver recorded a generic conflict
    /// (e.g., a combined ArrayEUF route) but after surface-syntax rewriting the
    /// clause is a plain integer-arithmetic contradiction that can export as
    /// `lia_generic` instead of `trust`.
    fn promote_generic_theory_lemma_kinds_after_rewrite(terms: &TermStore, proof: &mut Proof) {
        use crate::theory_inference::infer_theory_lemma_kind_from_clause_terms_and_farkas;
        for step in &mut proof.steps {
            if let ProofStep::TheoryLemma {
                kind,
                clause,
                farkas,
                ..
            } = step
            {
                if !kind.is_trust() {
                    continue;
                }
                let inferred = infer_theory_lemma_kind_from_clause_terms_and_farkas(
                    terms,
                    clause,
                    farkas.as_ref(),
                );
                if !inferred.is_trust() {
                    *kind = inferred;
                }
                if *kind == TheoryLemmaKind::LiaGeneric && farkas.is_none() {
                    *farkas = super::proof_farkas::synthesize_equality_farkas(terms, clause);
                }
            }
        }
    }

    // Farkas synthesis functions extracted to proof_farkas.rs (#6763).
    // Resolution strategies extracted to proof_resolution.rs (#6763).

    fn collect_hidden_problem_equality_assertions(&mut self) -> Vec<TermId> {
        let true_id = self.ctx.terms.true_term();
        let parsed_assertions: Vec<FrontendTerm> = self.ctx.assertions_parsed().to_vec();
        let problem_assertions = self.proof_original_problem_assertions();
        let mut hidden = Vec::new();

        for (&canonical, parsed) in problem_assertions.iter().zip(parsed_assertions.iter()) {
            if canonical != true_id || !super::proof_farkas::frontend_term_is_equality(parsed) {
                continue;
            }

            let Some(Some(CommandResult::CheckSatAssuming(term_ids))) = self
                .ctx
                .process_command(&Command::CheckSatAssuming(vec![parsed.clone()]))
                .ok()
            else {
                continue;
            };
            let [term_id] = term_ids.as_slice() else {
                continue;
            };

            if matches!(
                self.ctx.terms.get(*term_id),
                TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2
            ) && !hidden.contains(term_id)
            {
                hidden.push(*term_id);
            }
        }

        // (#6759) In the with_deferred_postprocessing path, provenance-aware
        // original problem assertions may contain equalities not present in
        // ctx.assertions (which holds simplified/temporary forms). Include
        // these directly so the Farkas reconstruction can find them for
        // Not(true) replacement.
        for &term in &problem_assertions {
            if !hidden.contains(&term)
                && !self.ctx.assertions.contains(&term)
                && matches!(
                    self.ctx.terms.get(term),
                    TermData::App(Symbol::Named(n), args) if n == "=" && args.len() == 2
                )
            {
                hidden.push(term);
            }
        }

        hidden
    }

    /// Get proof (get-proof command)
    ///
    /// Returns a proof that the assertions are unsatisfiable in Alethe format.
    pub(super) fn get_proof(&self) -> String {
        // Check that produce-proofs is enabled
        if !self.produce_proofs_enabled() {
            return "(error \"proof generation is not enabled, set :produce-proofs to true\")"
                .to_string();
        }

        // Check that last result was unsat
        match self.last_result {
            Some(SolveResult::Unsat) => {
                // Export the stored proof in Alethe format
                match &self.last_proof {
                    Some(proof) => export_alethe_with_problem_scope_and_overrides(
                        proof,
                        &self.ctx.terms,
                        &self.proof_problem_assertions(),
                        self.last_proof_term_overrides.as_ref(),
                    ),
                    None => "(error \"proof was not generated\")".to_string(),
                }
            }
            Some(SolveResult::Sat) => {
                "(error \"proof is not available, last result was sat\")".to_string()
            }
            Some(SolveResult::Unknown) => {
                "(error \"proof is not available, last result was unknown\")".to_string()
            }
            None => {
                "(error \"proof is not available, no check-sat has been performed\")".to_string()
            }
        }
    }

    /// Get the last serialized LRAT certificate, if proof export captured one.
    pub(crate) fn last_lrat_certificate(&self) -> Option<&[u8]> {
        self.last_lrat_certificate.as_deref()
    }

    /// Record eager array axioms as theory lemmas for proof attribution (#6722).
    ///
    /// Mirrors the DT selector axiom pattern in `solve_dt()`: each eager axiom
    /// that will appear in the DPLL assertion set is annotated in the proof
    /// tracker so SAT trace reconstruction can emit `TheoryLemma(ArraySelectStore)`
    /// steps instead of anonymous original clauses.
    ///
    /// Check if proof production is enabled
    pub(super) fn produce_proofs_enabled(&self) -> bool {
        self.proof_tracker.is_enabled()
            || matches!(
                self.ctx.get_option("produce-proofs"),
                Some(OptionValue::Bool(true))
            )
    }

    /// Check if strict proof checking is enabled (#4420).
    ///
    /// When `(set-option :check-proofs-strict true)` is set, the internal
    /// proof checker rejects `trust` and `hole` steps, requiring fully
    /// reconstructed proofs.
    fn strict_proofs_enabled(&self) -> bool {
        matches!(
            self.ctx.get_option("check-proofs-strict"),
            Some(OptionValue::Bool(true))
        )
    }
}

/// Replay a SAT clause trace into a standalone LRAT binary certificate.
///
/// Returns `None` when the trace is truncated or when the original-clause ID
/// layout no longer matches the contiguous `1..=n` numbering external LRAT
/// checkers expect from the input CNF.
fn clause_trace_to_lrat_bytes(trace: &z4_sat::ClauseTrace) -> Option<Vec<u8>> {
    if trace.is_truncated() || !trace.has_empty_clause() {
        return None;
    }

    let original_count =
        trace
            .original_clauses()
            .enumerate()
            .try_fold(0u64, |_, (idx, entry)| {
                let expected_id = u64::try_from(idx).ok()?.checked_add(1)?;
                (entry.id == expected_id).then_some(expected_id)
            })?;

    let mut output = z4_sat::ProofOutput::lrat_binary(Vec::new(), original_count);
    let mut next_learned_id = original_count + 1;
    for entry in trace.learned_clauses() {
        if entry.id < next_learned_id {
            return None;
        }
        output.advance_past(entry.id);
        let assigned_id = output.add(&entry.clause, &entry.resolution_hints).ok()?;
        if assigned_id != entry.id {
            return None;
        }
        next_learned_id = assigned_id + 1;
    }
    output.into_vec().ok()
}

#[cfg(test)]
use check::*;
#[cfg(test)]
mod tests;
