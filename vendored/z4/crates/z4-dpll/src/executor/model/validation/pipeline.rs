// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core model validation pipeline.
//!
//! Contains validate_model, validate_model_attempt, finalize_sat_model_validation,
//! and finalize_sat_assumption_validation methods on Executor.
//!
//! Per-term observation logic is in `observation.rs`.

use z4_core::{TermId, VerificationBoundary, VerificationEvidenceKind, VerificationVerdict};

use super::{
    ValidationAttempt, ValidationObservation, ValidationSkipKind, ValidationStats,
    ValidationTarget, TERM_FLAG_ARRAY,
};
use crate::executor::model::{debug_model, Executor};
use crate::executor_types::{
    ExecutorError, ModelValidationError, Result, SolveResult, UnknownReason,
};

impl Executor {
    /// Verify that every assertion with a SAT variable mapping evaluates to
    /// `true` in the SAT model's boolean skeleton.
    ///
    /// This is a lightweight check that does NOT require theory model evaluation.
    /// It catches Tseitin encoding bugs and SAT-level unsoundness even when
    /// `skip_model_eval` is set (Strings, Seq, FP theories).
    ///
    /// Part of #7912: universal verify_model coverage.
    #[cfg(debug_assertions)]
    fn debug_assert_boolean_skeleton(&self, context: &str) {
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            _ => return, // No model to check
        };
        if model.sat_model.is_empty() && model.term_to_var.is_empty() {
            return; // Trivially SAT (e.g., empty string assertions folded away)
        }
        for (i, &assertion) in self.ctx.assertions.iter().enumerate() {
            if let Some(&var) = model.term_to_var.get(&assertion) {
                let var_idx = var as usize;
                if var_idx < model.sat_model.len() {
                    debug_assert!(
                        model.sat_model[var_idx],
                        "BUG [{context}]: assertion {i} (term {assertion:?}) maps to SAT var {var} \
                         which is FALSE in the SAT model — boolean skeleton violated"
                    );
                }
            }
        }
    }

    fn apply_assertion_observation(
        stats: &mut ValidationStats,
        observation: ValidationObservation,
    ) -> std::result::Result<(), ModelValidationError> {
        match observation {
            ValidationObservation::Skip(kind) => {
                match kind {
                    ValidationSkipKind::Internal => stats.skipped_internal += 1,
                    ValidationSkipKind::Quantifier => stats.skipped_quantifier += 1,
                    ValidationSkipKind::Datatype => stats.skipped_datatype += 1,
                    ValidationSkipKind::Dtbv => stats.skipped_dtbv += 1,
                    ValidationSkipKind::ArithArrayMix => stats.skipped_arith_array_mix += 1,
                }
                Ok(())
            }
            ValidationObservation::Fallback(_) => {
                stats.sat_fallback_count += 1;
                Ok(())
            }
            ValidationObservation::Verdict { verdict, dt_only } => match verdict {
                VerificationVerdict::Verified { evidence, .. } => {
                    stats.checked += 1;
                    if evidence == VerificationEvidenceKind::DelegatedSolver {
                        stats.delegated_checks += 1;
                    }
                    let _ = dt_only;
                    Ok(())
                }
                VerificationVerdict::Incomplete(failure) => {
                    Err(ModelValidationError::Incomplete(failure))
                }
                VerificationVerdict::Violated(failure) => {
                    Err(ModelValidationError::Violated(failure))
                }
                _ => {
                    unreachable!("unexpected verification verdict variant in assertion validation")
                }
            },
        }
    }

    fn validate_model_attempt(&self) -> ValidationAttempt {
        let debug = debug_model();
        let model = match (&self.last_result, &self.last_model) {
            (Some(SolveResult::Sat), Some(m)) => m,
            (Some(SolveResult::Sat), None) => {
                // SAT with no assertions is trivially valid
                if self.ctx.assertions.is_empty() {
                    return ValidationAttempt::success(ValidationStats {
                        total: 0,
                        ..Default::default()
                    });
                }
                return ValidationAttempt::failure(
                    None,
                    ModelValidationError::violated(
                        VerificationBoundary::SmtGroundAssertion,
                        "No model available",
                    ),
                );
            }
            _ => {
                return ValidationAttempt::failure(
                    None,
                    ModelValidationError::violated(
                        VerificationBoundary::SmtGroundAssertion,
                        "Model validation requires SAT result",
                    ),
                )
            }
        };

        // Flatten top-level conjunctions so each leaf assertion gets its own
        // term flags and SAT-fallback lookup (#5585). The solve pipeline's
        // FlattenAnd preprocessor already splits conjunctions before Tseitin
        // encoding, so the individual conjuncts have SAT variables but the
        // parent conjunction may not. Without flattening here, a conjunction
        // like (and (= (select a i) 1) (>= x 0)) evaluates to Unknown when
        // any child is Unknown, then fails SAT-fallback because the conjunction
        // itself has no term_to_var mapping.
        let flat_assertions = self.flatten_assertion_conjunctions();
        let total = flat_assertions.len();

        // Precompute term classification flags in a single O(T) pass instead
        // of 5 separate recursive tree walks per assertion. On shared DAG terms,
        // the old approach could re-traverse exponentially; this is always O(T).
        let term_flags = self.precompute_term_flags();

        let mut stats = ValidationStats {
            total,
            ..Default::default()
        };
        let has_array_assertions = flat_assertions
            .iter()
            .any(|&assertion| term_flags[assertion.index()] & TERM_FLAG_ARRAY != 0);
        // BV-backed models use complete bit-blasting: the SAT model IS
        // ground truth for all BV+array terms. When model evaluation
        // returns false/unknown for an array assertion, this is a model
        // evaluator limitation, not a real violation.
        let bv_backed = model.bv_model.is_some();

        for (i, &assertion) in flat_assertions.iter().enumerate() {
            let flags_i = term_flags[assertion.index()];
            let observation = self.validate_term_observation(
                model,
                assertion,
                i,
                flags_i,
                has_array_assertions,
                ValidationTarget::GroundAssertion,
            );
            if debug {
                tracing::debug!(
                    assertion_index = i,
                    assertion = %self.format_term(assertion),
                    observation = ?observation,
                    "model validation assertion observation"
                );
            }
            if let Err(error) = Self::apply_assertion_observation(&mut stats, observation) {
                // BV-backed + array assertion: trust the bit-blasted SAT
                // model. The evaluator cannot reconstruct select/store
                // chains from bit-level assignments.
                if bv_backed && flags_i & TERM_FLAG_ARRAY != 0 {
                    tracing::debug!(
                        assertion_index = i,
                        "BV-backed array assertion: trusting bit-blasted SAT model"
                    );
                    stats.sat_fallback_count += 1;
                    continue;
                }
                return ValidationAttempt::failure(Some(stats), error);
            }
        }

        // Emit skip statistics for sat-debuggability (#4605).
        let skipped_total = stats.skipped_internal
            + stats.skipped_quantifier
            + stats.skipped_datatype
            + stats.skipped_dtbv
            + stats.skipped_arith_array_mix;
        debug_assert!(
            stats.checked + skipped_total + stats.sat_fallback_count <= stats.total,
            "BUG: ValidationStats accounting: checked({}) + skipped({}) + sat_fallback({}) > total({})",
            stats.checked,
            skipped_total,
            stats.sat_fallback_count,
            stats.total,
        );
        if skipped_total > 0 || stats.sat_fallback_count > 0 || debug {
            tracing::debug!(
                checked = stats.checked,
                sat_fallback = stats.sat_fallback_count,
                skipped_internal = stats.skipped_internal,
                skipped_quantifier = stats.skipped_quantifier,
                skipped_datatype = stats.skipped_datatype,
                skipped_dtbv = stats.skipped_dtbv,
                skipped_arith_array_mix = stats.skipped_arith_array_mix,
                total = stats.total,
                "model validation skip counts"
            );
        }
        // (#5488, #5499, #5546, #6273, #4057) Degrade to Unknown when no
        // assertion produced verification evidence at all.
        let euf_backed = model.euf_model.is_some();
        // BV-backed: eager bit-blasting produces a complete SAT encoding of all
        // BV and array terms. SAT-fallback (checking whether the assertion's
        // Tseitin variable is assigned true) IS valid verification evidence for
        // QF_BV/QF_ABV/QF_UFBV/QF_AUFBV — the SAT model is the ground truth
        // for the encoding. Without this, QF_ABV benchmarks with array
        // equalities inside ITE conditions degrade to Unknown because the model
        // evaluator can't evaluate array terms, even though the SAT solver
        // found a satisfying assignment for the complete bit-blasted encoding.
        let no_verification_evidence = stats.checked == 0
            && stats.total > 0
            && !euf_backed
            && !bv_backed
            && (stats.skipped_dtbv > 0
                || stats.sat_fallback_count > 0
                || stats.skipped_arith_array_mix > 0
                || stats.skipped_internal > 0);
        if no_verification_evidence {
            let msg = format!(
                "all {} assertions were skipped or SAT-fallback \
                 (internal={}, quantifier={}, datatype={}, dtbv={}, \
                 arith_array={}, sat_fallback={})",
                stats.total,
                stats.skipped_internal,
                stats.skipped_quantifier,
                stats.skipped_datatype,
                stats.skipped_dtbv,
                stats.skipped_arith_array_mix,
                stats.sat_fallback_count,
            );
            return ValidationAttempt::failure(
                Some(stats),
                ModelValidationError::incomplete(VerificationBoundary::SmtCircularSatFallback, msg),
            );
        }

        // (#6223) Proportional SAT-fallback guard: even when some assertions
        // independently validated (checked > 0), reject models where >90% of
        // assertions are SAT-fallback. Skip for BV-backed models where the
        // SAT encoding is complete (same rationale as no_verification_evidence).
        if stats.total >= 5
            && stats.sat_fallback_count > 0
            && stats.sat_fallback_count * 10 > stats.total * 9
            && !bv_backed
        {
            let msg = format!(
                "{}/{} assertions ({:.0}%) used SAT-fallback \
                 (circular self-validation), only {} independently checked",
                stats.sat_fallback_count,
                stats.total,
                stats.sat_fallback_count as f64 / stats.total as f64 * 100.0,
                stats.checked,
            );
            return ValidationAttempt::failure(
                Some(stats),
                ModelValidationError::incomplete(VerificationBoundary::SmtCircularSatFallback, msg),
            );
        }

        ValidationAttempt::success(stats)
    }

    /// Validate that the current model satisfies all assertions.
    ///
    /// Returns `Ok(ValidationStats)` if all assertions evaluate to `true`,
    /// or `Err` with details about which assertion failed.
    pub fn validate_model(&self) -> std::result::Result<ValidationStats, ModelValidationError> {
        self.validate_model_attempt().into_result()
    }

    /// Finalize SAT model validation: validate the model and handle
    /// graceful degradation for assertions that cannot be fully checked.
    ///
    /// `Incomplete` errors degrade SAT to `Unknown`. `Violated` errors
    /// propagate as hard `ExecutorError::ModelValidation` failures.
    pub(in crate::executor) fn finalize_sat_model_validation(&mut self) -> Result<SolveResult> {
        // When quantifier E-matching is active, the assertion set contains ground
        // instances instead of the original quantified formulas. Validating now would
        // produce false violations because the model may not satisfy synthetic ground
        // instances that were only added to guide the SAT solver. Validation is deferred
        // to check_sat_internal after the original assertions are restored (#2862).
        //
        // SOUNDNESS AUDIT (#7912, Gap B):
        // - defer_model_validation: set ONLY in solve_current_assertions_with_quantifier_support()
        //   when qr.original_assertions.is_some() (quantifier E-matching rewrote assertions).
        //   Validation occurs later in map_quantifier_result() after originals are restored.
        // - skip_model_eval: set by theories (Seq, Strings, FP) where model evaluation is
        //   unsupported. The caller (check_sat_guarded) logs this case. Both flags are
        //   cleared at the start of each check_sat/check_sat_assuming call.
        if self.defer_model_validation || self.skip_model_eval {
            // Log which validation skip path is active for debuggability.
            tracing::debug!(
                defer_model_validation = self.defer_model_validation,
                skip_model_eval = self.skip_model_eval,
                "finalize_sat_model_validation skipped (validation deferred or model eval unsupported)"
            );
            // #7912: Even when full model evaluation is impossible (Strings, Seq, FP),
            // verify the SAT boolean skeleton. Every assertion with a term_to_var
            // mapping must be true in the SAT model. This catches Tseitin encoding
            // bugs and SAT-level unsoundness without requiring theory model eval.
            #[cfg(debug_assertions)]
            if self.skip_model_eval {
                self.debug_assert_boolean_skeleton("finalize_sat_model_validation/skip_model_eval");
            }
            return Ok(SolveResult::Sat);
        }
        let attempt = self.validate_model_attempt();
        self.last_validation_stats = match attempt.error.as_ref() {
            None | Some(ModelValidationError::Incomplete(_)) => attempt.stats.clone(),
            Some(ModelValidationError::Violated(_)) => None,
        };
        match attempt.into_result() {
            Ok(stats) => {
                tracing::debug!(
                    checked = stats.checked,
                    sat_fallback = stats.sat_fallback_count,
                    skipped_internal = stats.skipped_internal,
                    skipped_quantifier = stats.skipped_quantifier,
                    skipped_datatype = stats.skipped_datatype,
                    skipped_dtbv = stats.skipped_dtbv,
                    skipped_arith_array_mix = stats.skipped_arith_array_mix,
                    total = stats.total,
                    "finalized SAT model validation"
                );
                self.last_model_validated = true;
                Ok(SolveResult::Sat)
            }
            Err(e @ ModelValidationError::Incomplete(_)) => {
                tracing::debug!(error = %e, "model validation incomplete, degrading to Unknown");
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.last_result = Some(SolveResult::Unknown);
                Ok(SolveResult::Unknown)
            }
            Err(e @ ModelValidationError::Violated(_)) => Err(ExecutorError::ModelValidation(e)),
        }
    }

    /// Finalize SAT validation for assumption-based checks.
    ///
    /// `Incomplete` errors degrade SAT to `Unknown`. `Violated` errors
    /// propagate as hard `ExecutorError::ModelValidation` failures.
    pub(in crate::executor) fn finalize_sat_assumption_validation(
        &mut self,
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        match self.validate_sat_assumptions(assumptions) {
            Ok(()) => Ok(SolveResult::Sat),
            Err(e @ ModelValidationError::Incomplete(_)) => {
                tracing::debug!(error = %e, "assumption validation incomplete, degrading to Unknown");
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.last_result = Some(SolveResult::Unknown);
                Ok(SolveResult::Unknown)
            }
            Err(e @ ModelValidationError::Violated(_)) => Err(ExecutorError::ModelValidation(e)),
        }
    }
}
