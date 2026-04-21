// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof checking, validation, and quality measurement.
//!
//! Contains the internal proof checker integration, proof quality metrics,
//! and proof predicate helpers (derives_empty_clause, etc.).
//!
//! Extracted from `proof.rs` for code health (#5970).

use z4_core::TermStore;
use z4_core::{AletheRule, Proof, ProofStep};
use z4_proof::ProofQuality;
#[cfg(feature = "proof-checker")]
use z4_proof::{check_proof_partial, PartialProofCheck};

use super::super::Executor;

#[cfg(feature = "proof-checker")]
pub(super) const PROOF_CHECKER_FAILURES_KEY: &str = "proof_checker_failures";
#[cfg(feature = "proof-checker")]
pub(super) const PROOF_CHECKER_SKIPPED_HOLE_STEPS_KEY: &str = "proof_checker_skipped_hole_steps";
#[cfg(feature = "proof-checker")]
pub(super) const PROOF_CHECKER_CHECKED_STEPS_KEY: &str = "proof_checker_checked_steps";
#[cfg(feature = "proof-checker")]
pub(super) const PROOF_CHECKER_TOTAL_STEPS_KEY: &str = "proof_checker_total_steps";

impl Executor {
    /// Populate statistics extra map with proof quality metrics.
    pub(super) fn populate_proof_quality_stats(&mut self, quality: &ProofQuality) {
        use crate::executor_types::StatValue;
        let extra = &mut self.last_statistics.extra;
        extra.insert(
            "proof_steps".to_string(),
            StatValue::Int(u64::from(quality.total_steps)),
        );
        extra.insert(
            "proof_verified".to_string(),
            StatValue::Int(u64::from(quality.verified_count())),
        );
        extra.insert(
            "proof_trust".to_string(),
            StatValue::Int(u64::from(quality.trust_count)),
        );
        extra.insert(
            "proof_complete".to_string(),
            StatValue::String(if quality.is_complete() {
                "true".to_string()
            } else {
                "false".to_string()
            }),
        );
    }

    /// Validate proof and collect quality metrics.
    ///
    /// In debug builds, runs the full proof checker (rejects invalid proofs via
    /// warning). In all builds, collects [`ProofQuality`] step-type counts for
    /// diagnostic reporting via `(get-info :all-statistics)`.
    pub(super) fn validate_and_measure_proof(&self, proof: &Proof) -> Option<ProofQuality> {
        let has_hole = proof.steps.iter().any(|s| {
            matches!(
                s,
                ProofStep::Step {
                    rule: AletheRule::Hole,
                    ..
                }
            )
        });
        if has_hole {
            return None;
        }

        // Use strict checker when enabled (#4420).
        let result = if self.strict_proofs_enabled() {
            z4_proof::check_proof_strict(proof, &self.ctx.terms)
        } else {
            z4_proof::check_proof_with_quality(proof, &self.ctx.terms)
        };

        match result {
            Ok(quality) => {
                tracing::debug!(
                    %quality,
                    complete = quality.is_complete(),
                    "UNSAT proof quality"
                );
                if !quality.is_complete() {
                    tracing::warn!(
                        trust = quality.trust_count,
                        hole = quality.hole_count,
                        total = quality.total_steps,
                        "UNSAT proof has unverified fallback steps"
                    );
                }
                Some(quality)
            }
            Err(e) => {
                tracing::warn!(
                    error = %e,
                    steps = proof.len(),
                    "internal proof checker rejected UNSAT proof"
                );
                None
            }
        }
    }

    pub(crate) fn proof_derives_empty_clause(proof: &Proof) -> bool {
        proof.steps.iter().any(|step| match step {
            ProofStep::Step { clause, .. } | ProofStep::Resolution { clause, .. } => {
                clause.is_empty()
            }
            _ => false,
        })
    }

    /// Check that the proof derives empty clause AND the resolution chain is
    /// valid (each ThResolution step's conclusion matches its premises).
    pub(super) fn proof_derives_valid_empty_clause(terms: &TermStore, proof: &Proof) -> bool {
        if !Self::proof_derives_empty_clause(proof) {
            return false;
        }
        // Quick check: run the partial checker. If it finds no errors, the
        // chain is valid.
        #[cfg(feature = "proof-checker")]
        {
            let (_, error) = check_proof_partial(proof, terms);
            error.is_none()
        }
        #[cfg(not(feature = "proof-checker"))]
        {
            let _ = terms;
            true
        }
    }

    #[cfg(feature = "proof-checker")]
    pub(super) fn run_internal_proof_check(&mut self, proof: &Proof) {
        // Strict mode (#4420): when enabled, reject trust and hole steps.
        // This gates on the SMT-LIB option `(set-option :check-proofs-strict true)`.
        if self.strict_proofs_enabled() {
            match z4_proof::check_proof_strict(proof, &self.ctx.terms) {
                Ok(_quality) => {
                    let shape = Self::proof_shape_summary(proof);
                    self.proof_check_result = Some(PartialProofCheck {
                        checked_steps: shape.total_steps,
                        skipped_hole_steps: 0,
                        total_steps: shape.total_steps,
                    });
                    self.record_proof_check_stats(0, Self::proof_shape_summary(proof));
                }
                Err(error) => {
                    let shape = Self::proof_shape_summary(proof);
                    let checked = shape.checked_steps;
                    let skipped = shape.skipped_hole_steps;
                    let total = shape.total_steps;
                    self.proof_check_result = Some(shape.clone());
                    self.record_proof_check_stats(1, shape);
                    tracing::error!(
                        error = %error,
                        checked_steps = checked,
                        skipped_hole_steps = skipped,
                        total_steps = total,
                        "strict proof checker rejected UNSAT proof"
                    );
                }
            }
            return;
        }

        let (summary, error) = check_proof_partial(proof, &self.ctx.terms);
        self.proof_check_result = Some(summary.clone());
        if let Some(error) = error {
            let shape = Self::proof_shape_summary(proof);
            let checked = shape.checked_steps;
            let skipped = shape.skipped_hole_steps;
            let total = shape.total_steps;
            self.record_proof_check_stats(1, shape);

            tracing::error!(
                error = %error,
                checked_steps = checked,
                skipped_hole_steps = skipped,
                total_steps = total,
                "internal proof checker rejected UNSAT proof"
            );
        } else {
            self.record_proof_check_stats(0, summary);
        }
    }

    #[cfg(feature = "proof-checker")]
    fn proof_shape_summary(proof: &Proof) -> PartialProofCheck {
        let total_steps = proof.steps.len() as u32;
        let skipped_hole_steps = proof
            .steps
            .iter()
            .filter(|step| {
                matches!(
                    step,
                    ProofStep::Step {
                        rule: AletheRule::Hole,
                        ..
                    }
                )
            })
            .count() as u32;

        PartialProofCheck {
            checked_steps: total_steps.saturating_sub(skipped_hole_steps),
            skipped_hole_steps,
            total_steps,
        }
    }

    #[cfg(feature = "proof-checker")]
    fn record_proof_check_stats(&mut self, failures: u64, summary: PartialProofCheck) {
        self.last_statistics
            .set_int(PROOF_CHECKER_FAILURES_KEY, failures);
        self.last_statistics.set_int(
            PROOF_CHECKER_SKIPPED_HOLE_STEPS_KEY,
            u64::from(summary.skipped_hole_steps),
        );
        self.last_statistics.set_int(
            PROOF_CHECKER_CHECKED_STEPS_KEY,
            u64::from(summary.checked_steps),
        );
        self.last_statistics.set_int(
            PROOF_CHECKER_TOTAL_STEPS_KEY,
            u64::from(summary.total_steps),
        );
    }
}
