// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consumer-facing proof export API for UNSAT results.
//!
//! Provides [`UnsatProofArtifact`] as a portable proof certificate that
//! downstream consumers (lean5, tRust, certus, tla2) can use without
//! linking against executor internals, plus a strict proof verdict and
//! consumer acceptance helpers.

use num_rational::BigRational;
use z4_core::{AletheRule, ProofStep};
use z4_proof::{
    check_proof_partial, check_proof_strict, check_proof_with_quality,
    export_alethe_with_problem_scope, PartialProofCheck, ProofCheckError, ProofQuality,
};

/// Exported strict-verification verdict for an UNSAT proof artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum StrictProofVerdict {
    /// Strict proof validation succeeded with the returned quality metrics.
    Verified(ProofQuality),
    /// Strict proof validation rejected the artifact with a stable explanation.
    Rejected(String),
}

/// Consumer-facing acceptance mode for an UNSAT proof artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofAcceptanceMode {
    /// Require strict proof validation to have succeeded.
    Strict,
    /// Require strict validation plus the lean5-supported strict subset.
    Lean5,
}

/// Error returned when an UNSAT proof artifact is not acceptable at a
/// consumer boundary.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ProofAcceptanceError {
    /// Strict proof validation failed.
    #[error("strict proof verification failed: {reason}")]
    StrictRejected {
        /// Stable rejection detail from the strict checker.
        reason: String,
    },
    /// Strict validation succeeded, but the proof is outside the lean5 subset.
    #[error("proof is not in the lean5-supported strict subset")]
    NotLean5Supported,
}

/// Structured Farkas payload for a theory lemma in the exported proof.
///
/// Coefficients are promoted to [`BigRational`] so downstream consumers can
/// use the certificate without depending on z4-core's internal `Rational64`
/// representation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct FarkasCertificate {
    /// Index of the `TheoryLemma` step in the exported proof DAG.
    pub proof_step_index: u32,
    /// Non-negative coefficients for the lemma's input constraints.
    pub coefficients: Vec<BigRational>,
}

/// A portable UNSAT proof certificate for downstream consumers.
///
/// Contains rendered Alethe proof text, diagnostic quality metrics, a strict
/// proof verdict, and a lean5-subset flag for consumers that need a stricter
/// acceptance boundary than the raw solver result.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
#[must_use]
pub struct UnsatProofArtifact {
    /// Diagnostic (non-strict) quality metrics: trust/hole/resolution/theory counts.
    ///
    /// This is a diagnostic summary. It does **not** imply full semantic
    /// verification — theory lemmas and generic rules are accepted as axioms.
    /// Use [`strict_verdict`](Self::strict_verdict) for the exported strict verdict.
    pub quality: ProofQuality,
    /// Rendered Alethe proof text (SMT-LIB compatible).
    pub alethe: String,
    /// Partial check result from the internal checker.
    pub partial_check: Option<PartialProofCheck>,
    /// Consumer-visible strict proof verdict.
    pub strict_verdict: StrictProofVerdict,
    /// Whether every proof step uses only rules in the lean5-supported subset
    /// **and** the proof passes strict semantic validation.
    ///
    /// True only when:
    /// 1. [`strict_verdict`](Self::strict_verdict) is [`StrictProofVerdict::Verified`]
    /// 2. Every `Step` rule is in the lean5 whitelist
    /// 3. Every `TheoryLemma` kind is in the lean5-supported subset (EUF only)
    pub lean5_supported: bool,
    /// Serialized LRAT certificate for the SAT backbone proof, when available.
    ///
    /// This is exported only when the stored clause trace is complete enough
    /// to replay into a standalone LRAT certificate.
    pub lrat_certificate: Option<Vec<u8>>,
    /// Structured Farkas certificates extracted from arithmetic theory lemmas.
    pub farkas_certificates: Vec<FarkasCertificate>,
}

/// Internal evaluation of all three proof quality signals.
///
/// Computed once per artifact export, preventing redundant proof walks.
struct ProofArtifactEvaluation {
    /// Non-strict diagnostic quality (theory lemmas treated as axioms).
    diagnostic_quality: ProofQuality,
    /// Partial check result from the internal checker.
    partial_check: PartialProofCheck,
    /// Result of `check_proof_strict` — `Ok` when every step is semantically
    /// verified, `Err` when any step fails strict validation.
    strict_quality: Result<ProofQuality, ProofCheckError>,
}

/// Convert the strict checker result into the stable consumer-facing verdict.
pub(super) fn strict_verdict_from_result(
    strict_quality: Result<ProofQuality, ProofCheckError>,
) -> StrictProofVerdict {
    match strict_quality {
        Ok(quality) => StrictProofVerdict::Verified(quality),
        Err(error) => StrictProofVerdict::Rejected(error.to_string()),
    }
}

/// Evaluate the proof through all three validation levels in a single pass.
fn evaluate_proof_artifact_boundary(
    proof: &z4_core::Proof,
    terms: &z4_core::TermStore,
) -> Option<ProofArtifactEvaluation> {
    let diagnostic_quality = check_proof_with_quality(proof, terms).ok()?;
    let (partial_check, _partial_err) = check_proof_partial(proof, terms);
    let strict_quality = check_proof_strict(proof, terms);
    Some(ProofArtifactEvaluation {
        diagnostic_quality,
        partial_check,
        strict_quality,
    })
}

/// Hard-coded whitelist of Alethe rules that lean5 can reconstruct as
/// kernel proof terms. Derived from trust-free QF_BOOL and simple QF_UF
/// proof evidence.
fn is_lean5_supported_rule(rule: &AletheRule) -> bool {
    matches!(
        rule,
        // Propositional tautology rules (Tseitin clausification)
        AletheRule::True
            | AletheRule::False
            | AletheRule::NotTrue
            | AletheRule::NotFalse
            | AletheRule::And
            | AletheRule::AndPos(_)
            | AletheRule::AndNeg
            | AletheRule::NotAnd
            | AletheRule::Or
            | AletheRule::OrPos(_)
            | AletheRule::OrNeg
            | AletheRule::NotOr
            | AletheRule::Implies
            | AletheRule::ImpliesPos
            | AletheRule::ImpliesNeg1
            | AletheRule::ImpliesNeg2
            | AletheRule::NotImplies1
            | AletheRule::NotImplies2
            | AletheRule::Equiv
            | AletheRule::EquivPos1
            | AletheRule::EquivPos2
            | AletheRule::EquivNeg1
            | AletheRule::EquivNeg2
            | AletheRule::NotEquiv1
            | AletheRule::NotEquiv2
            | AletheRule::Ite
            | AletheRule::ItePos1
            | AletheRule::ItePos2
            | AletheRule::IteNeg1
            | AletheRule::IteNeg2
            | AletheRule::NotIte1
            | AletheRule::NotIte2
            | AletheRule::XorPos1
            | AletheRule::XorPos2
            | AletheRule::XorNeg1
            | AletheRule::XorNeg2
            // Resolution and structural
            | AletheRule::Resolution
            | AletheRule::ThResolution
            | AletheRule::Contraction
            | AletheRule::Drup
            // EUF equality rules
            | AletheRule::Refl
            | AletheRule::Symm
            | AletheRule::Trans
            | AletheRule::Cong
            | AletheRule::EqReflexive
            | AletheRule::EqTransitive
            | AletheRule::EqCongruent
            | AletheRule::EqCongruentPred
            // Simplification (boolean only for now)
            | AletheRule::AllSimplify
            | AletheRule::BoolSimplify
    )
}

/// Check whether all proof steps use only lean5-supported rules.
///
/// Returns `true` only when:
/// 1. `trust_count == 0` and `hole_count == 0`
/// 2. Every `Step` rule is in the lean5 whitelist
/// 3. Every `TheoryLemma` kind is in the lean5-supported subset (EUF only)
fn check_lean5_supported(quality: &ProofQuality, proof: &z4_core::Proof) -> bool {
    use z4_core::TheoryLemmaKind;

    if quality.trust_count > 0 || quality.hole_count > 0 {
        return false;
    }

    for step in &proof.steps {
        match step {
            ProofStep::Step { rule, .. } => {
                if !is_lean5_supported_rule(rule) {
                    return false;
                }
            }
            ProofStep::TheoryLemma { kind, .. } => {
                // Only EUF theory lemmas are in the lean5-supported first slice.
                // Arithmetic (LraFarkas, LiaGeneric) and other theories are out
                // of scope even when they don't export as `trust`.
                if !matches!(
                    kind,
                    TheoryLemmaKind::EufTransitive
                        | TheoryLemmaKind::EufCongruent
                        | TheoryLemmaKind::EufCongruentPred
                ) {
                    return false;
                }
            }
            // Assume, Resolution, Anchor are always OK.
            _ => {}
        }
    }
    true
}

fn extract_farkas_certificates(proof: &z4_core::Proof) -> Vec<FarkasCertificate> {
    proof
        .steps
        .iter()
        .enumerate()
        .filter_map(|(proof_step_index, step)| {
            let ProofStep::TheoryLemma {
                farkas: Some(annotation),
                ..
            } = step
            else {
                return None;
            };
            Some(FarkasCertificate {
                proof_step_index: u32::try_from(proof_step_index).ok()?,
                coefficients: annotation
                    .coefficients
                    .iter()
                    .map(|coefficient| {
                        BigRational::new(
                            (*coefficient.numer()).into(),
                            (*coefficient.denom()).into(),
                        )
                    })
                    .collect(),
            })
        })
        .collect()
}

impl UnsatProofArtifact {
    /// Accept this proof artifact at a consumer-facing boundary.
    ///
    /// `Strict` requires the strict checker to have accepted the proof.
    /// `Lean5` additionally requires the proof to remain inside the current
    /// lean5-supported strict subset.
    #[must_use = "consumer boundaries must check whether an UNSAT proof artifact is acceptable"]
    pub fn accept_for_consumer(
        &self,
        mode: ProofAcceptanceMode,
    ) -> Result<(), ProofAcceptanceError> {
        match (&self.strict_verdict, mode) {
            (StrictProofVerdict::Verified(_), ProofAcceptanceMode::Strict) => Ok(()),
            (StrictProofVerdict::Verified(_), ProofAcceptanceMode::Lean5)
                if self.lean5_supported =>
            {
                Ok(())
            }
            (StrictProofVerdict::Verified(_), ProofAcceptanceMode::Lean5) => {
                Err(ProofAcceptanceError::NotLean5Supported)
            }
            (StrictProofVerdict::Rejected(reason), _) => {
                Err(ProofAcceptanceError::StrictRejected {
                    reason: reason.clone(),
                })
            }
        }
    }
}

impl super::Solver {
    /// Export the last UNSAT proof as a rendered Alethe certificate with
    /// diagnostic quality metrics, a strict verdict, and a lean5 compatibility flag.
    ///
    /// `strict_verdict` preserves the result of `check_proof_strict`.
    /// `lean5_supported` is `true` only when the strict verdict is verified
    /// **and** every rule is in the lean5 whitelist. The `quality` field
    /// remains the non-strict diagnostic summary.
    ///
    /// Returns `None` if:
    /// - The last result was not UNSAT
    /// - Proof production was not enabled
    /// - No proof was generated
    #[must_use]
    pub fn export_last_unsat_artifact(&self) -> Option<UnsatProofArtifact> {
        let proof = self.executor.last_proof()?;
        let terms = self.executor.terms();
        let assertions = &self.executor.context().assertions;

        let alethe = export_alethe_with_problem_scope(proof, terms, assertions);
        let evaluation = evaluate_proof_artifact_boundary(proof, terms)?;

        let lean5_rule_subset_ok = check_lean5_supported(&evaluation.diagnostic_quality, proof);
        let strict_verdict = strict_verdict_from_result(evaluation.strict_quality);
        let lean5_supported =
            matches!(&strict_verdict, StrictProofVerdict::Verified(_)) && lean5_rule_subset_ok;
        let farkas_certificates = extract_farkas_certificates(proof);

        Some(UnsatProofArtifact {
            alethe,
            quality: evaluation.diagnostic_quality,
            partial_check: Some(evaluation.partial_check),
            strict_verdict,
            lean5_supported,
            lrat_certificate: self.executor.last_lrat_certificate().map(<[u8]>::to_vec),
            farkas_certificates,
        })
    }

    /// Export the last UNSAT proof as rendered Alethe text.
    ///
    /// Returns `None` if the last result was not UNSAT or proofs were not enabled.
    #[must_use]
    pub fn export_last_proof_alethe(&self) -> Option<String> {
        let proof = self.executor.last_proof()?;
        let terms = self.executor.terms();
        let assertions = &self.executor.context().assertions;
        Some(export_alethe_with_problem_scope(proof, terms, assertions))
    }

    /// Get diagnostic (non-strict) quality metrics for the last UNSAT proof.
    ///
    /// This returns the same non-strict summary as `UnsatProofArtifact::quality`.
    /// For the strict verdict, use [`last_strict_proof_quality`](Self::last_strict_proof_quality).
    ///
    /// Returns `None` if the last result was not UNSAT or proofs were not enabled.
    #[must_use]
    pub fn last_proof_quality(&self) -> Option<ProofQuality> {
        let proof = self.executor.last_proof()?;
        let terms = self.executor.terms();
        check_proof_with_quality(proof, terms).ok()
    }

    /// Get strict proof validation result for the last UNSAT proof.
    ///
    /// Returns:
    /// - `None` — no UNSAT proof available
    /// - `Some(Ok(quality))` — strict validation succeeded
    /// - `Some(Err(error))` — strict validation rejected the proof
    ///
    /// This is the authoritative proof validation result. Unlike
    /// [`last_proof_quality`](Self::last_proof_quality), the strict checker
    /// rejects theory lemmas without semantic validators and unvalidated
    /// generic Alethe rules.
    #[must_use]
    pub fn last_strict_proof_quality(&self) -> Option<Result<ProofQuality, ProofCheckError>> {
        let proof = self.executor.last_proof()?;
        let terms = self.executor.terms();
        Some(check_proof_strict(proof, terms))
    }

    /// Get partial check result for the last UNSAT proof.
    ///
    /// Returns `None` if the last result was not UNSAT or proofs were not enabled.
    #[must_use]
    pub fn last_partial_proof_check(&self) -> Option<PartialProofCheck> {
        let proof = self.executor.last_proof()?;
        let terms = self.executor.terms();
        let (partial, _err) = check_proof_partial(proof, terms);
        Some(partial)
    }
}
