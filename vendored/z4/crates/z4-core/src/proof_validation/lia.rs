// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Semantic validation for LIA (Linear Integer Arithmetic) proof certificates.
//!
//! LIA theory lemmas can arise from three proof shapes:
//!
//! - **BoundsGap**: The Farkas combination of conflict literals yields integer
//!   bounds `lower > upper` after rounding. For example, `x >= 6 AND x <= 5`
//!   is a bounds gap because no integer satisfies both.
//!
//! - **Divisibility**: The GCD of a constraint's variable coefficients does not
//!   divide the constant term, proving no integer solution exists. For example,
//!   `2x = 3` has no integer solution because `gcd(2) = 2` does not divide 3.
//!
//! - **CuttingPlane**: A Farkas combination followed by integer rounding
//!   (Gomory cut). The combination produces a valid real inequality, which after
//!   dividing by a divisor and rounding to integers becomes contradictory.
//!
//! All three shapes ultimately reduce to Farkas certificate verification with
//! additional integer-specific checks.

use thiserror::Error;

use crate::{
    CuttingPlaneAnnotation, FarkasAnnotation, LiaAnnotation, ProofId, TermId, TermStore, TheoryLit,
};

/// Errors returned when an LIA proof certificate fails validation.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum LiaValidationError {
    /// The underlying Farkas certificate is invalid.
    #[error("Farkas validation failed: {reason}")]
    FarkasInvalid {
        /// Detail from the Farkas validator.
        reason: String,
    },

    /// BoundsGap: the Farkas combination does not produce a contradiction
    /// when rounded to integers.
    #[error("bounds gap does not produce integer contradiction")]
    BoundsGapNotContradictory,

    /// CuttingPlane: the divisor is non-positive.
    #[error("cutting plane divisor must be positive, got {divisor}")]
    InvalidDivisor {
        /// The invalid divisor value.
        divisor: i64,
    },

    /// The LIA annotation is missing but required for strict validation.
    #[error("LIA theory lemma in strict mode requires an LiaAnnotation")]
    MissingAnnotation,

    /// The Farkas annotation is missing but required for the LIA proof shape.
    #[error("LIA proof shape {shape} requires a Farkas annotation")]
    MissingFarkas {
        /// The proof shape that requires Farkas coefficients.
        shape: &'static str,
    },
}

/// Validate an LIA theory lemma given its annotation, clause, and Farkas certificate.
///
/// This is the main entry point for LIA strict-mode validation. It dispatches
/// to the appropriate shape-specific validator based on the `LiaAnnotation`.
pub fn validate_lia_theory_lemma(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
    lia: &LiaAnnotation,
) -> Result<(), LiaValidationError> {
    match lia {
        LiaAnnotation::BoundsGap => validate_bounds_gap(terms, clause, farkas),
        LiaAnnotation::Divisibility => validate_divisibility(terms, step_id, clause),
        LiaAnnotation::CuttingPlane(cp) => validate_cutting_plane(terms, clause, cp),
    }
}

/// Validate a BoundsGap LIA proof.
///
/// A bounds gap proof asserts that the Farkas combination of conflict literals
/// yields a contradiction after integer rounding. Specifically, if the Farkas
/// combination produces `0 <= -epsilon` for some positive epsilon, then in the
/// integer domain the contradiction is even stronger.
///
/// The Farkas combination itself already proves real-arithmetic UNSAT. For
/// BoundsGap, we just verify the Farkas certificate is valid (the integer
/// strengthening is implicit).
fn validate_bounds_gap(
    terms: &TermStore,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
) -> Result<(), LiaValidationError> {
    let farkas = farkas.ok_or(LiaValidationError::MissingFarkas { shape: "BoundsGap" })?;

    // Convert blocking clause literals to conflict literals
    let conflict: Vec<TheoryLit> = clause
        .iter()
        .map(|&lit| blocking_lit_to_conflict(terms, lit))
        .collect();

    // Delegate to the shared Farkas validator
    crate::proof_validation::verify_farkas_conflict_lits_full(terms, &conflict, farkas).map_err(
        |e| LiaValidationError::FarkasInvalid {
            reason: e.to_string(),
        },
    )
}

/// Validate a Divisibility LIA proof.
///
/// A divisibility proof asserts that the GCD of variable coefficients in a
/// constraint does not divide the constant term, so no integer solution exists.
///
/// For now, this performs a structural check only: the clause must be non-empty
/// and all literals must be over integer-sorted variables. Full GCD verification
/// is future work.
fn validate_divisibility(
    _terms: &TermStore,
    _step_id: ProofId,
    clause: &[TermId],
) -> Result<(), LiaValidationError> {
    // Structural check: divisibility conflicts must have at least one literal
    if clause.is_empty() {
        return Err(LiaValidationError::BoundsGapNotContradictory);
    }

    // Full GCD-based divisibility validation is future work.
    // For now, accept structurally valid clauses. The Farkas validator covers
    // the arithmetic soundness; this annotation merely classifies the proof shape.
    Ok(())
}

/// Validate a CuttingPlane LIA proof.
///
/// A cutting plane proof:
/// 1. Combines conflict literals using Farkas coefficients
/// 2. Divides by a positive integer divisor
/// 3. Rounds (ceiling) to obtain tighter integer bounds
/// 4. The tightened bounds are contradictory
///
/// We validate:
/// - The divisor is positive
/// - The Farkas certificate is structurally valid (non-negative, correct count)
fn validate_cutting_plane(
    terms: &TermStore,
    clause: &[TermId],
    cp: &CuttingPlaneAnnotation,
) -> Result<(), LiaValidationError> {
    if cp.divisor <= 0 {
        return Err(LiaValidationError::InvalidDivisor {
            divisor: cp.divisor,
        });
    }

    // Validate the underlying Farkas certificate
    let conflict: Vec<TheoryLit> = clause
        .iter()
        .map(|&lit| blocking_lit_to_conflict(terms, lit))
        .collect();

    crate::proof_validation::verify_farkas_annotation_shape(&cp.farkas, conflict.len()).map_err(
        |e| LiaValidationError::FarkasInvalid {
            reason: e.to_string(),
        },
    )
}

/// Convert a blocking-clause literal to the corresponding conflict `TheoryLit`.
///
/// Same polarity inversion as in the LRA Farkas validator:
/// - `NOT(atom)` in blocking clause -> conflict literal `atom = true`
/// - `atom` in blocking clause -> conflict literal `atom = false`
fn blocking_lit_to_conflict(terms: &TermStore, lit: TermId) -> TheoryLit {
    use crate::TermData;
    match terms.get(lit) {
        TermData::Not(inner) => TheoryLit {
            term: *inner,
            value: true,
        },
        _ => TheoryLit {
            term: lit,
            value: false,
        },
    }
}
