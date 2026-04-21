// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode semantic validation for `TheoryLemmaKind::LiaGeneric` proof steps.
//!
//! When an `LiaAnnotation` is present, delegates to the corresponding
//! `z4_core::proof_validation::validate_lia_theory_lemma` validator.
//!
//! When no annotation is present, falls back to Farkas validation (same as LRA)
//! since many LIA conflicts are pure bounds gaps that the Farkas validator
//! can verify without integer-specific reasoning.

use z4_core::{FarkasAnnotation, LiaAnnotation, ProofId, TermId, TermStore};

use super::ProofCheckError;

/// Validate an `LiaGeneric` theory lemma in strict mode.
///
/// Strategy:
/// 1. If an `LiaAnnotation` is present, use the LIA-specific validator.
/// 2. If only a `FarkasAnnotation` is present (no LIA annotation), fall back
///    to the shared Farkas validator (same as LRA). This handles the common
///    case where LIA conflicts are simple bounds gaps.
/// 3. If neither annotation is present, reject.
pub(crate) fn validate_lia_generic(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
    lia: Option<&LiaAnnotation>,
) -> Result<(), ProofCheckError> {
    if let Some(lia_ann) = lia {
        // LIA-specific validation
        z4_core::proof_validation::validate_lia_theory_lemma(
            terms, step_id, clause, farkas, lia_ann,
        )
        .map_err(|e| ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: e.to_string(),
        })
    } else if farkas.is_some() {
        // Fall back to Farkas validation (same as LRA)
        super::lra_farkas::validate_lra_farkas(terms, step_id, clause, farkas)
    } else {
        Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "LiaGeneric in strict mode requires either LiaAnnotation or FarkasAnnotation"
                .to_string(),
        })
    }
}
