// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lean5-specific UNSAT certificate adapter (#6354).
//!
//! Provides [`LeanUnsatCertificate`] and [`export_unsat_certificate_from_smt2`]
//! for producing trust-free Alethe proof certificates from SMT-LIB input.
//!
//! This module bridges `z4::api::UnsatProofArtifact` to a lean5-consumable
//! certificate. The boundary is a rendered, portable Alethe text — lean5 does
//! not need to link against z4 internals.

use z4::api::{Logic, ProofQuality, SolveResult, Solver, UnsatProofArtifact};

use crate::LeanError;

/// A portable UNSAT proof certificate for lean5 consumption.
///
/// Contains rendered Alethe text plus quality metrics. Only produced when the
/// proof uses exclusively lean5-supported rules (propositional + simple EUF).
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct LeanUnsatCertificate {
    /// Rendered Alethe proof text.
    pub alethe: String,
    /// Quality metrics for the proof.
    pub quality: ProofQuality,
}

/// Export an UNSAT certificate from an SMT-LIB2 input string.
///
/// Constructs a solver, enables proofs, parses the input, runs `check_sat`,
/// and returns a lean5-supported certificate if the result is UNSAT and the
/// proof passes the lean5 rule-subset gate.
///
/// # Errors
///
/// Returns an error if:
/// - The SMT-LIB2 input fails to parse
/// - The result is not UNSAT
/// - The proof is not lean5-supported (unsupported rules, trust/hole steps)
///
pub fn export_unsat_certificate_from_smt2(smt2: &str) -> Result<LeanUnsatCertificate, LeanError> {
    // Detect logic from the SMT-LIB input to configure the solver.
    let logic = detect_logic(smt2).unwrap_or(Logic::QfUf);

    #[allow(deprecated)]
    let mut solver = Solver::new(logic);
    solver.set_produce_proofs(true);

    solver
        .parse_smtlib2(smt2)
        .map_err(|e| LeanError::ProofFailed {
            message: format!("SMT-LIB2 parse error: {e}"),
        })?;

    let result = solver.check_sat();
    if result != SolveResult::Unsat {
        return Err(LeanError::ProofFailed {
            message: format!("expected UNSAT, got {result:?}"),
        });
    }

    let artifact: UnsatProofArtifact =
        solver
            .export_last_unsat_artifact()
            .ok_or_else(|| LeanError::ProofFailed {
                message: "no proof artifact available after UNSAT".to_string(),
            })?;

    if !artifact.lean5_supported {
        // Distinguish strict-check failure from unsupported-rule failure.
        let strict_detail = solver.last_strict_proof_quality().and_then(Result::err);
        let message = if let Some(strict_err) = strict_detail {
            format!("proof failed strict validation: {strict_err}")
        } else {
            format!(
                "proof uses rules not yet supported by lean5: {}",
                artifact.quality
            )
        };
        return Err(LeanError::ProofFailed { message });
    }

    Ok(LeanUnsatCertificate {
        alethe: artifact.alethe,
        quality: artifact.quality,
    })
}

/// Detect the SMT-LIB logic from the input string.
///
/// Scans for `(set-logic <name>)` and parses it as a `Logic` variant.
fn detect_logic(smt2: &str) -> Option<Logic> {
    let set_logic_idx = smt2.find("(set-logic")?;
    let rest = &smt2[set_logic_idx + "(set-logic".len()..];
    let rest = rest.trim_start();
    let end = rest.find(')')?;
    let logic_name = rest[..end].trim();
    logic_name.parse().ok()
}

#[cfg(test)]
#[path = "proof_tests.rs"]
mod tests;
