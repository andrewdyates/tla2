// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solve result types.

use z4_sat::SatResult;

/// Result of a satisfiability check
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
#[must_use = "solve results must be checked — ignoring Sat/Unsat loses correctness"]
pub enum SolveResult {
    /// The constraints are satisfiable
    Sat,
    /// The constraints are unsatisfiable
    Unsat,
    /// The solver could not determine satisfiability
    Unknown,
}

impl SolveResult {
    /// Returns true if the result is Sat
    #[inline]
    pub fn is_sat(&self) -> bool {
        matches!(self, Self::Sat)
    }

    /// Returns true if the result is Unsat
    #[inline]
    pub fn is_unsat(&self) -> bool {
        matches!(self, Self::Unsat)
    }

    /// Returns true if the result is Unknown
    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown)
    }
}

impl std::fmt::Display for SolveResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sat => write!(f, "sat"),
            Self::Unsat => write!(f, "unsat"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

impl From<SatResult> for SolveResult {
    fn from(result: SatResult) -> Self {
        match result {
            SatResult::Sat(_) => Self::Sat,
            SatResult::Unsat => Self::Unsat,
            SatResult::Unknown => Self::Unknown,
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        }
    }
}

/// Error returned when a solve result is not acceptable at a consumer boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ConsumerAcceptanceError {
    /// SAT was reported, but model validation did not run.
    #[error("sat result rejected at consumer boundary: model validation did not run")]
    SatModelNotValidated,
}

/// A `SolveResult` that has been validated by the executor.
///
/// For `Sat` results, this records whether model validation passed
/// (via `finalize_sat_model_validation`). Consumers must inspect
/// [`was_model_validated()`](Self::was_model_validated) or call
/// [`accept_for_consumer()`](Self::accept_for_consumer) before treating a SAT
/// model as trusted. For `Unsat` results, the DPLL(T) proof was produced (when
/// proofs are enabled).
///
/// The private inner field prevents construction outside z4-dpll.
/// Within the crate, only the validated code path in `Solver::check_sat()`
/// can create this type.
///
/// Part of #5748: structural verification invariant Phase 3.
#[derive(Debug, Clone, Copy)]
#[must_use = "solver results must be checked — ignoring Sat/Unsat loses correctness"]
pub struct VerifiedSolveResult {
    result: SolveResult,
    model_validated: bool,
}

impl VerifiedSolveResult {
    /// Wrap a validated solve result with model validation provenance (#5973).
    ///
    /// Only callable within z4-dpll. The caller MUST have validated the
    /// result through the executor's model validation pipeline.
    pub(crate) fn from_validated(result: SolveResult, model_validated: bool) -> Self {
        Self {
            result,
            model_validated,
        }
    }

    /// Whether model validation actually ran for this result.
    #[inline]
    pub fn was_model_validated(&self) -> bool {
        self.model_validated
    }

    /// Get the underlying solve result.
    #[inline]
    pub fn result(&self) -> SolveResult {
        self.result
    }

    /// Accept this solve result at a consumer-facing boundary.
    ///
    /// High-level consumers must call this before surfacing a SAT model or
    /// counterexample as trusted. SAT results where model validation did not
    /// run are rejected.
    #[must_use = "consumer boundaries must check whether SAT is acceptable before surfacing a model"]
    #[inline]
    pub fn accept_for_consumer(self) -> Result<SolveResult, ConsumerAcceptanceError> {
        match self.result {
            SolveResult::Sat if !self.model_validated => {
                Err(ConsumerAcceptanceError::SatModelNotValidated)
            }
            _ => Ok(self.result),
        }
    }

    /// Returns true if the result is Sat.
    #[inline]
    pub fn is_sat(&self) -> bool {
        self.result.is_sat()
    }

    /// Returns true if the result is Unsat.
    #[inline]
    pub fn is_unsat(&self) -> bool {
        self.result.is_unsat()
    }

    /// Returns true if the result is Unknown.
    #[inline]
    pub fn is_unknown(&self) -> bool {
        self.result.is_unknown()
    }

    /// Consume and return the inner `SolveResult`.
    ///
    /// `SolveResult` is `Copy` so this is equivalent to `.result()`, but
    /// the method exists for API consistency with the other verified newtypes.
    ///
    /// **Trust boundary:** The returned `SolveResult` carries no compile-time
    /// proof of verification. Verification happened at construction time (via
    /// the executor's model validation pipeline). Prefer using
    /// [`.accept_for_consumer()`](Self::accept_for_consumer) at public
    /// boundaries, or [`.result()`](Self::result) / [`.is_sat()`](Self::is_sat)
    /// / [`.is_unsat()`](Self::is_unsat) when you explicitly need the raw
    /// diagnostic state.
    #[inline]
    pub fn into_inner(self) -> SolveResult {
        self.result
    }
}

impl std::fmt::Display for VerifiedSolveResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.result.fmt(f)
    }
}

impl PartialEq<SolveResult> for VerifiedSolveResult {
    fn eq(&self, other: &SolveResult) -> bool {
        self.result == *other
    }
}

impl PartialEq<VerifiedSolveResult> for SolveResult {
    fn eq(&self, other: &VerifiedSolveResult) -> bool {
        *self == other.result
    }
}

impl PartialEq for VerifiedSolveResult {
    fn eq(&self, other: &Self) -> bool {
        self.result == other.result
    }
}

impl Eq for VerifiedSolveResult {}
