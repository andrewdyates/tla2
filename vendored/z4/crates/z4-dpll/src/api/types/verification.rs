// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Verification envelope types: level, summary, and solve details.

use crate::executor_types::{Statistics, UnknownReason};

use super::{ConsumerAcceptanceError, SolveResult, Term, VerifiedSolveResult};

/// The level of runtime verification applied to a solve result.
///
/// Z4 performs different levels of verification depending on build mode and
/// configuration. Consumers need to know what level of trust to place in a
/// result without inspecting scattered env vars.
///
/// The levels encode two independent axes: debug assertions (compile-time)
/// and proof production (runtime). `FullyVerified` means both are active.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum VerificationLevel {
    /// No runtime verification beyond the solver's own correctness.
    /// This is the default in release builds without proof production.
    Trusted,
    /// Debug-assertion checks ran (structural + semantic theory conflict
    /// verification, EUF re-checking, propagation validation).
    /// Active when `cfg(debug_assertions)` is true.
    DebugChecked,
    /// Proof production was enabled: the solver generated a DRAT/LRAT proof
    /// for UNSAT results or validated the model for SAT results.
    ProofChecked,
    /// Both debug-assertion checks and proof production were active.
    /// Maximum internal verification.
    FullyVerified,
}

impl VerificationLevel {
    /// Compute the verification level from the current runtime state.
    ///
    /// Examines `cfg(debug_assertions)` (compile-time) and whether proof
    /// production is enabled (runtime) to determine the level.
    #[must_use]
    pub fn from_state(proofs_enabled: bool) -> Self {
        let debug = cfg!(debug_assertions);
        match (debug, proofs_enabled) {
            (false, false) => Self::Trusted,
            (true, false) => Self::DebugChecked,
            (false, true) => Self::ProofChecked,
            (true, true) => Self::FullyVerified,
        }
    }

    /// Returns true if debug-assertion checks are active.
    #[must_use]
    pub fn has_debug_checks(&self) -> bool {
        matches!(self, Self::DebugChecked | Self::FullyVerified)
    }

    /// Returns true if proof production is active.
    #[must_use]
    pub fn has_proof_checking(&self) -> bool {
        matches!(self, Self::ProofChecked | Self::FullyVerified)
    }

    /// Returns true if this is the minimum trust level (no extra verification).
    #[must_use]
    pub fn is_trusted_only(&self) -> bool {
        matches!(self, Self::Trusted)
    }
}

impl std::fmt::Display for VerificationLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Trusted => write!(f, "trusted"),
            Self::DebugChecked => write!(f, "debug-checked"),
            Self::ProofChecked => write!(f, "proof-checked"),
            Self::FullyVerified => write!(f, "fully-verified"),
        }
    }
}

/// Verification metadata attached to a solve result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub struct VerificationSummary {
    /// True when `validate_model()` actually ran and passed on this solve call.
    /// False when validation was skipped (deferred, or result was UNSAT/Unknown).
    pub sat_model_validated: bool,
    /// True when an UNSAT result has a proof artifact available.
    pub unsat_proof_available: bool,
    /// Number of internal proof-checker failures recorded for the solve call.
    pub unsat_proof_checker_failures: u64,
    /// Number of assertions independently verified by the model evaluator.
    /// Excludes theory-delegated checks counted in `sat_delegated_checks`.
    pub sat_independent_checks: u64,
    /// Number of assertions accepted via theory-solver delegation
    /// (the theory solver verified consistency during solving).
    pub sat_delegated_checks: u64,
    /// Number of assertions where verification was incomplete or skipped
    /// (SAT fallback, evaluator incompleteness, or uncheckable categories such
    /// as internal helper assertions / quantified assertions).
    /// When > 0 and `sat_model_validated` is false, the result was
    /// degraded from SAT to Unknown due to incomplete evidence.
    pub sat_incomplete_checks: u64,
}

/// Atomic solve envelope containing result, diagnostics, and verification provenance.
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use]
pub struct SolveDetails {
    /// SAT/UNSAT/UNKNOWN result — carries verification provenance.
    /// Part of #5750: Phase 5 escape hatch sealing.
    pub result: VerifiedSolveResult,
    /// Solver statistics captured from the same solve call.
    pub statistics: Statistics,
    /// Structured reason for Unknown, when available.
    pub unknown_reason: Option<UnknownReason>,
    /// Executor error detail when `unknown_reason` is `InternalError`.
    ///
    /// Captures the underlying error message from the same solve call,
    /// eliminating the need for a follow-up `get_executor_error()` call.
    pub executor_error: Option<String>,
    /// Verification/provenance summary for the solve call.
    pub verification: VerificationSummary,
    /// Level of runtime verification applied to this solve result.
    pub verification_level: VerificationLevel,
}

impl SolveDetails {
    /// Accept this solve envelope at a consumer-facing boundary.
    ///
    /// This keeps the low-level diagnostic result intact while centralizing the
    /// public policy for when SAT may be surfaced as a trusted success.
    #[must_use = "consumer boundaries must check whether SAT is acceptable before surfacing a model"]
    pub fn accept_for_consumer(&self) -> Result<SolveResult, ConsumerAcceptanceError> {
        self.result.accept_for_consumer()
    }
}

/// Atomic solve envelope for assumption-based solving.
///
/// Wraps `SolveDetails` with the unsat-assumption subset from the same solve
/// call, eliminating the split contract of solving first then reading
/// `get_unsat_assumptions()` separately.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct AssumptionSolveDetails {
    /// The base solve envelope (result, statistics, verification, etc.).
    pub solve: SolveDetails,
    /// The subset of assumptions that caused UNSAT, captured from the same
    /// solve call. `None` when the result is not UNSAT or when no assumptions
    /// were provided.
    pub unsat_assumptions: Option<Vec<Term>>,
}

impl AssumptionSolveDetails {
    /// Accept this solve envelope at a consumer-facing boundary.
    #[must_use = "consumer boundaries must check whether SAT is acceptable before surfacing a model"]
    pub fn accept_for_consumer(&self) -> Result<SolveResult, ConsumerAcceptanceError> {
        self.solve.accept_for_consumer()
    }
}
