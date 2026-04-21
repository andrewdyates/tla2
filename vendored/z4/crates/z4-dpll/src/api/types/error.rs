// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver error types.

use z4_core::Sort;

use crate::ExecutorError;

/// Display wrapper for `Vec<Sort>` that formats as comma-separated list without brackets.
pub(crate) struct DisplaySorts<'a>(pub(crate) &'a Vec<Sort>);

impl std::fmt::Display for DisplaySorts<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, sort) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{sort}")?;
        }
        Ok(())
    }
}

/// Error type for Solver API operations
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum SolverError {
    /// The specified logic is not supported
    #[error("unsupported logic: {0}. Supported logics: \
        ALL, AUFDT, AUFDTLIA, AUFDTLIRA, AUFLIA, AUFLIRA, AUFLRA, \
        LIA, LIRA, LRA, NIA, NIRA, NRA, \
        QF_ABV, QF_AUFBV, QF_AUFLIA, QF_AUFLIRA, QF_AUFLRA, QF_AX, \
        QF_BV, QF_BVFP, QF_DT, QF_FP, QF_LIA, QF_LIRA, QF_LRA, \
        QF_NIA, QF_NIRA, QF_NRA, QF_S, QF_SEQ, QF_SLIA, QF_SNIA, \
        QF_UF, QF_UFBV, QF_UFLIA, QF_UFLRA, QF_UFNIA, QF_UFNIRA, QF_UFNRA, \
        UF, UFDT, UFDTLIA, UFDTLIRA, UFDTLRA, UFDTNIA, UFDTNIRA, UFDTNRA, \
        UFLIA, UFLRA, UFNIA, UFNIRA, UFNRA, HORN")]
    UnsupportedLogic(String),
    /// Other executor error
    #[error(transparent)]
    ExecutorError(ExecutorError),
    /// API-level sort mismatch (e.g., passing Bool to a BV operator)
    #[error(
        "sort mismatch in {operation}: expected {expected}, got {}",
        DisplaySorts(got)
    )]
    SortMismatch {
        /// Name of the operation that failed
        operation: &'static str,
        /// Description of the expected sort
        expected: &'static str,
        /// Actual sorts received
        got: Vec<Sort>,
    },
    /// API-level invalid argument (e.g., bvextract range errors)
    #[error("invalid argument to {operation}: {message}")]
    InvalidArgument {
        /// Name of the operation that failed
        operation: &'static str,
        /// Description of why the argument is invalid
        message: String,
    },
    /// Invalid quantifier trigger/pattern specification.
    #[error("invalid trigger for {operation}: {message}")]
    InvalidTrigger {
        /// Name of the operation that failed
        operation: &'static str,
        /// Description of why the trigger is invalid
        message: String,
    },
    /// The solver panicked during a `try_check_sat*` call.
    ///
    /// The contained message is extracted from the panic payload when possible.
    /// Downstream consumers can match on this variant instead of independently
    /// wrapping every call in `catch_unwind(AssertUnwindSafe(...))`.
    ///
    /// **Warning:** After a `SolverPanic`, the solver's internal state is
    /// likely corrupted. Do not call `check_sat` or `try_check_sat` again
    /// on the same `Solver` instance — create a fresh solver instead.
    #[error("solver panic: {0}")]
    SolverPanic(String),
    /// A [`ModelValue`](super::ModelValue) was not the expected variant.
    #[error("model value mismatch: expected {expected}, got {actual}")]
    ModelValueMismatch {
        /// The expected variant name (e.g., "Bool", "Int").
        expected: &'static str,
        /// Description of the actual variant received.
        actual: String,
    },
    /// DPLL(T) internal error (theory-SAT mapping failure or unexpected result).
    ///
    /// This indicates a bug in the solver's theory integration layer.
    /// Unlike `SolverPanic`, the solver state is still valid after this error.
    #[error("DPLL internal error: {0}")]
    DpllInternal(#[from] crate::DpllError),
    /// No solve result is available (no `check_sat` has been called).
    #[error("no solve result available — call check_sat first")]
    NoResult,
    /// The last solve result was not Sat, so no model is available.
    #[error("last result was not sat — model only available after sat")]
    NotSat,
    /// The last solve result was not Unsat, so no unsat core is available.
    #[error("last result was not unsat — unsat core only available after unsat")]
    NotUnsat,
    /// The executor failed to generate a model string.
    ///
    /// This indicates a bug in the executor's model generation. The contained
    /// string is the raw error output (e.g., an `(error ...)` response) or
    /// a description of the failure mode.
    #[error("model generation failed: {0}")]
    ModelGenerationFailed(String),
    /// The executor failed to generate or parse an unsat core.
    #[error("unsat core generation failed: {0}")]
    UnsatCoreGenerationFailed(String),
}

impl From<ExecutorError> for SolverError {
    fn from(e: ExecutorError) -> Self {
        match e {
            ExecutorError::UnsupportedLogic(s) => Self::UnsupportedLogic(s),
            other => Self::ExecutorError(other),
        }
    }
}
