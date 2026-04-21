//! Error types for TLA+ to z4 translation
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use thiserror::Error;
use z4_dpll::SolverError;

/// Errors that can occur during TLA+ to z4 translation
#[derive(Debug, Error)]
pub enum Z4Error {
    /// Variable not found in translation context
    #[error("unknown variable: {0}")]
    UnknownVariable(String),

    /// Type mismatch during translation
    #[error("type mismatch for '{name}': expected {expected}, got {actual}")]
    TypeMismatch {
        /// Variable or expression name
        name: String,
        /// Expected type
        expected: String,
        /// Actual type found
        actual: String,
    },

    /// Expression cannot be translated to z4
    #[error("untranslatable expression: {0}")]
    UntranslatableExpr(String),

    /// Unsupported TLA+ operator
    #[error("unsupported operator: {0}")]
    UnsupportedOp(String),

    /// z4 solver returned unknown
    #[error("solver returned unknown")]
    SolverUnknown,

    /// No initial states found
    #[error("no initial states satisfy Init predicate")]
    NoInitStates,

    /// Integer overflow during translation
    #[error("integer too large for SMT: {0}")]
    IntegerOverflow(String),

    /// BMC bound too large
    #[error("BMC bound {bound} exceeds maximum {max}")]
    BmcBoundTooLarge {
        /// The requested BMC bound.
        bound: usize,
        /// The maximum allowed BMC bound (`MAX_BMC_BOUND`).
        max: usize,
    },

    /// z4 solver error (sort mismatch, invalid argument, etc.)
    #[error("z4 solver error: {0}")]
    Solver(#[from] SolverError),
}

/// Maximum reasonable BMC bound to prevent memory exhaustion.
/// A bound of 1M would allocate 1M z4 terms per variable, likely OOM.
pub(crate) const MAX_BMC_BOUND: usize = 100_000;

impl From<String> for Z4Error {
    fn from(msg: String) -> Self {
        Z4Error::UntranslatableExpr(msg)
    }
}

/// Result type for z4 operations
pub type Z4Result<T> = Result<T, Z4Error>;
