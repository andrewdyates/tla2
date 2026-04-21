// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Type definitions for the SMT executor.
//!
//! This module contains error types, result types, and statistics structures
//! used by the [`Executor`](crate::Executor).

use std::collections::BTreeMap;
use z4_core::string_literal;
use z4_core::{VerificationBoundary, VerificationFailure};
use z4_frontend::ElaborateError;

use crate::DpllError;

/// Typed model validation error replacing the previous `String`-based contract.
///
/// The previous `ExecutorError::ModelValidation(String)` relied on substring
/// matching (`"could not be model-validated"`) to decide whether to degrade
/// SAT to Unknown or to surface a hard error. This enum makes that decision
/// compile-time checkable.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ModelValidationError {
    /// This layer could not prove the model satisfies the property.
    /// The caller should degrade SAT to Unknown.
    #[error("model validation incomplete: {0}")]
    Incomplete(VerificationFailure),
    /// A concrete contradiction was found — the model definitely violates
    /// the property. This is a hard error.
    #[error("model validation violated: {0}")]
    Violated(VerificationFailure),
}

impl ModelValidationError {
    /// Create an `Incomplete` error for a specific boundary.
    pub fn incomplete(boundary: VerificationBoundary, detail: impl Into<String>) -> Self {
        Self::Incomplete(VerificationFailure {
            boundary,
            detail: detail.into(),
        })
    }

    /// Create a `Violated` error for a specific boundary.
    pub fn violated(boundary: VerificationBoundary, detail: impl Into<String>) -> Self {
        Self::Violated(VerificationFailure {
            boundary,
            detail: detail.into(),
        })
    }

    /// Returns `true` if this is an `Incomplete` error (should degrade to Unknown).
    pub fn is_incomplete(&self) -> bool {
        matches!(self, Self::Incomplete(_))
    }

    /// Returns `true` if this is a `Violated` error (hard failure).
    pub fn is_violated(&self) -> bool {
        matches!(self, Self::Violated(_))
    }

    /// Returns the failure detail for either variant.
    pub fn failure(&self) -> &VerificationFailure {
        match self {
            Self::Incomplete(f) | Self::Violated(f) => f,
        }
    }

    /// Check if the human-readable detail string contains a substring.
    ///
    /// Convenience for test assertions migrating from the old `String`-based
    /// error contract. Prefer `is_incomplete()` / `is_violated()` for new
    /// code.
    pub fn contains(&self, needle: &str) -> bool {
        self.failure().detail.contains(needle)
    }
}

/// Error during SMT execution
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ExecutorError {
    /// Elaboration error
    #[error("elaboration error: {0}")]
    Elaborate(#[from] ElaborateError),
    /// DPLL(T) solver error (theory-SAT mapping failure or unexpected result)
    #[error("DPLL solver error: {0}")]
    Dpll(#[from] DpllError),
    /// Unsupported logic
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
    /// Unsupported optimization feature
    #[error("unsupported optimization: {0}")]
    UnsupportedOptimization(String),
    /// Model validation failed — typed contract replaces previous `String`.
    #[error("model validation failed: {0}")]
    ModelValidation(ModelValidationError),
}

/// Result type for executor operations
pub type Result<T> = std::result::Result<T, ExecutorError>;

/// Reason for an Unknown result from check-sat
///
/// When the solver returns Unknown, this enum provides structured information
/// about why satisfiability could not be determined. Modeled after CVC5's
/// `UnknownExplanation` enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UnknownReason {
    /// Time limit exceeded
    Timeout,
    /// Resource limit exceeded
    ResourceLimit,
    /// Memory limit exceeded
    MemoryLimit,
    /// User or portfolio interrupted the solver
    Interrupted,
    /// Logic requires unimplemented features
    Incomplete,
    /// E-matching round budget or per-round instantiation limit exhausted.
    /// The solver could not explore all possible instantiations within budget.
    QuantifierRoundLimit,
    /// Deferred quantifier instantiations remain that could invalidate the model.
    QuantifierDeferred,
    /// Triggerless quantifiers that neither E-matching nor CEGQI could handle.
    QuantifierUnhandled,
    /// CEGQI-specific incompleteness: mixed forall/exists, failed ground
    /// disambiguation, or incomplete witness/counterexample search.
    QuantifierCegqiIncomplete,
    /// E-matching processed an exists quantifier but added instances as
    /// conjunctive assertions. UNSAT from the conjunction is unreliable
    /// because exists only needs one witness (#3593).
    QuantifierEmatchingExistsIncomplete,
    /// Maximum split limit reached (theory solver)
    SplitLimit,
    /// Expression split needed but not yet implemented (#1915)
    ExpressionSplit,
    /// Unsupported feature encountered
    Unsupported,
    /// Internal executor error (e.g., model validation failure).
    /// Use `Solver::get_executor_error()` for the detail message.
    InternalError,
    /// No specific reason available
    Unknown,
}

impl UnknownReason {
    /// Returns `true` if this reason is any quantifier-related incompleteness.
    pub fn is_quantifier(&self) -> bool {
        matches!(
            self,
            Self::QuantifierRoundLimit
                | Self::QuantifierDeferred
                | Self::QuantifierUnhandled
                | Self::QuantifierCegqiIncomplete
                | Self::QuantifierEmatchingExistsIncomplete
        )
    }
}

impl std::fmt::Display for UnknownReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Use lowercase symbols matching SMT-LIB convention (cvc5/yices2 style)
        match self {
            Self::Timeout => write!(f, "timeout"),
            Self::ResourceLimit => write!(f, "resourceout"),
            Self::MemoryLimit => write!(f, "memout"),
            Self::Interrupted => write!(f, "interrupted"),
            Self::Incomplete => write!(f, "incomplete"),
            Self::QuantifierRoundLimit => write!(f, "(incomplete quantifier-round-limit)"),
            Self::QuantifierDeferred => write!(f, "(incomplete quantifier-deferred)"),
            Self::QuantifierUnhandled => write!(f, "(incomplete quantifier-unhandled)"),
            Self::QuantifierCegqiIncomplete => write!(f, "(incomplete quantifier-cegqi)"),
            Self::QuantifierEmatchingExistsIncomplete => {
                write!(f, "(incomplete quantifier-ematching-exists)")
            }
            Self::SplitLimit => write!(f, "incomplete"),
            Self::ExpressionSplit => write!(f, "incomplete"),
            Self::Unsupported => write!(f, "unsupported"),
            Self::InternalError => write!(f, "internal-error"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

/// Value type for extensible statistics
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum StatValue {
    /// Integer count
    Int(u64),
    /// Floating point value (e.g., time in seconds)
    Float(f64),
    /// String value (e.g., labels)
    String(String),
}

impl std::fmt::Display for StatValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int(v) => write!(f, "{v}"),
            Self::Float(v) => write!(f, "{v:.2}"),
            Self::String(v) => write!(f, "{}", string_literal(v)),
        }
    }
}

/// Solver statistics from the last check-sat call
///
/// Provides performance metrics for debugging and analysis.
/// Modeled after Z3's `Z3_solver_get_statistics` and CVC5's `Solver::getStatistics()`.
#[derive(Debug, Clone, Default, PartialEq)]
#[non_exhaustive]
pub struct Statistics {
    // =========================================================================
    // SAT-level statistics
    // =========================================================================
    /// Number of conflicts encountered during solving
    pub conflicts: u64,
    /// Number of decisions made
    pub decisions: u64,
    /// Number of unit propagations
    pub propagations: u64,
    /// Number of restarts
    pub restarts: u64,
    /// Number of learned clauses currently retained
    pub learned_clauses: u64,
    /// Number of clauses deleted during clause management
    pub deleted_clauses: u64,

    // =========================================================================
    // Theory-level statistics
    // =========================================================================
    /// Number of theory conflicts (theory solver detected inconsistency)
    pub theory_conflicts: u64,
    /// Number of theory propagations
    pub theory_propagations: u64,

    // =========================================================================
    // Problem size
    // =========================================================================
    /// Number of variables in the problem
    pub num_vars: u64,
    /// Number of clauses in the problem
    pub num_clauses: u64,
    /// Number of assertions
    pub num_assertions: u64,

    // =========================================================================
    // Extensible statistics
    // =========================================================================
    /// Additional statistics (for theory-specific or future metrics)
    pub extra: BTreeMap<String, StatValue>,
}

impl Statistics {
    /// Create an empty statistics object
    pub fn new() -> Self {
        Self::default()
    }

    /// Assert internal consistency invariants (debug builds only).
    ///
    /// Theory-level counters must be subsets of SAT-level counters:
    /// - theory_conflicts <= conflicts
    /// - theory_propagations <= propagations
    #[inline]
    pub(crate) fn debug_assert_consistency(&self) {
        debug_assert!(
            self.theory_conflicts <= self.conflicts,
            "BUG: theory_conflicts ({}) > conflicts ({})",
            self.theory_conflicts,
            self.conflicts,
        );
        debug_assert!(
            self.theory_propagations <= self.propagations,
            "BUG: theory_propagations ({}) > propagations ({})",
            self.theory_propagations,
            self.propagations,
        );
    }

    /// Get an integer statistic by name
    pub fn get_int(&self, name: &str) -> Option<u64> {
        match name {
            "conflicts" => Some(self.conflicts),
            "decisions" => Some(self.decisions),
            "propagations" => Some(self.propagations),
            "restarts" => Some(self.restarts),
            "learned_clauses" => Some(self.learned_clauses),
            "deleted_clauses" => Some(self.deleted_clauses),
            "theory_conflicts" => Some(self.theory_conflicts),
            "theory_propagations" => Some(self.theory_propagations),
            "num_vars" => Some(self.num_vars),
            "num_clauses" => Some(self.num_clauses),
            "num_assertions" => Some(self.num_assertions),
            _ => self.extra.get(name).and_then(|v| {
                if let StatValue::Int(i) = v {
                    Some(*i)
                } else {
                    None
                }
            }),
        }
    }

    /// Set an extra integer statistic
    pub fn set_int(&mut self, name: &str, value: u64) {
        self.extra.insert(name.to_string(), StatValue::Int(value));
    }

    /// Set an extra float statistic
    pub fn set_float(&mut self, name: &str, value: f64) {
        self.extra.insert(name.to_string(), StatValue::Float(value));
    }
}

impl std::fmt::Display for Statistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "(:statistics")?;
        writeln!(f, "  :conflicts {}", self.conflicts)?;
        writeln!(f, "  :decisions {}", self.decisions)?;
        writeln!(f, "  :propagations {}", self.propagations)?;
        writeln!(f, "  :restarts {}", self.restarts)?;
        writeln!(f, "  :learned-clauses {}", self.learned_clauses)?;
        writeln!(f, "  :deleted-clauses {}", self.deleted_clauses)?;
        writeln!(f, "  :theory-conflicts {}", self.theory_conflicts)?;
        writeln!(f, "  :theory-propagations {}", self.theory_propagations)?;
        writeln!(f, "  :num-vars {}", self.num_vars)?;
        writeln!(f, "  :num-clauses {}", self.num_clauses)?;
        writeln!(f, "  :num-assertions {}", self.num_assertions)?;
        for (name, value) in &self.extra {
            writeln!(f, "  :{name} {value}")?;
        }
        write!(f, ")")
    }
}

// Re-export SolveResult from the API types for backward compatibility.
// Previously this module defined its own `CheckSatResult` with identical variants.
pub(crate) use crate::api::types::SolveResult;

#[cfg(test)]
mod tests;
