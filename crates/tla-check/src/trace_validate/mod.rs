// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trace validation engine using explicit-state enumeration.
//!
//! This module implements trace validation using the <code>Candidates\[i\]</code> algorithm:
//! - <code>Candidates\[0\]</code> = Init states filtered by <code>observation\[0\]</code>
//! - <code>Candidates\[i+1\]</code> = successors of <code>Candidates\[i\]</code> filtered by <code>observation\[i+1\]</code>
//! - FAIL if <code>Candidates\[i+1\]</code> = empty
//! - SUCCESS if all steps pass
//!
//! ## Design
//!
//! The MVP uses interpreter-level enumeration (EvalCtx) rather than compiled
//! StateMachine trait implementations. This allows validation against any
//! TLA+ spec without requiring code generation.
//!
//! See `designs/2026-02-01-trace-validation-via-generated-oracles.md` for details.
//! See `reports/research/2026-02-02-trace-validation-mvp-architecture.md` for architecture.

mod engine;

#[cfg(test)]
mod tests;

use crate::error::EvalError;
use crate::json_codec::JsonValueDecodeError;

pub use engine::TraceValidationEngine;

/// Action label enforcement mode for trace validation.
///
/// Controls whether action label mismatches are treated as errors or warnings.
/// In `Error` mode (default), a trace step whose action label doesn't match any
/// observed transition fails validation. In `Warn` mode, mismatches are collected
/// as warnings but validation continues using observation-matched candidates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ActionLabelMode {
    /// Action label mismatches are hard errors (default).
    #[default]
    Error,
    /// Action label mismatches produce warnings but do not fail validation.
    Warn,
}

/// Diagnostic information collected when a trace validation step fails.
///
/// Captures what was attempted so users can understand why validation failed
/// and which action came closest to matching.
#[derive(Debug, Clone)]
pub struct StepDiagnostic {
    /// Total successor states enumerated from prior candidates.
    pub successors_enumerated: usize,
    /// Number of successor states that matched the observation constraint.
    pub observation_matches: usize,
    /// Per-action match results (action name -> matched at least one transition).
    /// Only populated when action labels are present in the trace.
    pub action_results: Vec<ActionMatchResult>,
    /// Names of all detected spec actions (from Next decomposition).
    pub available_actions: Vec<String>,
}

/// Result of attempting to match a single spec action against transitions.
#[derive(Debug, Clone)]
pub struct ActionMatchResult {
    /// Name of the spec action.
    pub name: String,
    /// Whether at least one observation-matching transition also satisfied this action.
    pub matched: bool,
}

impl std::fmt::Display for StepDiagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} successors enumerated, {} matched observation",
            self.successors_enumerated, self.observation_matches
        )?;
        if !self.action_results.is_empty() {
            write!(f, "; actions attempted: ")?;
            for (i, ar) in self.action_results.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(
                    f,
                    "{}={}",
                    ar.name,
                    if ar.matched { "matched" } else { "no match" }
                )?;
            }
        }
        if !self.available_actions.is_empty() {
            write!(f, "; available spec actions: ")?;
            for (i, name) in self.available_actions.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{name}")?;
            }
        }
        Ok(())
    }
}

/// Error during trace validation.
#[derive(Debug, thiserror::Error)]
pub enum TraceValidationError {
    #[error("trace step {step} has no matching spec states (0 candidates); {diagnostic}")]
    NoMatchingStates {
        step: usize,
        diagnostic: StepDiagnostic,
    },

    #[error("trace step {step} references unknown action label {label:?}")]
    UnknownActionLabel { step: usize, label: String },

    #[error("trace step {step} action label {label:?} did not match any observed transition; {diagnostic}")]
    ActionLabelNotSatisfied {
        step: usize,
        label: String,
        diagnostic: StepDiagnostic,
    },

    #[error("initial state enumeration failed: {0}")]
    InitEnumerationFailed(#[source] EvalError),

    #[error("successor enumeration failed at step {step}: {source}")]
    SuccessorEnumerationFailed {
        step: usize,
        #[source]
        source: EvalError,
    },

    #[error("action expression evaluation failed at step {step}: {source}")]
    ActionExprEvalFailed {
        step: usize,
        #[source]
        source: EvalError,
    },

    #[error("observation decode failed at step {step}, variable {variable:?}: {source}")]
    ObservationDecodeError {
        step: usize,
        variable: String,
        #[source]
        source: JsonValueDecodeError,
    },

    #[error("trace variable {variable:?} not found in spec variables")]
    UnknownTraceVariable { variable: String },

    #[error("spec variable {variable:?} missing from trace observation at step {step}")]
    MissingSpecVariable { step: usize, variable: String },
}

/// A warning emitted during trace validation (when ActionLabelMode::Warn).
#[derive(Debug, Clone)]
pub struct TraceValidationWarning {
    /// The step index where the warning occurred.
    pub step: usize,
    /// Human-readable warning message.
    pub message: String,
}

/// Result of successful trace validation.
#[derive(Debug, Clone)]
pub struct TraceValidationSuccess {
    /// Total number of trace steps validated.
    pub steps_validated: usize,
    /// Number of candidate states at each step (index = step number).
    pub candidates_per_step: Vec<usize>,
    /// Total candidate states enumerated.
    pub total_candidates_enumerated: usize,
    /// Warnings collected during validation (non-empty only in ActionLabelMode::Warn).
    pub warnings: Vec<TraceValidationWarning>,
}

/// Result of trace validation.
pub type TraceValidationResult = Result<TraceValidationSuccess, TraceValidationError>;

/// Builder for trace validation configuration.
///
/// Stores Init/Next operator names for use when constructing a TraceValidationEngine.
/// The CLI integration (#1082) will use this to resolve operator definitions from
/// the parsed module before creating the engine.
///
/// # Example
/// ```no_run
/// # use tla_check::TraceValidationBuilder;
/// let builder = TraceValidationBuilder::new()
///     .init_name("MCInit")
///     .next_name("MCNext");
/// // CLI will resolve builder.get_init_name() / get_next_name() to OperatorDefs
/// // then call TraceValidationEngine::new(ctx, init_def, next_def, vars)
/// ```
#[derive(Debug, Clone)]
pub struct TraceValidationBuilder {
    init_name: String,
    next_name: String,
}

impl TraceValidationBuilder {
    /// Create a new builder with default Init/Next names.
    pub fn new() -> Self {
        Self {
            init_name: "Init".to_string(),
            next_name: "Next".to_string(),
        }
    }

    /// Set the Init predicate name.
    pub fn init_name(mut self, name: impl Into<String>) -> Self {
        self.init_name = name.into();
        self
    }

    /// Set the Next relation name.
    pub fn next_name(mut self, name: impl Into<String>) -> Self {
        self.next_name = name.into();
        self
    }

    /// Get the configured Init name.
    pub fn get_init_name(&self) -> &str {
        &self.init_name
    }

    /// Get the configured Next name.
    pub fn get_next_name(&self) -> &str {
        &self.next_name
    }
}

impl Default for TraceValidationBuilder {
    fn default() -> Self {
        Self::new()
    }
}
