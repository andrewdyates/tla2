// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Decomposed model-checking error types.
//!
//! `CheckError` is split into five domain-specific sub-enums so that match
//! sites can dispatch on category first, then variant.  Each sub-enum uses
//! `thiserror::Error` for consistent `Display` formatting.
//!
//! Part of #2651.

use crate::error::EvalError;
use thiserror::Error;

// ── Config / setup errors ─────────────────────────────────────────────

/// Errors arising from configuration validation or spec setup.
///
/// These are caught before state exploration begins.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum ConfigCheckError {
    /// Model checker setup error (e.g., caller did not provide required loaded modules).
    #[error("Setup error: {0}")]
    Setup(String),
    /// Missing Init definition
    #[error("Missing INIT definition")]
    MissingInit,
    /// Missing Next definition
    #[error("Missing NEXT definition")]
    MissingNext,
    /// Missing invariant definition
    #[error("Missing invariant: {0}")]
    MissingInvariant(String),
    /// Missing property definition
    #[error("Missing property: {0}")]
    MissingProperty(String),
    /// Config operator has wrong arity (TLC: TLC_CONFIG_ID_REQUIRES_NO_ARG).
    ///
    /// Part of #2573: TLC rejects operators with parameters when used as
    /// INVARIANT, PROPERTY, CONSTRAINT, ACTION_CONSTRAINT, INIT, or NEXT.
    #[error("{kind} {op_name} requires no arguments, but has arity {arity}")]
    OpRequiresNoArgs {
        /// Name of the operator.
        op_name: String,
        /// Config element kind (e.g., "INVARIANT", "NEXT").
        kind: String,
        /// Actual arity.
        arity: usize,
    },
    /// Invariant uses primed variables or temporal operators (TLC: TLC_INVARIANT_VIOLATED_LEVEL).
    ///
    /// Part of #2573: TLC rejects invariants at action-level (Prime) or temporal-level
    /// (Always, Eventually, etc.) because they cannot be correctly evaluated in a
    /// single-state context. This prevents silent wrong results.
    #[error("{}", _format_invariant_not_state_level(.name, .has_prime, .has_temporal))]
    InvariantNotStateLevel {
        /// Name of the invariant.
        name: String,
        /// Whether the issue is primed variables.
        has_prime: bool,
        /// Whether the issue is temporal operators.
        has_temporal: bool,
    },
    /// No variables in spec
    #[error("Specification has no variables")]
    NoVariables,
    /// Init predicate contains expressions that cannot be enumerated
    #[error("Cannot enumerate Init: {0}")]
    InitCannotEnumerate(String),
    /// SPECIFICATION directive error
    #[error("SPECIFICATION error: {0}")]
    Specification(String),
    /// TLC configuration error that requires access to the loaded module set
    #[error("CONFIG error: {0}")]
    Config(String),
}

/// Format `InvariantNotStateLevel` Display — conditional reason from prime/temporal flags.
fn _format_invariant_not_state_level(name: &str, has_prime: &bool, has_temporal: &bool) -> String {
    let reason = match (*has_prime, *has_temporal) {
        (true, true) => "primed variables and temporal operators",
        (true, false) => "primed variables",
        (false, _) => "temporal operators",
    };
    format!("Invariant {name} is not a state predicate: contains {reason}")
}

// ── Evaluation errors ─────────────────────────────────────────────────

/// Errors arising during expression evaluation.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum EvalCheckError {
    /// Evaluation error
    #[error("Evaluation error: {0}")]
    Eval(#[from] EvalError),
    /// Init predicate didn't return boolean
    #[error("Init predicate must return boolean")]
    InitNotBoolean,
    /// Next relation didn't return boolean
    #[error("Next relation must return boolean")]
    NextNotBoolean,
    /// Invariant didn't return boolean
    #[error("Invariant {0} must return boolean")]
    InvariantNotBoolean(String),
    /// CONSTRAINT/ACTION_CONSTRAINT didn't return boolean
    #[error("Constraint {0} must return boolean")]
    ConstraintNotBoolean(String),
    /// Property didn't return boolean
    #[error("Property {0} must return boolean")]
    PropertyNotBoolean(String),
}

// ── Liveness errors ───────────────────────────────────────────────────

/// Errors specific to liveness / temporal property checking.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum LivenessCheckError {
    /// Liveness checking error (incomplete or generic).
    ///
    /// Used when liveness checking could not complete due to expected limitations
    /// (e.g., unsupported formula patterns, exploration limits). For internal runtime
    /// failures during liveness checking, see `RuntimeFailure`.
    #[error("Liveness error: {0}")]
    Generic(String),
    /// Internal runtime failure during liveness checking.
    ///
    /// Part of #2156: Distinct from `Generic` (expected incompleteness) and
    /// `CheckResult::LivenessViolation` (counterexample found). This variant covers
    /// tool/runtime faults: evaluation errors, Tarjan SCC invariant violations,
    /// SCC constraint check failures, and counterexample construction failures.
    ///
    /// TLC treats these as system/general errors that terminate the checker, separate
    /// from both violation results and "cannot handle formula" incompleteness.
    #[error("Liveness failure: {0}")]
    RuntimeFailure(String),
    /// TLC liveness formula tautology error (EC 2253).
    ///
    /// Reported when a temporal property's negation produces zero liveness checkers,
    /// meaning the property is a tautology (e.g., `<>TRUE`). TLC rejects
    /// these with TLC_LIVE_FORMULA_TAUTOLOGY before state exploration begins.
    #[error("Temporal property '{property}' is a tautology")]
    FormulaTautology {
        /// Name of the property that is tautological.
        property: String,
    },
    // Part of #3223: TooManyTags variant removed. The >63-tag case is handled
    // gracefully by inline_fairness.rs (warns + falls back to evaluator-backed
    // liveness checking) rather than as a hard error.
    /// TLC liveness conversion failure: "cannot handle the temporal formula" (EC 2213).
    ///
    /// This is reported when liveness conversion needs to enumerate bounded-quantifier contexts
    /// for a temporal-level formula but cannot (e.g., non-enumerable domains).
    #[error("{}", _format_tlc_live_cannot_handle(.location, .reason))]
    CannotHandleFormula {
        /// TLC-shaped location string (e.g., "bytes 0-0 of module Foo").
        location: String,
        /// Optional explanation printed on a new line.
        reason: Option<String>,
    },
}

/// Format `CannotHandleFormula` Display — delegates to `TlcLiveCannotHandleFormulaMsg`.
fn _format_tlc_live_cannot_handle(location: &str, reason: &Option<String>) -> String {
    format!(
        "{}",
        crate::check::TlcLiveCannotHandleFormulaMsg {
            location,
            reason: reason.as_deref(),
        }
    )
}

// ── Infrastructure errors ─────────────────────────────────────────────

/// Errors from the model-checking infrastructure (storage, threading).
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum InfraCheckError {
    /// Fingerprint storage overflow - some states were dropped.
    ///
    /// TLC treats fingerprint loss as fatal (Assert.fail → System.exit).
    /// We match that: BFS stops immediately and reports this error.
    #[error("{}", _format_fp_storage_overflow(.dropped, .detail))]
    FingerprintOverflow {
        /// Number of fingerprints that were dropped.
        dropped: usize,
        /// Backend-specific diagnostic detail (from `StorageFault`).
        detail: String,
    },
    /// A parallel worker thread panicked while model checking.
    #[error("Worker thread {worker_id} panicked: {message}")]
    WorkerThreadPanicked {
        /// Zero-based worker index.
        worker_id: usize,
        /// Best-effort panic payload rendering.
        message: String,
    },
    /// The parallel progress reporting thread panicked.
    #[error("Progress thread panicked: {message}")]
    ProgressThreadPanicked {
        /// Best-effort panic payload rendering.
        message: String,
    },
}

/// Format `FingerprintOverflow` Display — conditional detail suffix.
fn _format_fp_storage_overflow(dropped: &usize, detail: &str) -> String {
    let base = format!(
        "Fingerprint storage overflow: {dropped} states were dropped. \
         Results may be incomplete. Increase --mmap-fingerprints capacity."
    );
    if detail.is_empty() {
        base
    } else {
        format!("{base} Detail: {detail}")
    }
}

// ── Runtime errors ────────────────────────────────────────────────────

/// Runtime errors during state exploration (not config, not eval type-mismatch).
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum RuntimeCheckError {
    /// ASSUME statement evaluated to FALSE
    #[error("Assumption {location} is false.")]
    AssumeFalse {
        /// Location information for the assumption (formatted like "bytes 123-456 of module M").
        location: String,
    },
    /// POSTCONDITION evaluated to FALSE after model checking completed.
    #[error("Postcondition {operator} is false.")]
    PostconditionFalse {
        /// Name of the postcondition operator.
        operator: String,
    },
    /// VIEW evaluation error — TLC treats as fatal, no fallback to full-state fingerprint.
    #[error("VIEW {view_name} evaluation error: {eval_error}")]
    ViewEvalError {
        /// Name of the VIEW operator.
        view_name: String,
        /// The underlying evaluation error.
        eval_error: EvalError,
    },
    /// Internal invariant violation — indicates a bug in the model checker, not user error.
    #[error("Internal error (bug): {0}")]
    Internal(String),
}

// ── Top-level CheckError ──────────────────────────────────────────────

/// An error during model checking, categorised into five domains.
///
/// Part of #2651: decomposed from 28 flat variants into category sub-enums.
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum CheckError {
    /// Configuration / setup error (caught before exploration).
    #[error(transparent)]
    Config(#[from] ConfigCheckError),
    /// Expression evaluation error.
    #[error(transparent)]
    Eval(#[from] EvalCheckError),
    /// Liveness / temporal property error.
    #[error(transparent)]
    Liveness(#[from] LivenessCheckError),
    /// Infrastructure error (storage, threading).
    #[error(transparent)]
    Infra(#[from] InfraCheckError),
    /// Runtime error (ASSUME, POSTCONDITION, VIEW, internal bug).
    #[error(transparent)]
    Runtime(#[from] RuntimeCheckError),
}

// Convenience: allow `EvalError` to convert directly to `CheckError` via `?`.
impl From<EvalError> for CheckError {
    fn from(e: EvalError) -> Self {
        Self::Eval(EvalCheckError::Eval(e))
    }
}
