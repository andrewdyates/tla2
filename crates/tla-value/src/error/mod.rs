// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Evaluation errors for the TLA+ model checker.
//!
//! Value-dependent convenience constructors (type_error, one_argument_error,
//! evaluating_error, argument_error) are defined in `value/error_constructors.rs`
//! to break the error->value circular dependency.
//!
//! Part of #1269 Phase 2: break the error<->value cycle.

use thiserror::Error;
use tla_core::Span;

mod messages;
#[cfg(test)]
mod tests;

use self::messages::{
    _format_argument_error, _format_index_out_of_bounds, _format_no_such_field,
    _format_not_in_domain, _format_one_argument_error,
};

/// Evaluation error
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
pub enum EvalError {
    /// Type mismatch in operation
    #[error("Type error: expected {expected}, got {got}")]
    TypeError {
        expected: &'static str,
        got: &'static str,
        span: Option<Span>,
    },

    /// Division by zero (TLC: EC.TLC_MODULE_DIVISION_BY_ZERO)
    #[error("The second argument of \\div is 0.")]
    DivisionByZero { span: Option<Span> },

    /// Modulus operator requires positive divisor (TLC: EC.TLC_MODULE_ARGUMENT_ERROR)
    #[error("The second argument of % should be a positive number, but instead it is:\n{value}")]
    ModulusNotPositive { value: String, span: Option<Span> },

    /// Undefined variable reference
    #[error("Undefined variable: {name}")]
    UndefinedVar { name: String, span: Option<Span> },

    /// Undefined operator reference
    #[error("Undefined operator: {name}")]
    UndefinedOp { name: String, span: Option<Span> },

    /// Function applied to value not in domain (TLC: FcnRcdValue.java:354)
    /// When func_display is provided, uses TLC-compatible verbose format.
    #[error("{}", _format_not_in_domain(.arg, .func_display))]
    NotInDomain {
        arg: String,
        func_display: Option<String>,
        span: Option<Span>,
    },

    /// Record field not found (TLC: RecordValue.java:488)
    /// With record_display: "Attempted to access nonexistent field '<field>' of record\n<record>"
    /// Without: "Record has no field: <field>"
    #[error("{}", _format_no_such_field(.field, .record_display))]
    NoSuchField {
        field: String,
        record_display: Option<String>,
        span: Option<Span>,
    },

    /// Sequence/tuple index out of bounds (TLC: TupleValue.java:144)
    /// With value_display: "Attempted to access index <N> of tuple\n<tuple>\nwhich is out of bounds."
    /// Without: "Sequence index out of bounds: <index> not in 1..<len>"
    #[error("{}", _format_index_out_of_bounds(.index, .len, .value_display))]
    IndexOutOfBounds {
        index: i64,
        len: usize,
        value_display: Option<String>,
        span: Option<Span>,
    },

    /// TLC-compatible single-argument type error (TLC: EC.TLC_MODULE_ONE_ARGUMENT_ERROR = 2283)
    /// Format: "The argument of <op> should be a <type>, but instead it is:\n<value>"
    /// Used by Len, Head, Tail.
    #[error("{}", _format_one_argument_error(.op, .expected_type, .value_display))]
    OneArgumentError {
        op: &'static str,
        expected_type: &'static str,
        value_display: String,
        span: Option<Span>,
    },

    /// TLC-compatible empty sequence error (TLC: EC.TLC_MODULE_APPLY_EMPTY_SEQ = 2184)
    /// Format: "Attempted to apply <op> to the empty sequence."
    /// Used by Head, Tail.
    #[error("Attempted to apply {op} to the empty sequence.")]
    ApplyEmptySeq {
        op: &'static str,
        span: Option<Span>,
    },

    /// TLC-compatible evaluation form error (TLC: EC.TLC_MODULE_EVALUATING = 2182)
    /// Format: "Evaluating an expression of the form <form> when s is not a <type>:\n<value>"
    /// Used by Append, Cons, Concat.
    #[error("Evaluating an expression of the form {form} when s is not a {expected_type}:\n{value_display}")]
    EvaluatingError {
        form: &'static str,
        expected_type: &'static str,
        value_display: String,
        span: Option<Span>,
    },

    /// CHOOSE found no witness
    #[error("CHOOSE failed: no value satisfies predicate")]
    ChooseFailed { span: Option<Span> },

    /// Arity mismatch in operator application
    #[error("Arity mismatch: {op} expects {expected} arguments, got {got}")]
    ArityMismatch {
        op: String,
        expected: usize,
        got: usize,
        span: Option<Span>,
    },

    /// Set too large to enumerate
    #[error("Set too large to enumerate (infinite or > limit)")]
    SetTooLarge { span: Option<Span> },

    /// TLC-compatible argument type error (TLC: EC.TLC_MODULE_ARGUMENT_ERROR)
    /// Format: "The <position> argument of <op> should be <a/an> <expected>, but instead it is:\n<value>"
    #[error("{}", _format_argument_error(.position, .op, .expected_type, .value_display))]
    ArgumentError {
        position: &'static str,
        op: String,
        expected_type: &'static str,
        value_display: String,
        span: Option<Span>,
    },

    /// Internal evaluation error (bug in evaluator)
    #[error("Internal error: {message}")]
    Internal { message: String, span: Option<Span> },

    /// Unbounded CHOOSE expression (`CHOOSE x : P(x)` without `\in S`).
    ///
    /// Occurs when CHOOSE has no domain set and thus cannot be evaluated
    /// (requires enumerating all possible values). During compile-time
    /// constant evaluation, this is an expected deferral — the expression
    /// simply cannot be evaluated at compile time.
    /// Part of #2861: replaces `Internal { message: "CHOOSE requires bounded quantification" }`.
    #[error("CHOOSE requires bounded quantification")]
    ChooseUnbounded { span: Option<Span> },

    /// Primed variable evaluated outside next-state context.
    ///
    /// Occurs when a guard expression references a primed variable (e.g., `x'`)
    /// but no next-state environment is bound. In guard checking, this indicates
    /// the expression is an action-level construct, not a pure guard.
    /// Part of #1891: replaces string-matched Internal error.
    #[error("Primed variable cannot be evaluated (no next-state context)")]
    PrimedVariableNotBound { span: Option<Span> },

    /// UNCHANGED evaluated outside next-state context.
    ///
    /// Occurs when UNCHANGED is evaluated without a next-state environment.
    /// In guard checking, this indicates an action-level construct.
    /// Part of #1891: replaces string-matched Internal error.
    #[error("UNCHANGED cannot be evaluated (no next-state context)")]
    UnchangedNotEvaluable { span: Option<Span> },

    /// TLC Assert(FALSE, msg) — throws the message string directly.
    /// TLC semantics: the error message IS the second argument, not wrapped.
    /// This enables AssertError(msg, Assert(FALSE, msg)) to return TRUE.
    #[error("{message}")]
    AssertionFailed { message: String, span: Option<Span> },

    /// TLCSet("exit", TRUE) was called - early termination requested
    /// Part of #254: Animation and export specs use this for bounded exploration.
    #[error("Model checking terminated by TLCSet(\"exit\", TRUE)")]
    ExitRequested { span: Option<Span> },

    /// CASE expression: no arm guard evaluated to TRUE and no OTHER clause.
    /// TLC: Assert.fail("Attempted to evaluate a CASE expression, and none of the conditions were true.")
    /// Part of #1425: Previously silently returned Ok(()), masking spec errors.
    #[error("Attempted to evaluate a CASE expression, and none of the conditions were true.")]
    CaseNoMatch { span: Option<Span> },

    /// CASE guard evaluation failed.
    ///
    /// This wrapper preserves the underlying error while preventing disabled-action
    /// fallback paths from incorrectly swallowing fatal CASE guard failures.
    /// Display intentionally mirrors the wrapped source error.
    #[error("{source}")]
    CaseGuardError {
        source: Box<EvalError>,
        span: Option<Span>,
    },
}

impl EvalError {
    // Value-dependent convenience constructors (type_error, one_argument_error,
    // evaluating_error, argument_error) are in value/error_constructors.rs
    // to break the error->value circular dependency (Part of #1269 Phase 2).

    pub fn span(&self) -> Option<Span> {
        match self {
            EvalError::TypeError { span, .. } => *span,
            EvalError::DivisionByZero { span } => *span,
            EvalError::ModulusNotPositive { span, .. } => *span,
            EvalError::UndefinedVar { span, .. } => *span,
            EvalError::UndefinedOp { span, .. } => *span,
            EvalError::NotInDomain { span, .. } => *span,
            EvalError::NoSuchField { span, .. } => *span,
            EvalError::IndexOutOfBounds { span, .. } => *span,
            EvalError::OneArgumentError { span, .. } => *span,
            EvalError::ApplyEmptySeq { span, .. } => *span,
            EvalError::EvaluatingError { span, .. } => *span,
            EvalError::ChooseFailed { span } => *span,
            EvalError::ArityMismatch { span, .. } => *span,
            EvalError::SetTooLarge { span } => *span,
            EvalError::ArgumentError { span, .. } => *span,
            EvalError::Internal { span, .. } => *span,
            EvalError::ChooseUnbounded { span } => *span,
            EvalError::PrimedVariableNotBound { span } => *span,
            EvalError::UnchangedNotEvaluable { span } => *span,
            EvalError::AssertionFailed { span, .. } => *span,
            EvalError::ExitRequested { span } => *span,
            EvalError::CaseNoMatch { span } => *span,
            EvalError::CaseGuardError { span, .. } => *span,
        }
    }
}

pub type EvalResult<T> = Result<T, EvalError>;
