// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! EvalError convenience constructors that depend on Value.
//!
//! These methods are defined here (in the value module) rather than in error.rs
//! to break the error->value circular dependency. This enables EvalError to
//! eventually move to tla-core without dragging in Value.
//!
//! Part of #1269 Phase 2: break the error<->value cycle.

use super::Value;
use crate::error::EvalError;
use tla_core::Span;

impl EvalError {
    pub fn type_error(expected: &'static str, got: &Value, span: Option<Span>) -> Self {
        EvalError::TypeError {
            expected,
            got: got.type_name(),
            span,
        }
    }

    /// Create a TLC-compatible single-argument type error (EC.TLC_MODULE_ONE_ARGUMENT_ERROR).
    /// Used by Len, Head, Tail for type errors on their single argument.
    pub fn one_argument_error(
        op: &'static str,
        expected_type: &'static str,
        value: &Value,
        span: Option<Span>,
    ) -> Self {
        EvalError::OneArgumentError {
            op,
            expected_type,
            value_display: format!("{value}"),
            span,
        }
    }

    /// Create a TLC-compatible evaluation form error (EC.TLC_MODULE_EVALUATING).
    /// Used by Append, Cons, Concat for type errors.
    pub fn evaluating_error(
        form: &'static str,
        expected_type: &'static str,
        value: &Value,
        span: Option<Span>,
    ) -> Self {
        EvalError::EvaluatingError {
            form,
            expected_type,
            value_display: format!("{value}"),
            span,
        }
    }

    /// Create a TLC-compatible argument type error (EC.TLC_MODULE_ARGUMENT_ERROR).
    /// Used for arithmetic and multi-argument operations where TLC produces specific formatted messages.
    pub fn argument_error(
        position: &'static str,
        op: &str,
        expected_type: &'static str,
        value: &Value,
        span: Option<Span>,
    ) -> Self {
        EvalError::ArgumentError {
            position,
            op: op.to_string(),
            expected_type,
            value_display: format!("{value}"),
            span,
        }
    }
}
