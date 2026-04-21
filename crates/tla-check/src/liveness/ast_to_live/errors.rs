// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::core::AstToLive;
use crate::eval::EvalError;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;

impl Default for AstToLive {
    fn default() -> Self {
        Self::new()
    }
}

/// Error during AST to LiveExpr conversion
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ConvertError {
    /// Expression evaluated to a non-boolean constant
    NonBooleanConstant(Arc<Spanned<Expr>>),
    /// Unsupported temporal expression
    UnsupportedTemporal(Arc<Spanned<Expr>>),
    /// TLC-style "cannot handle formula" error for cases where conversion attempted a bounded
    /// quantifier expansion but could not enumerate its bound domain (or otherwise enumerate
    /// contexts) and the overall quantified expression is temporal-level.
    CannotHandleFormula {
        original: Arc<Spanned<Expr>>,
        /// Module name used when rendering TLC-shaped location strings.
        ///
        /// This is populated by the conversion callsite when known (e.g., model checking),
        /// and falls back to <code>"&lt;unknown&gt;"</code> when absent (e.g., unit tests that construct
        /// a converter directly).
        location_module_name: Option<Arc<str>>,
        reason: Option<String>,
    },
    /// A bound value was substituted into an expression, but we cannot faithfully
    /// represent that `Value` as a pure AST `Expr`.
    UnsupportedValueReification {
        original: Arc<Spanned<Expr>>,
        ident: String,
        value_variant: &'static str,
    },
    /// A bounded quantifier uses a tuple pattern (e.g., `<<x, y>>`) but the
    /// enumerated element is not a tuple or has the wrong arity.
    BoundTuplePatternMismatch {
        original: Arc<Spanned<Expr>>,
        expected_arity: usize,
        actual_value_variant: &'static str,
        actual_arity: Option<usize>,
    },
    /// Constant-level expression evaluation failed with an error that is NOT
    /// an unbound variable (which would indicate level misclassification).
    /// Fatal eval errors (DivisionByZero, TypeError, etc.) should not be
    /// silently promoted to state predicates.
    EvalFailed {
        original: Arc<Spanned<Expr>>,
        source: EvalError,
    },
}

impl std::fmt::Display for ConvertError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConvertError::NonBooleanConstant(e) => {
                write!(
                    f,
                    "Expected boolean constant in liveness property: {:?}",
                    e.node
                )
            }
            ConvertError::UnsupportedTemporal(e) => {
                write!(
                    f,
                    "Unsupported temporal expression in liveness property: {:?}",
                    e.node
                )
            }
            ConvertError::CannotHandleFormula {
                original,
                location_module_name,
                reason,
            } => {
                let module_name = location_module_name
                    .as_deref()
                    .unwrap_or("<unknown>");
                let location = crate::check::format_span_location(&original.span, module_name);
                write!(
                    f,
                    "{}",
                    crate::check::TlcLiveCannotHandleFormulaMsg {
                        location: &location,
                        reason: reason.as_deref(),
                    }
                )
            }
            ConvertError::UnsupportedValueReification {
                original,
                ident,
                value_variant,
            } => {
                write!(
                    f,
                    "Unsupported value reification in liveness property: cannot substitute '{}' with {} in {:?}",
                    ident, value_variant, original.node
                )
            }
            ConvertError::BoundTuplePatternMismatch {
                original,
                expected_arity,
                actual_value_variant,
                actual_arity,
            } => match actual_arity {
                Some(actual_arity) => write!(
                    f,
                    "Bounded quantifier tuple pattern expects tuple of length {}, got {} of length {} in {:?}",
                    expected_arity, actual_value_variant, actual_arity, original.node
                ),
                None => write!(
                    f,
                    "Bounded quantifier tuple pattern expects tuple of length {}, got {} in {:?}",
                    expected_arity, actual_value_variant, original.node
                ),
            },
            ConvertError::EvalFailed { original, source } => {
                write!(
                    f,
                    "Constant expression evaluation failed in liveness property: {} in {:?}",
                    source, original.node
                )
            }
        }
    }
}

impl std::error::Error for ConvertError {}
