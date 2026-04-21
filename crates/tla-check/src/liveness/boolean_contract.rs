// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared boolean contract for liveness evaluation.
//!
//! All boolean-required positions in liveness checking (StatePred, ActionPred,
//! ENABLED, Not, And, Or) must enforce consistent non-boolean handling.
//!
//! TLC baseline behavior is strict:
//! - `LNStateAST.eval`: non-boolean → `Assert.fail(EC.TLC_LIVE_STATE_PREDICATE_NON_BOOL)`
//! - `LNAction.eval`: non-boolean → `Assert.fail(EC.TLC_LIVE_ENCOUNTERED_NONBOOL_PREDICATE)`
//!
//! This module provides a single shared helper that both `checker/eval.rs` and
//! `consistency.rs` use to enforce this contract, preventing semantic drift.

use crate::error::{EvalError, EvalResult};
use crate::Value;
use tla_core::Span;

/// Extract a boolean from a liveness evaluation result, or return a TypeError.
///
/// This is the shared contract for all boolean-required liveness positions:
/// StatePred, ActionPred, ENABLED results, Not/And/Or operands.
///
/// # Arguments
/// * `value` - The evaluation result to check
/// * `span` - Source span for error reporting (from the AST expression)
///
/// # Returns
/// * `Ok(bool)` if the value is `Value::Bool(_)`
/// * `Err(EvalError::TypeError)` if the value is not boolean
pub fn expect_live_bool(value: &Value, span: Option<Span>) -> EvalResult<bool> {
    match value {
        Value::Bool(b) => Ok(*b),
        other => Err(EvalError::TypeError {
            expected: "BOOLEAN",
            got: other.type_name(),
            span,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Value;
    use tla_core::{FileId, Span};

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_expect_live_bool_true() {
        assert!(expect_live_bool(&Value::Bool(true), None).unwrap());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_expect_live_bool_false() {
        assert!(!expect_live_bool(&Value::Bool(false), None).unwrap());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_expect_live_bool_integer_returns_type_error() {
        let result = expect_live_bool(&Value::int(42), None);
        assert!(result.is_err());
        match result.unwrap_err() {
            EvalError::TypeError { expected, got, .. } => {
                assert_eq!(expected, "BOOLEAN");
                assert_eq!(got, "Int");
            }
            other => panic!("expected TypeError, got {:?}", other),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_expect_live_bool_string_returns_type_error() {
        let result = expect_live_bool(&Value::string("hello"), None);
        assert!(result.is_err());
        match result.unwrap_err() {
            EvalError::TypeError { expected, got, .. } => {
                assert_eq!(expected, "BOOLEAN");
                assert_eq!(got, "STRING");
            }
            other => panic!("expected TypeError, got {:?}", other),
        }
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_expect_live_bool_preserves_span() {
        let span = Span::new(FileId(0), 10, 20);
        let result = expect_live_bool(&Value::int(1), Some(span));
        match result.unwrap_err() {
            EvalError::TypeError { span: s, .. } => {
                assert_eq!(s, Some(span));
            }
            other => panic!("expected TypeError, got {:?}", other),
        }
    }
}
