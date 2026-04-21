// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Error policy API for model checker evaluation.
//!
//! Centralizes the contract for when eval failures are fatal vs. when
//! speculative fallback is permitted. Replaces ad-hoc `if let Ok(...)`,
//! `unwrap_or(false)`, and `Err(_) => continue` patterns with a single
//! approved API that uses a closed `FallbackClass` enum.
//!
//! # Design rationale
//!
//! TLC treats evaluation errors as fatal unless structurally decomposed
//! (e.g., `getPrimedVar` is a compile-time check, not error recovery).
//! TLA2 uses `eval()` more broadly, creating sites where error-swallowing
//! masks real bugs. This module forces callers to declare *which class*
//! of failure they expect, making catch-all patterns impossible.
//!
//! Part of #1433: systematic error-swallowing audit.

// Currently used: eval_speculative, FallbackClass (in action_resolve.rs).
// Removed unused functions (eval_required, eval_bool_required, eval_bool_speculative)
// — recoverable from git history when #1433 wires them into callsites.

use crate::check::CheckError;
use crate::eval::{eval_entry, EvalCtx};
use crate::EvalCheckError;
use tla_core::ast::Expr;
use tla_core::Spanned;
use tla_value::error::EvalError;
use tla_value::Value;

/// Closed set of eval failure classes where fallback behavior is architecturally
/// legitimate. Each variant documents *why* the fallback is safe.
///
/// Using a closed enum prevents catch-all `Err(_) =>` patterns. Callers must
/// name the specific failure mode they expect.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FallbackClass {
    /// Primed variable not yet bound during constraint enumeration.
    ///
    /// TLC handles this structurally via `getPrimedVar` (pattern matching,
    /// not error recovery). In TLA2, the evaluator may encounter an unbound
    /// primed variable before the enumeration pipeline has assigned it.
    /// This is the *only* legitimate deferral class in the enumeration pipeline.
    #[allow(dead_code)] // Part of #1433: matched in error_matches_class, constructed in tests
    PrimedVarNotYetBound,

    /// Config constant evaluation during liveness constant-folding.
    ///
    /// Constants may depend on state variables — eval failure means
    /// "not a compile-time constant, keep as symbolic expression."
    /// Used in liveness action_resolve.rs for config constant inlining.
    ConstantResolution,

    /// UNCHANGED evaluated outside next-state context.
    ///
    /// During liveness compilation or guard analysis, UNCHANGED may appear
    /// in expressions that are being analyzed structurally rather than
    /// evaluated in a concrete state pair.
    #[allow(dead_code)] // Part of #1433: matched in error_matches_class, constructed in tests
    UnchangedOutsideNextState,

    /// Undefined variable/operator during speculative resolution.
    ///
    /// During multi-candidate resolution (e.g., SPECIFICATION directive
    /// resolution), trying a candidate that references an undefined name
    /// is expected — the caller tries the next candidate.
    #[allow(dead_code)] // Part of #1433: matched in error_matches_class, constructed in tests
    UndefinedName,
}

/// Returns `true` if the given `EvalError` is covered by the specified
/// fallback class.
fn error_matches_class(err: &EvalError, class: FallbackClass) -> bool {
    match class {
        FallbackClass::PrimedVarNotYetBound => {
            matches!(err, EvalError::PrimedVariableNotBound { .. })
        }
        FallbackClass::ConstantResolution => matches!(
            err,
            EvalError::UndefinedVar { .. }
                | EvalError::UndefinedOp { .. }
                | EvalError::PrimedVariableNotBound { .. }
        ),
        FallbackClass::UnchangedOutsideNextState => {
            matches!(err, EvalError::UnchangedNotEvaluable { .. })
        }
        FallbackClass::UndefinedName => {
            matches!(
                err,
                EvalError::UndefinedVar { .. } | EvalError::UndefinedOp { .. }
            )
        }
    }
}

/// Returns `true` if the error matches any of the allowed fallback classes.
fn error_matches_any(err: &EvalError, allowed: &[FallbackClass]) -> bool {
    allowed.iter().any(|class| error_matches_class(err, *class))
}

/// Evaluate speculatively — only *specific* failure classes trigger fallback.
///
/// Returns:
/// - `Ok(Some(value))` — evaluation succeeded
/// - `Ok(None)` — evaluation failed with an error matching one of the
///   `allowed` fallback classes (fallback is safe)
/// - `Err(CheckError)` — evaluation failed with an error NOT in `allowed`
///   (caller must propagate)
///
/// The `allowed` parameter is a slice of `FallbackClass` variants. Using
/// an empty slice makes this equivalent to `eval_required`.
///
/// Replaces patterns like:
/// ```text
/// if let Ok(value) = eval_entry(ctx, expr) {
///     // use value
/// }
/// // silently ignore ALL errors
/// ```
pub(crate) fn eval_speculative(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    allowed: &[FallbackClass],
) -> Result<Option<Value>, CheckError> {
    match eval_entry(ctx, expr) {
        Ok(val) => Ok(Some(val)),
        Err(e) if error_matches_any(&e, allowed) => Ok(None),
        Err(e) => Err(EvalCheckError::Eval(e).into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: construct common test error values.
    fn test_errors() -> (
        EvalError,
        EvalError,
        EvalError,
        EvalError,
        EvalError,
        EvalError,
    ) {
        (
            EvalError::PrimedVariableNotBound { span: None },
            EvalError::UnchangedNotEvaluable { span: None },
            EvalError::UndefinedVar {
                name: "x".into(),
                span: None,
            },
            EvalError::UndefinedOp {
                name: "Op".into(),
                span: None,
            },
            EvalError::TypeError {
                expected: "BOOLEAN",
                got: "INTEGER",
                span: None,
            },
            EvalError::DivisionByZero { span: None },
        )
    }

    #[test]
    fn test_primed_var_class_matching() {
        let (primed, unchanged, undef_var, _, type_err, _) = test_errors();
        assert!(error_matches_class(
            &primed,
            FallbackClass::PrimedVarNotYetBound
        ));
        assert!(!error_matches_class(
            &unchanged,
            FallbackClass::PrimedVarNotYetBound
        ));
        assert!(!error_matches_class(
            &undef_var,
            FallbackClass::PrimedVarNotYetBound
        ));
        assert!(!error_matches_class(
            &type_err,
            FallbackClass::PrimedVarNotYetBound
        ));
    }

    #[test]
    fn test_constant_resolution_class_matching() {
        let (primed, _, undef_var, undef_op, type_err, div_zero) = test_errors();
        assert!(error_matches_class(
            &primed,
            FallbackClass::ConstantResolution
        ));
        assert!(error_matches_class(
            &undef_var,
            FallbackClass::ConstantResolution
        ));
        assert!(error_matches_class(
            &undef_op,
            FallbackClass::ConstantResolution
        ));
        assert!(!error_matches_class(
            &type_err,
            FallbackClass::ConstantResolution
        ));
        assert!(!error_matches_class(
            &div_zero,
            FallbackClass::ConstantResolution
        ));
    }

    #[test]
    fn test_unchanged_and_undefined_class_matching() {
        let (primed, unchanged, undef_var, undef_op, type_err, _) = test_errors();
        // UnchangedOutsideNextState: matches only UnchangedNotEvaluable
        assert!(error_matches_class(
            &unchanged,
            FallbackClass::UnchangedOutsideNextState
        ));
        assert!(!error_matches_class(
            &primed,
            FallbackClass::UnchangedOutsideNextState
        ));
        assert!(!error_matches_class(
            &undef_var,
            FallbackClass::UnchangedOutsideNextState
        ));
        // UndefinedName: matches UndefinedVar and UndefinedOp
        assert!(error_matches_class(
            &undef_var,
            FallbackClass::UndefinedName
        ));
        assert!(error_matches_class(&undef_op, FallbackClass::UndefinedName));
        assert!(!error_matches_class(&primed, FallbackClass::UndefinedName));
        assert!(!error_matches_class(
            &type_err,
            FallbackClass::UndefinedName
        ));
    }

    #[test]
    fn test_error_matches_any() {
        let (primed, _, _, _, type_err, _) = test_errors();
        // Empty allowed list: nothing matches
        assert!(!error_matches_any(&primed, &[]));
        assert!(!error_matches_any(&type_err, &[]));
        // Multiple classes: matches if ANY class matches
        let allowed = &[
            FallbackClass::PrimedVarNotYetBound,
            FallbackClass::UnchangedOutsideNextState,
        ];
        assert!(error_matches_any(&primed, allowed));
        assert!(!error_matches_any(&type_err, allowed));
    }

    // ============= End-to-end eval_speculative API tests =============

    use num_bigint::BigInt;
    use tla_core::ast::Expr;

    /// Helper: create a Spanned<Expr> that evaluates to an integer (42).
    fn expr_int() -> Spanned<Expr> {
        Spanned::dummy(Expr::Int(BigInt::from(42)))
    }

    /// Helper: create a Spanned<Expr> that triggers DivisionByZero (1 \div 0).
    fn expr_div_by_zero() -> Spanned<Expr> {
        Spanned::dummy(Expr::IntDiv(
            Box::new(Spanned::dummy(Expr::Int(BigInt::from(1)))),
            Box::new(Spanned::dummy(Expr::Int(BigInt::from(0)))),
        ))
    }

    /// Helper: create a Spanned<Expr> that triggers UndefinedVar.
    fn expr_undefined_var() -> Spanned<Expr> {
        Spanned::dummy(Expr::Ident(
            "nonexistent_variable".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))
    }

    #[test]
    fn test_eval_speculative_rejects_non_enumerated_error() {
        let ctx = EvalCtx::new();
        // DivisionByZero is not in any FallbackClass — must be rejected
        let result = eval_speculative(
            &ctx,
            &expr_div_by_zero(),
            &[FallbackClass::PrimedVarNotYetBound],
        );
        assert!(
            result.is_err(),
            "eval_speculative must reject errors not in allowed classes"
        );
        match result.unwrap_err() {
            CheckError::Eval(EvalCheckError::Eval(EvalError::DivisionByZero { .. })) => {}
            other => panic!("Expected DivisionByZero error, got: {other:?}"),
        }
    }

    #[test]
    fn test_eval_speculative_empty_allowed_rejects_all() {
        let ctx = EvalCtx::new();
        // Empty allowed list: equivalent to eval_required
        let result = eval_speculative(&ctx, &expr_div_by_zero(), &[]);
        assert!(
            result.is_err(),
            "eval_speculative with empty allowed list must reject all errors"
        );
    }

    #[test]
    fn test_eval_speculative_allows_enumerated_class() {
        let ctx = EvalCtx::new();
        // UndefinedVar should be allowed by FallbackClass::UndefinedName
        let result = eval_speculative(&ctx, &expr_undefined_var(), &[FallbackClass::UndefinedName]);
        assert!(
            result.is_ok(),
            "eval_speculative must allow UndefinedVar when UndefinedName is in allowed list"
        );
        assert_eq!(
            result.unwrap(),
            None,
            "Allowed fallback must return Ok(None)"
        );
    }

    #[test]
    fn test_eval_speculative_returns_value_on_success() {
        let ctx = EvalCtx::new();
        let result = eval_speculative(&ctx, &expr_int(), &[FallbackClass::PrimedVarNotYetBound]);
        assert!(result.is_ok());
        // Small integers (fits in i64) are stored as Value::SmallInt
        match result.unwrap() {
            Some(Value::SmallInt(n)) => assert_eq!(n, 42),
            other => panic!("Expected Some(SmallInt(42)), got: {other:?}"),
        }
    }

    #[test]
    fn test_fallback_class_exhaustive_match() {
        // Compile-time exhaustiveness check: if a new FallbackClass variant is
        // added, this match will fail to compile, forcing the author to update
        // this test and decide whether the new class is appropriate.
        let classes = [
            FallbackClass::PrimedVarNotYetBound,
            FallbackClass::ConstantResolution,
            FallbackClass::UnchangedOutsideNextState,
            FallbackClass::UndefinedName,
        ];
        for class in &classes {
            match class {
                FallbackClass::PrimedVarNotYetBound => {}
                FallbackClass::ConstantResolution => {}
                FallbackClass::UnchangedOutsideNextState => {}
                FallbackClass::UndefinedName => {}
            }
        }
        assert_eq!(
            classes.len(),
            4,
            "FallbackClass must have exactly 4 variants"
        );
    }
}
