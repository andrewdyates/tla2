// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Boolean strictness and error-precedence tests.

use super::*;

fn assert_bool_int_type_mismatch<T>(res: Result<T, JitError>) {
    assert!(matches!(
        res,
        Err(JitError::TypeMismatch { expected, actual })
            if expected == "boolean" && actual == "integer"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_boolean_strictness_short_circuit_masks_type_errors() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::And(Box::new(bool_lit(false)), Box::new(num(2))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 0);

    let expr = spanned(Expr::Or(Box::new(bool_lit(true)), Box::new(num(2))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 1);

    let expr = spanned(Expr::Implies(Box::new(bool_lit(false)), Box::new(num(2))));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_boolean_strictness_evaluated_non_boolean_errors() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::And(Box::new(bool_lit(true)), Box::new(num(2))));
    assert_bool_int_type_mismatch(jit.compile_expr(&expr));

    let expr = spanned(Expr::Or(Box::new(bool_lit(false)), Box::new(num(2))));
    assert_bool_int_type_mismatch(jit.compile_expr(&expr));

    let expr = spanned(Expr::Implies(Box::new(bool_lit(true)), Box::new(num(2))));
    assert_bool_int_type_mismatch(jit.compile_expr(&expr));

    let expr = spanned(Expr::Not(Box::new(num(2))));
    assert_bool_int_type_mismatch(jit.compile_expr(&expr));

    let expr = spanned(Expr::If(
        Box::new(num(2)),
        Box::new(num(1)),
        Box::new(num(0)),
    ));
    assert_bool_int_type_mismatch(jit.compile_expr(&expr));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_boolean_strictness_evaluated_div_by_zero_errors() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::And(
        Box::new(bool_lit(true)),
        Box::new(div_by_zero_eq()),
    ));
    assert!(matches!(
        jit.compile_expr(&expr),
        Err(JitError::CompileError(msg)) if msg.contains("division by zero")
    ));

    let expr = spanned(Expr::Or(
        Box::new(bool_lit(false)),
        Box::new(div_by_zero_eq()),
    ));
    assert!(matches!(
        jit.compile_expr(&expr),
        Err(JitError::CompileError(msg)) if msg.contains("division by zero")
    ));

    let expr = spanned(Expr::Implies(
        Box::new(bool_lit(true)),
        Box::new(div_by_zero_eq()),
    ));
    assert!(matches!(
        jit.compile_expr(&expr),
        Err(JitError::CompileError(msg)) if msg.contains("division by zero")
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_boolean_strictness_equiv_error_precedence() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::Equiv(Box::new(num(2)), Box::new(div_by_zero_eq())));
    let err = jit.compile_expr(&expr).unwrap_err();
    match err {
        JitError::CompileError(msg) => assert!(
            msg.contains("division by zero"),
            "unexpected CompileError: {msg}"
        ),
        other => panic!("expected CompileError for div-by-zero, got: {other:?}"),
    }
}
