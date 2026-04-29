// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLC-compatible floor-division `\div` and `%` semantics (Part of #745).

use super::*;

fn int_div(left: Spanned<Expr>, right: Spanned<Expr>) -> Spanned<Expr> {
    spanned(Expr::IntDiv(Box::new(left), Box::new(right)))
}

fn modulo(left: Spanned<Expr>, right: Spanned<Expr>) -> Spanned<Expr> {
    spanned(Expr::Mod(Box::new(left), Box::new(right)))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_div_positive_positive() {
    let mut jit = JitContext::new().unwrap();
    let expr = int_div(num(7), num(3));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 2, "7 \\div 3");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_div_negative_positive() {
    let mut jit = JitContext::new().unwrap();
    let expr = int_div(num(-7), num(3));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), -3, "-7 \\div 3");

    let expr = int_div(num(-1), num(3));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), -1, "-1 \\div 3");

    let expr = int_div(num(-6), num(3));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), -2, "-6 \\div 3");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_div_positive_negative() {
    let mut jit = JitContext::new().unwrap();
    let expr = int_div(num(7), num(-3));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), -3, "7 \\div -3");

    let expr = int_div(num(1), num(-3));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), -1, "1 \\div -3");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_div_negative_negative() {
    let mut jit = JitContext::new().unwrap();
    let expr = int_div(num(-7), num(-3));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 2, "-7 \\div -3");

    let expr = int_div(num(-6), num(-3));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 2, "-6 \\div -3");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_div_by_zero_rejected() {
    let mut jit = JitContext::new().unwrap();
    let expr = int_div(num(5), num(0));
    assert!(
        jit.compile_expr(&expr).is_err(),
        "\\div by zero should be rejected"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mod_positive_positive() {
    let mut jit = JitContext::new().unwrap();
    let expr = modulo(num(7), num(3));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 1, "7 % 3");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mod_negative_positive() {
    let mut jit = JitContext::new().unwrap();
    let expr = modulo(num(-7), num(3));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 2, "-7 % 3");

    let expr = modulo(num(-1), num(3));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 2, "-1 % 3");

    let expr = modulo(num(-6), num(3));
    assert_eq!(jit.compile_expr(&expr).unwrap()(), 0, "-6 % 3");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mod_non_positive_divisor_rejected() {
    let mut jit = JitContext::new().unwrap();
    let expr = modulo(num(7), num(0));
    let err = jit.compile_expr(&expr).unwrap_err();
    assert!(
        matches!(err, JitError::CompileError(msg) if msg.contains("not positive")),
        "% by 0 should fail with 'not positive'"
    );

    let expr = modulo(num(7), num(-3));
    let err = jit.compile_expr(&expr).unwrap_err();
    assert!(
        matches!(err, JitError::CompileError(msg) if msg.contains("not positive")),
        "% by -3 should fail with 'not positive'"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_int_div_matches_floor_div() {
    let mut jit = JitContext::new().unwrap();
    let test_cases: &[(i64, i64)] = &[
        (7, 3),
        (-7, 3),
        (7, -3),
        (-7, -3),
        (10, 4),
        (-10, 4),
        (10, -4),
        (-10, -4),
        (15, 5),
        (-15, 5),
        (15, -5),
        (-15, -5),
        (0, 3),
        (0, -3),
        (1, 1),
        (-1, 1),
        (1, -1),
        (-1, -1),
    ];
    for &(a, b) in test_cases {
        let expr = int_div(num(a), num(b));
        let q = a / b;
        let expected = if (a ^ b) < 0 && a % b != 0 { q - 1 } else { q };
        let actual = jit.compile_expr(&expr).unwrap()();
        assert_eq!(
            actual, expected,
            "{a} \\div {b}: expected {expected}, got {actual}"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mod_matches_rust_rem_euclid() {
    let mut jit = JitContext::new().unwrap();
    let test_cases: &[(i64, i64)] = &[
        (7, 3),
        (-7, 3),
        (10, 4),
        (-10, 4),
        (15, 5),
        (-15, 5),
        (0, 3),
        (1, 1),
        (-1, 1),
        (100, 7),
        (-100, 7),
    ];
    for &(a, b) in test_cases {
        let expr = modulo(num(a), num(b));
        let expected = a.rem_euclid(b);
        let actual = jit.compile_expr(&expr).unwrap()();
        assert_eq!(
            actual, expected,
            "{a} % {b}: expected {expected}, got {actual}"
        );
    }
}
