// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Short-circuit semantics tests (subprocess-backed).

use super::*;
use crate::error::JitError;
use num_bigint::BigInt;
use std::process::Command;
use tla_core::span::Span;

mod boolean_strictness;
mod euclidean_div_mod;

pub(super) fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::new(node, Span::default())
}

pub(super) fn num(n: i64) -> Spanned<Expr> {
    spanned(Expr::Int(BigInt::from(n)))
}

pub(super) fn bool_lit(b: bool) -> Spanned<Expr> {
    spanned(Expr::Bool(b))
}

pub(super) fn add(left: Spanned<Expr>, right: Spanned<Expr>) -> Spanned<Expr> {
    spanned(Expr::Add(Box::new(left), Box::new(right)))
}

pub(super) fn div_by_zero_eq() -> Spanned<Expr> {
    spanned(Expr::Eq(
        Box::new(spanned(Expr::Div(Box::new(num(1)), Box::new(num(0))))),
        Box::new(num(0)),
    ))
}

const SC_CHILD_ENV: &str = "TLA2_JIT_SC_CHILD";

fn is_sc_child() -> bool {
    std::env::var(SC_CHILD_ENV).is_ok() // gate:env-var-ok — test subprocess detection, intentionally uncached
}

fn run_sc_child(test_name: &str) {
    let exe = std::env::current_exe().unwrap();
    let output = Command::new(exe)
        .env(SC_CHILD_ENV, "1")
        .arg(test_name)
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "child process exited with {}.\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let expected = format!("test compiler::tests_semantics::{test_name} ... ok");
    assert!(
        stdout.contains(&expected),
        "child process did not run expected test.\nexpected substring:\n{expected}\nstdout:\n{stdout}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stderr),
    );
}

// Short-circuit assertion helpers

fn assert_short_circuit_or_masks_div_by_zero() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::Or(
        Box::new(bool_lit(true)),
        Box::new(div_by_zero_eq()),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

fn assert_short_circuit_and_masks_div_by_zero() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::And(
        Box::new(bool_lit(false)),
        Box::new(div_by_zero_eq()),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}

fn assert_short_circuit_implies_masks_div_by_zero() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::Implies(
        Box::new(bool_lit(false)),
        Box::new(div_by_zero_eq()),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 1);
}

fn assert_if_true_masks_else_div_by_zero() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::If(
        Box::new(bool_lit(true)),
        Box::new(num(42)),
        Box::new(spanned(Expr::Div(Box::new(num(1)), Box::new(num(0))))),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 42);
}

fn assert_if_false_masks_then_div_by_zero() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::If(
        Box::new(bool_lit(false)),
        Box::new(spanned(Expr::Div(Box::new(num(1)), Box::new(num(0))))),
        Box::new(num(42)),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 42);
}

// =========================================================================
// Short-circuit subprocess tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_short_circuit_or_masks_div_by_zero() {
    if is_sc_child() {
        assert_short_circuit_or_masks_div_by_zero();
    } else {
        run_sc_child("short_circuit_or_masks_div_by_zero_child");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn short_circuit_or_masks_div_by_zero_child() {
    if is_sc_child() {
        assert_short_circuit_or_masks_div_by_zero();
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_short_circuit_and_masks_div_by_zero() {
    if is_sc_child() {
        assert_short_circuit_and_masks_div_by_zero();
    } else {
        run_sc_child("short_circuit_and_masks_div_by_zero_child");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn short_circuit_and_masks_div_by_zero_child() {
    if is_sc_child() {
        assert_short_circuit_and_masks_div_by_zero();
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_short_circuit_implies_masks_div_by_zero() {
    if is_sc_child() {
        assert_short_circuit_implies_masks_div_by_zero();
    } else {
        run_sc_child("short_circuit_implies_masks_div_by_zero_child");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn short_circuit_implies_masks_div_by_zero_child() {
    if is_sc_child() {
        assert_short_circuit_implies_masks_div_by_zero();
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_if_true_masks_else_div_by_zero() {
    if is_sc_child() {
        assert_if_true_masks_else_div_by_zero();
    } else {
        run_sc_child("if_true_masks_else_div_by_zero_child");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn if_true_masks_else_div_by_zero_child() {
    if is_sc_child() {
        assert_if_true_masks_else_div_by_zero();
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_if_false_masks_then_div_by_zero() {
    if is_sc_child() {
        assert_if_false_masks_then_div_by_zero();
    } else {
        run_sc_child("if_false_masks_then_div_by_zero_child");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn if_false_masks_then_div_by_zero_child() {
    if is_sc_child() {
        assert_if_false_masks_then_div_by_zero();
    }
}

// =========================================================================
// Short-circuit masks overflow
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_short_circuit_and_masks_overflow() {
    let mut jit = JitContext::new().unwrap();
    let expr = spanned(Expr::And(
        Box::new(spanned(Expr::Bool(false))),
        Box::new(spanned(Expr::Eq(
            Box::new(add(num(i64::MAX), num(1))),
            Box::new(num(0)),
        ))),
    ));
    let func = jit.compile_expr(&expr).unwrap();
    assert_eq!(func(), 0);
}
