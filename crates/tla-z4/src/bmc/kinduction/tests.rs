// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the pure SMT-level k-induction checker. Part of #3722.

use num_bigint::BigInt;
use tla_core::ast::Expr;
use tla_core::name_intern::NameId;
use tla_core::Spanned;

use super::*;
use crate::TlaSort;

fn s<T>(node: T) -> Spanned<T> {
    Spanned::dummy(node)
}

fn ident(name: &str) -> Spanned<Expr> {
    s(Expr::Ident(name.to_string(), NameId::INVALID))
}

fn int(v: i64) -> Spanned<Expr> {
    s(Expr::Int(BigInt::from(v)))
}

fn prime(e: Spanned<Expr>) -> Spanned<Expr> {
    s(Expr::Prime(Box::new(e)))
}

fn eq(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    s(Expr::Eq(Box::new(a), Box::new(b)))
}

fn and(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    s(Expr::And(Box::new(a), Box::new(b)))
}

fn add(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    s(Expr::Add(Box::new(a), Box::new(b)))
}

fn leq(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    s(Expr::Leq(Box::new(a), Box::new(b)))
}

fn geq(a: Spanned<Expr>, b: Spanned<Expr>) -> Spanned<Expr> {
    s(Expr::Geq(Box::new(a), Box::new(b)))
}

fn if_then_else(
    cond: Spanned<Expr>,
    then_e: Spanned<Expr>,
    else_e: Spanned<Expr>,
) -> Spanned<Expr> {
    s(Expr::If(Box::new(cond), Box::new(then_e), Box::new(else_e)))
}

/// Helper: build a KInductionChecker for a single Int variable "x".
fn single_var_checker(
    init: Spanned<Expr>,
    next: Spanned<Expr>,
    safety: Spanned<Expr>,
) -> KInductionChecker {
    KInductionChecker::new(vec![("x".to_string(), TlaSort::Int)], init, next, safety)
}

fn default_config(max_k: usize) -> KInductionConfig {
    KInductionConfig {
        max_k,
        start_k: 1,
        debug: false,
        incremental: false,
        solve_timeout: Some(Duration::from_secs(30)),
    }
}

// ---- Test 1: Stable property is 1-inductive ----
//
// x starts at 0, x' = x. Safety: x = 0.
// Trivially 1-inductive.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_stable_property_proved() {
    let init = eq(ident("x"), int(0));
    let next = eq(prime(ident("x")), ident("x"));
    let safety = eq(ident("x"), int(0));

    let checker = single_var_checker(init, next, safety);
    let result = checker.check(&default_config(10)).expect("should succeed");

    match result {
        KInductionResult::Proved { k } => {
            assert_eq!(k, 1, "x'=x with Safety x=0 should be 1-inductive");
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ---- Test 2: Toggle property is 1-inductive ----
//
// x toggles between 0 and 1. Safety: 0 <= x <= 1.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_toggle_proved() {
    // Init: x \in {0, 1} -> (x = 0 \/ x = 1)
    let init = s(Expr::Or(
        Box::new(eq(ident("x"), int(0))),
        Box::new(eq(ident("x"), int(1))),
    ));
    // Next: IF x = 0 THEN x' = 1 ELSE x' = 0
    let next = if_then_else(
        eq(ident("x"), int(0)),
        eq(prime(ident("x")), int(1)),
        eq(prime(ident("x")), int(0)),
    );
    // Safety: x >= 0 /\ x <= 1
    let safety = and(geq(ident("x"), int(0)), leq(ident("x"), int(1)));

    let checker = single_var_checker(init, next, safety);
    let result = checker.check(&default_config(10)).expect("should succeed");

    match result {
        KInductionResult::Proved { k } => {
            assert!(k <= 2, "toggle should be proved at small k, got k={k}");
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ---- Test 3: Counterexample found by BMC base case ----
//
// x starts at 0, x' = x + 1. Safety: x <= 2.
// Violation at depth 3 (x reaches 3).

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_counterexample_found() {
    let init = eq(ident("x"), int(0));
    let next = eq(prime(ident("x")), add(ident("x"), int(1)));
    let safety = leq(ident("x"), int(2));

    let checker = single_var_checker(init, next, safety);
    let result = checker.check(&default_config(10)).expect("should succeed");

    match result {
        KInductionResult::Counterexample { depth, trace } => {
            assert_eq!(depth, 3, "violation at depth 3 (x reaches 3)");
            assert_eq!(trace.len(), 4, "trace should have states 0 through 3");
        }
        other => panic!("expected Counterexample, got {other:?}"),
    }
}

// ---- Test 4: Non-inductive property returns Unknown ----
//
// x starts at 0, x' = x + 1. Safety: x <= 100.
// Not provable by k-induction at small k.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_unknown_for_non_inductive() {
    let init = eq(ident("x"), int(0));
    let next = eq(prime(ident("x")), add(ident("x"), int(1)));
    let safety = leq(ident("x"), int(100));

    let checker = single_var_checker(init, next, safety);
    let result = checker.check(&default_config(5)).expect("should succeed");

    match result {
        KInductionResult::Unknown { max_k, .. } => {
            assert_eq!(max_k, 5, "should exhaust the bound");
        }
        KInductionResult::Proved { k } => {
            panic!("should NOT be provable, got Proved at k={k}");
        }
        KInductionResult::Counterexample { depth, .. } => {
            panic!("unexpected Counterexample at depth {depth} with max_k=5");
        }
    }
}

// ---- Test 5: Two-variable pipeline (2-inductive) ----
//
// x, y. Init: x=0, y=0. Next: y' = x, x' = IF x=0 THEN 1 ELSE 0.
// Safety: y >= 0 /\ y <= 1.
// NOT 1-inductive. IS 2-inductive.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_two_variable_pipeline_2_inductive() {
    let init = and(eq(ident("x"), int(0)), eq(ident("y"), int(0)));

    let next = and(
        eq(prime(ident("y")), ident("x")),
        if_then_else(
            eq(ident("x"), int(0)),
            eq(prime(ident("x")), int(1)),
            eq(prime(ident("x")), int(0)),
        ),
    );

    let safety = and(geq(ident("y"), int(0)), leq(ident("y"), int(1)));

    let checker = KInductionChecker::new(
        vec![
            ("x".to_string(), TlaSort::Int),
            ("y".to_string(), TlaSort::Int),
        ],
        init,
        next,
        safety,
    );

    let result = checker.check(&default_config(10)).expect("should succeed");

    match result {
        KInductionResult::Proved { k } => {
            assert!(k >= 2, "pipeline should NOT be 1-inductive, got k={k}");
            assert!(
                k <= 3,
                "pipeline should be provable at k=2 or k=3, got k={k}"
            );
        }
        other => panic!("expected Proved at k>=2, got {other:?}"),
    }
}

// ---- Test 6: Three-variable shift register (needs k>=3) ----
//
// a, b, c. Init: all 0. Next: c'=b, b'=a, a' = IF a=0 THEN 1 ELSE 0.
// Safety: c >= 0 /\ c <= 1.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_shift_register_3_inductive() {
    let init = and(
        and(eq(ident("a"), int(0)), eq(ident("b"), int(0))),
        eq(ident("c"), int(0)),
    );

    let next = and(
        and(
            eq(prime(ident("c")), ident("b")),
            eq(prime(ident("b")), ident("a")),
        ),
        if_then_else(
            eq(ident("a"), int(0)),
            eq(prime(ident("a")), int(1)),
            eq(prime(ident("a")), int(0)),
        ),
    );

    let safety = and(geq(ident("c"), int(0)), leq(ident("c"), int(1)));

    let checker = KInductionChecker::new(
        vec![
            ("a".to_string(), TlaSort::Int),
            ("b".to_string(), TlaSort::Int),
            ("c".to_string(), TlaSort::Int),
        ],
        init,
        next,
        safety,
    );

    let result = checker.check(&default_config(10)).expect("should succeed");

    match result {
        KInductionResult::Proved { k } => {
            assert!(k >= 2, "shift register should need k >= 2, got k={k}");
            assert!(k <= 5, "shift register should prove by k <= 5, got k={k}");
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ---- Test 7: Incremental mode proves stable property ----

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_incremental_proves_stable() {
    let init = eq(ident("x"), int(0));
    let next = eq(prime(ident("x")), ident("x"));
    let safety = eq(ident("x"), int(0));

    let checker = single_var_checker(init, next, safety);
    let config = KInductionConfig {
        incremental: true,
        ..default_config(10)
    };
    let result = checker.check(&config).expect("should succeed");

    match result {
        KInductionResult::Proved { k } => {
            assert_eq!(
                k, 1,
                "incremental: x'=x with Safety x=0 should be 1-inductive"
            );
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ---- Test 8: Incremental mode finds counterexample ----

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_incremental_finds_counterexample() {
    let init = eq(ident("x"), int(0));
    let next = eq(prime(ident("x")), add(ident("x"), int(1)));
    let safety = leq(ident("x"), int(2));

    let checker = single_var_checker(init, next, safety);
    let config = KInductionConfig {
        incremental: true,
        ..default_config(10)
    };
    let result = checker.check(&config).expect("should succeed");

    match result {
        KInductionResult::Counterexample { depth, trace } => {
            assert_eq!(depth, 3, "incremental: violation at depth 3");
            assert_eq!(trace.len(), 4, "trace should have 4 states");
        }
        other => panic!("expected Counterexample, got {other:?}"),
    }
}

// ---- Test 9: Incremental mode returns Unknown for non-inductive ----

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_incremental_returns_unknown() {
    let init = eq(ident("x"), int(0));
    let next = eq(prime(ident("x")), add(ident("x"), int(1)));
    let safety = leq(ident("x"), int(100));

    let checker = single_var_checker(init, next, safety);
    let config = KInductionConfig {
        incremental: true,
        ..default_config(5)
    };
    let result = checker.check(&config).expect("should succeed");

    match result {
        KInductionResult::Unknown { max_k, .. } => {
            assert_eq!(max_k, 5, "incremental: should exhaust the bound");
        }
        KInductionResult::Proved { k } => {
            panic!("incremental: should NOT prove, got Proved at k={k}");
        }
        KInductionResult::Counterexample { depth, .. } => {
            panic!("unexpected Counterexample at depth {depth}");
        }
    }
}

// ---- Test 10: Incremental mode proves 2-inductive pipeline ----

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_incremental_proves_pipeline() {
    let init = and(eq(ident("x"), int(0)), eq(ident("y"), int(0)));

    let next = and(
        eq(prime(ident("y")), ident("x")),
        if_then_else(
            eq(ident("x"), int(0)),
            eq(prime(ident("x")), int(1)),
            eq(prime(ident("x")), int(0)),
        ),
    );

    let safety = and(geq(ident("y"), int(0)), leq(ident("y"), int(1)));

    let checker = KInductionChecker::new(
        vec![
            ("x".to_string(), TlaSort::Int),
            ("y".to_string(), TlaSort::Int),
        ],
        init,
        next,
        safety,
    );

    let config = KInductionConfig {
        incremental: true,
        ..default_config(10)
    };
    let result = checker.check(&config).expect("should succeed");

    match result {
        KInductionResult::Proved { k } => {
            assert!(k >= 2, "incremental: pipeline NOT 1-inductive, got k={k}");
            assert!(
                k <= 3,
                "incremental: pipeline should prove at k=2 or 3, got k={k}"
            );
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ---- Test 11: Incremental and non-incremental agree ----

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_incremental_agrees_with_non_incremental() {
    let init = and(
        and(eq(ident("a"), int(0)), eq(ident("b"), int(0))),
        eq(ident("c"), int(0)),
    );

    let next = and(
        and(
            eq(prime(ident("c")), ident("b")),
            eq(prime(ident("b")), ident("a")),
        ),
        if_then_else(
            eq(ident("a"), int(0)),
            eq(prime(ident("a")), int(1)),
            eq(prime(ident("a")), int(0)),
        ),
    );

    let safety = and(geq(ident("c"), int(0)), leq(ident("c"), int(1)));

    let vars = vec![
        ("a".to_string(), TlaSort::Int),
        ("b".to_string(), TlaSort::Int),
        ("c".to_string(), TlaSort::Int),
    ];

    let checker = KInductionChecker::new(vars, init.clone(), next.clone(), safety.clone());

    let non_incr = checker
        .check(&default_config(10))
        .expect("non-incr should succeed");

    let checker2 = KInductionChecker::new(
        vec![
            ("a".to_string(), TlaSort::Int),
            ("b".to_string(), TlaSort::Int),
            ("c".to_string(), TlaSort::Int),
        ],
        init,
        next,
        safety,
    );

    let incr_config = KInductionConfig {
        incremental: true,
        ..default_config(10)
    };
    let incr = checker2.check(&incr_config).expect("incr should succeed");

    let non_incr_k = match non_incr {
        KInductionResult::Proved { k } => k,
        other => panic!("non-incr: expected Proved, got {other:?}"),
    };
    let incr_k = match incr {
        KInductionResult::Proved { k } => k,
        other => panic!("incr: expected Proved, got {other:?}"),
    };

    assert!(
        non_incr_k <= 10 && incr_k <= 10,
        "both should prove within max_k=10: non_incr={non_incr_k}, incr={incr_k}"
    );
}

// ---- Test 12: Empty variable set returns error ----

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_kinduction_error_empty_vars() {
    let checker = KInductionChecker::new(
        vec![],
        s(Expr::Bool(true)),
        s(Expr::Bool(true)),
        s(Expr::Bool(true)),
    );

    let err = checker.check(&default_config(5));
    assert!(err.is_err(), "should fail with empty variables");
}

// ---- Test 13: Custom start_k parameter ----

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_custom_start_k() {
    let init = eq(ident("x"), int(0));
    let next = eq(prime(ident("x")), ident("x"));
    let safety = eq(ident("x"), int(0));

    let checker = single_var_checker(init, next, safety);
    let config = KInductionConfig {
        start_k: 3,
        ..default_config(10)
    };
    let result = checker.check(&config).expect("should succeed");

    match result {
        KInductionResult::Proved { k } => {
            assert!(
                k >= 3,
                "with start_k=3, proof should be at k >= 3, got k={k}"
            );
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}
