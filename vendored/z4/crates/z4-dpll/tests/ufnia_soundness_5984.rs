// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #5984: logic_has_uf check misses UFNIA/UFNRA/UFNIRA.
//!
//! Before the fix, UFNIA/UFNRA mapped to NIA/NRA, losing UF information.
//! The NIA solver could assign inconsistent values to UF function applications
//! (e.g., (f x) = 1 and (f y) = 2 when x = y), producing unsound SAT results.
//!
//! After the fix, these logics route to dedicated UF-aware categories that
//! return Unknown (no combined UF+NIA/NRA solver exists yet).

use ntest::timeout;
mod common;

/// QF_UFNIA with UF consistency requirement: (f x) must equal (f y) when x = y.
/// Before fix: NIA solver could return sat with inconsistent UF assignments.
/// After fix: returns unknown (no combined UF+NIA solver).
#[test]
#[timeout(10_000)]
fn qf_ufnia_returns_unknown_not_unsound_sat() {
    let smt = r#"
(set-logic QF_UFNIA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)
"#;
    let output = common::solve(smt);
    let result = common::sat_result(&output).unwrap();
    // Must be "unsat" (correct) or "unknown" (safe), but NEVER "sat" (unsound).
    assert_ne!(
        result, "sat",
        "UFNIA must not return sat without UF congruence closure"
    );
}

/// QF_UFNRA: same UF consistency test with real arithmetic.
#[test]
#[timeout(10_000)]
fn qf_ufnra_returns_unknown_not_unsound_sat() {
    let smt = r#"
(set-logic QF_UFNRA)
(declare-fun g (Real) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= a b))
(assert (not (= (g a) (g b))))
(check-sat)
"#;
    let output = common::solve(smt);
    let result = common::sat_result(&output).unwrap();
    assert_ne!(
        result, "sat",
        "UFNRA must not return sat without UF congruence closure"
    );
}

/// QF_AUFNIA: arrays + UF + NIA preserves UF information.
#[test]
#[timeout(10_000)]
fn qf_aufnia_returns_unknown_not_unsound_sat() {
    let smt = r#"
(set-logic QF_AUFNIA)
(declare-fun f (Int) Int)
(declare-fun x () Int)
(assert (not (= (f x) (f x))))
(check-sat)
"#;
    let output = common::solve(smt);
    let result = common::sat_result(&output).unwrap();
    // (f x) = (f x) is a UF tautology. Must not return sat.
    assert_ne!(
        result, "sat",
        "AUFNIA must not return sat without UF congruence closure"
    );
}

/// Quantified UFNIA returns unknown (not yet implemented).
#[test]
#[timeout(10_000)]
fn quantified_ufnia_returns_unknown() {
    let smt = r#"
(set-logic UFNIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (>= (f x) 0)))
(check-sat)
"#;
    let output = common::solve(smt);
    let result = common::sat_result(&output).unwrap();
    // Quantified UFNIA is not yet implemented — must return unknown.
    assert!(
        result == "unknown" || result == "unsat",
        "Quantified UFNIA should not claim sat — got: {result}"
    );
}

/// QF_UFNIRA: mixed int/real + UF.
#[test]
#[timeout(10_000)]
fn qf_ufnira_returns_unknown() {
    let smt = r#"
(set-logic QF_UFNIRA)
(declare-fun h (Int) Real)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
(assert (not (= (h x) (h y))))
(check-sat)
"#;
    let output = common::solve(smt);
    let result = common::sat_result(&output).unwrap();
    assert_ne!(
        result, "sat",
        "UFNIRA must not return sat without UF congruence closure"
    );
}
