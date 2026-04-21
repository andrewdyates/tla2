// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for `(mod x k)` / `(div x k)` with constant divisor in LIA (#1614).

use ntest::timeout;
mod common;

#[test]
#[timeout(60_000)]
fn test_qf_lia_mod_by_constant_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (mod x 2) 1))
        (check-sat)
    "#;
    assert_eq!(common::solve(smt).trim(), "sat");
}

#[test]
#[timeout(60_000)]
fn test_qf_lia_mod_by_constant_unsat_contradiction() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (mod x 2) 0))
        (assert (= (mod x 2) 1))
        (check-sat)
    "#;
    assert_eq!(common::solve(smt).trim(), "unsat");
}

#[test]
#[timeout(60_000)]
fn test_qf_lia_mod_by_negative_constant_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (mod x (- 2)) 1))
        (check-sat)
    "#;
    assert_eq!(common::solve(smt).trim(), "sat");
}

#[test]
#[timeout(60_000)]
fn test_qf_lia_div_by_constant_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (div x 2) 0))
        (check-sat)
    "#;
    assert_eq!(common::solve(smt).trim(), "sat");
}

#[test]
#[timeout(60_000)]
fn test_qf_lia_div_by_negative_constant_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= (div x (- 2)) 0))
        (check-sat)
    "#;
    assert_eq!(common::solve(smt).trim(), "sat");
}

#[test]
#[timeout(60_000)]
fn test_qf_lia_mod_by_zero_total_semantics_unsat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (not (= (mod x 0) x)))
        (check-sat)
    "#;
    assert_eq!(common::solve(smt).trim(), "unsat");
}

#[test]
#[timeout(60_000)]
fn test_qf_lia_mod_by_constant_check_sat_assuming_sat() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 1))
        (check-sat-assuming ((= (mod x 2) 1)))
    "#;
    assert_eq!(common::solve(smt).trim(), "sat");
}

/// Regression test for #2781: constant folding must use Euclidean division,
/// not Rust's truncation-toward-zero division.
///
/// SMT-LIB defines: a = b * (div a b) + (mod a b), with 0 <= (mod a b) < |b|.
/// Verified against Z3 for all four sign combinations.
#[test]
#[timeout(60_000)]
fn test_qf_lia_constant_folding_euclidean_division_2781() {
    // (div -7 2) = -4 (not -3)
    assert_eq!(
        common::solve("(set-logic QF_LIA)(assert (= (div (- 7) 2) (- 4)))(check-sat)").trim(),
        "sat"
    );

    // (mod -7 2) = 1 (not -1)
    assert_eq!(
        common::solve("(set-logic QF_LIA)(assert (= (mod (- 7) 2) 1))(check-sat)").trim(),
        "sat"
    );

    // (div 7 -2) = -3 (not -4)
    assert_eq!(
        common::solve("(set-logic QF_LIA)(assert (= (div 7 (- 2)) (- 3)))(check-sat)").trim(),
        "sat"
    );

    // (mod 7 -2) = 1 (always non-negative)
    assert_eq!(
        common::solve("(set-logic QF_LIA)(assert (= (mod 7 (- 2)) 1))(check-sat)").trim(),
        "sat"
    );

    // (div -7 -2) = 4 (not 3)
    assert_eq!(
        common::solve("(set-logic QF_LIA)(assert (= (div (- 7) (- 2)) 4))(check-sat)").trim(),
        "sat"
    );

    // (mod -7 -2) = 1 (always non-negative)
    assert_eq!(
        common::solve("(set-logic QF_LIA)(assert (= (mod (- 7) (- 2)) 1))(check-sat)").trim(),
        "sat"
    );
}
