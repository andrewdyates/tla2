// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #3389 — QF_SNIA dispatch and correctness.

#[macro_use]
mod common;

use ntest::timeout;

#[test]
#[timeout(10_000)]
fn qf_snia_pure_string_formula_is_sat() {
    let smt = r#"
(set-logic QF_SNIA)
(declare-fun x () String)
(assert (= x "a"))
(check-sat)
"#;
    let result = common::solve(smt);
    assert_eq!(
        common::sat_result(&result),
        Some("sat"),
        "pure-string QF_SNIA formula is satisfiable"
    );
}

#[test]
#[timeout(10_000)]
fn qf_snia_check_sat_assuming_with_to_int_routes() {
    let smt = r#"
(set-logic QF_SNIA)
(declare-fun x () String)
(assert (= x "42"))
(check-sat-assuming ((= (str.to_int x) 43)))
"#;
    let result = common::solve(smt);
    assert_eq!(
        common::sat_result(&result),
        Some("unsat"),
        "str.to_int(\"42\") != 43 under check-sat-assuming"
    );
}

#[test]
#[timeout(10_000)]
fn qf_snia_to_int_mismatch_is_unsat() {
    let smt = r#"
(set-logic QF_SNIA)
(declare-fun x () String)
(assert (= x "42"))
(assert (= (str.to_int x) 43))
(check-sat)
"#;
    let result = common::solve(smt);
    assert_eq!(
        common::sat_result(&result),
        Some("unsat"),
        "str.to_int(\"42\") = 43 is unsatisfiable"
    );
}

#[test]
#[timeout(10_000)]
fn qf_snia_from_int_mismatch_is_unsat() {
    let smt = r#"
(set-logic QF_SNIA)
(assert (= (str.from_int 42) "43"))
(check-sat)
"#;
    let result = common::solve(smt);
    assert_eq!(
        common::sat_result(&result),
        Some("unsat"),
        "str.from_int(42) = \"43\" is unsatisfiable"
    );
}

#[test]
#[timeout(10_000)]
fn qf_snia_true_nonlinear_constraint_remains_unknown() {
    let smt = r#"
(set-logic QF_SNIA)
(declare-fun x () String)
(declare-fun n () Int)
(assert (= x "a"))
(assert (= (* n n) 2))
(check-sat)
"#;
    let result = common::solve(smt);
    assert_eq!(
        common::sat_result(&result),
        Some("unknown"),
        "true non-linear Int arithmetic in QF_SNIA should still return unknown"
    );
}
