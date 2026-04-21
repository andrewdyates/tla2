// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_executor_qf_lra_simple_sat() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (<= x 10.0))
        (assert (>= x 5.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_lra_simple_unsat() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (<= x 5.0))
        (assert (>= x 10.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_lra_linear_constraint_unsat() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (<= (+ x y) 10.0))
        (assert (>= x 5.0))
        (assert (>= y 6.0))
        (check-sat)
    "#;
    // x >= 5, y >= 6, but x + y <= 10: 5 + 6 = 11 > 10, so UNSAT

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_lra_linear_constraint_sat() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (<= (+ x y) 10.0))
        (assert (>= x 3.0))
        (assert (>= y 4.0))
        (check-sat)
    "#;
    // x >= 3, y >= 4, x + y <= 10: 3 + 4 = 7 <= 10, so SAT

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_lra_strict_inequality() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 5.0))
        (assert (> x 5.0))
        (check-sat)
    "#;
    // x < 5 and x > 5 is impossible

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_lra_equality_with_strict() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (= x 5.0))
        (assert (> x 5.0))
        (check-sat)
    "#;
    // x = 5 and x > 5 is impossible

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
/// Regression test for #1243: LRA Farkas verification panic on simple equalities + disjunction.
#[test]
fn test_executor_qf_lra_farkas_verification_regression_1243() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x_0 Real)
        (assert (>= x_0 0))
        (assert (<= x_0 1))
        (declare-const y_0 Real)
        (assert (= y_0 (+ (* 1 x_0) 1)))
        (assert (or (< y_0 0.5) (> y_0 2.5)))
        (check-sat)
    "#;
    // UNSAT because x ∈ [0,1] => y = x+1 ∈ [1,2] which contradicts y ∉ [0.5,2.5]

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_lra_scaled_variable() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= (* 2.0 x) 10.0))
        (assert (>= x 5.0))
        (check-sat)
    "#;
    // 2x >= 10 and x >= 5: x >= 5 satisfies 2x >= 10

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
/// #5600: QF_LRA disequality (distinct) with arithmetic constraint.
///
/// Tests the NeedDisequalitySplit path in the LRA split-loop pipeline.
/// x != y with x + y = 10 is satisfiable (e.g., x=3, y=7).
#[test]
fn test_executor_qf_lra_distinct_sat_5600() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (distinct x y))
        (assert (= (+ x y) 10.0))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat"],
        "#5600: distinct x y with x+y=10 is satisfiable"
    );
}
/// #5600: QF_LRA negated equality with tight bounds.
///
/// Tests the disequality split on a variable with tight rational bounds.
/// x != 5, x > 4, x < 6 is satisfiable (e.g., x=4.5 or x=5.5).
#[test]
fn test_executor_qf_lra_negated_equality_tight_bounds_5600() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (not (= x 5.0)))
        (assert (> x 4.0))
        (assert (< x 6.0))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat"],
        "#5600: x != 5 with 4 < x < 6 is satisfiable (e.g., x=4.5)"
    );
}
/// #5600: QF_LRA contradictory disequality — UNSAT.
///
/// x = 5 AND x != 5 is a direct contradiction.
#[test]
fn test_executor_qf_lra_contradictory_disequality_unsat_5600() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (= x 5.0))
        (assert (not (= x 5.0)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "#5600: x = 5 AND x != 5 is contradictory"
    );
}

// QF_LIA (Linear Integer Arithmetic) Tests
// =========================================
