// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_executor_qf_lia_simple_sat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (<= x 10))
        (assert (>= x 5))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_lia_simple_unsat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (<= x 5))
        (assert (>= x 10))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_lia_integer_gap_unsat() {
    // x > 5 and x < 6 where x is integer - no integer between 5 and 6
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 5))
        (assert (< x 6))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // LIA should detect this is UNSAT (no integer in (5,6))
    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_lia_integer_boundary_sat() {
    // x >= 5 and x <= 6 where x is integer - x can be 5 or 6
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 5))
        (assert (<= x 6))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_lia_equality() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 5))
        (assert (>= x 1))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_lia_linear_constraint_sat() {
    // x + y <= 10, x >= 3, y >= 4: solution x=3, y=4 (integer)
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (<= (+ x y) 10))
        (assert (>= x 3))
        (assert (>= y 4))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_lia_linear_constraint_unsat() {
    // x + y <= 10, x >= 5, y >= 6: 5 + 6 = 11 > 10, so UNSAT
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (<= (+ x y) 10))
        (assert (>= x 5))
        (assert (>= y 6))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

// QF_UFLIA (Uninterpreted Functions with Linear Integer Arithmetic) Tests
