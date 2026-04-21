// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core executor tests - basic SAT/UNSAT, push/pop, multiple check-sat

use crate::Executor;
use z4_frontend::parse;
use z4_frontend::sexp::parse_sexp;

#[test]
fn test_executor_simple_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (or a b))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_simple_unsat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (assert (not a))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_optimize_maximize_qf_lia() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (maximize (+ (* 2 x) y))
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    assert_eq!(pair[1].as_numeral(), Some("20"));
}

#[test]
fn test_executor_optimize_maximize_qf_lra() {
    // Maximize x subject to 0 <= x <= 10.5. Optimal: x = 10.5 = 21/2.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x 0.0))
        (assert (<= x (/ 21 2)))
        (maximize x)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    // Optimal value is 21/2 = 10.5
    let val_str = format!("{}", pair[1]);
    assert!(
        val_str.contains("21") && val_str.contains("2"),
        "expected 21/2 (10.5), got: {val_str}"
    );
}

#[test]
fn test_executor_optimize_minimize_qf_lra() {
    // Minimize x subject to x >= 3.5. Optimal: x = 3.5 = 7/2.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x (/ 7 2)))
        (assert (<= x 100.0))
        (minimize x)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    // Optimal value is 7/2 = 3.5
    let val_str = format!("{}", pair[1]);
    assert!(
        val_str.contains("7") && val_str.contains("2"),
        "expected 7/2 (3.5), got: {val_str}"
    );
}

#[test]
fn test_executor_optimize_real_linear_combination() {
    // Maximize (+ (* (/ 3 1) x) (* (/ 2 1) y)) subject to x + y <= 10, x >= 0, y >= 0.
    // Optimal at vertex (10, 0): objective = 30.
    // Uses exact rational coefficients to avoid decimal-to-float precision loss.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x (/ 0 1)))
        (assert (>= y (/ 0 1)))
        (assert (<= (+ x y) (/ 10 1)))
        (maximize (+ (* (/ 3 1) x) (* (/ 2 1) y)))
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).unwrap();
    let items = sexp.as_list().unwrap();
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1].as_list().unwrap();
    assert_eq!(pair.len(), 2);
    // Optimal value is 30 (at x=10, y=0)
    let val_str = format!("{}", pair[1]);
    assert!(
        val_str == "30" || val_str.contains("30"),
        "expected 30, got: {val_str}"
    );
}

#[test]
fn test_executor_optimize_real_unsat() {
    // Infeasible constraints: x >= 5 and x <= 3.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= x 5.0))
        (assert (<= x 3.0))
        (maximize x)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
}

#[test]
fn test_executor_qf_nira_with_real_terms_returns_unknown() {
    let input = r#"
        (set-logic QF_NIRA)
        (declare-const x Real)
        (declare-const y Int)
        (assert (= (* x x) (to_real y)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unknown"]);
}

#[test]
fn test_executor_qf_nira_with_int_only_can_be_unsat() {
    let input = r#"
        (set-logic QF_NIRA)
        (declare-const x Int)
        (assert (> x 0))
        (assert (<= x 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_ufidl_as_uflia_alias() {
    let input = r#"
        (set-logic QF_UFIDL)
        (declare-sort U 0)
        (declare-fun f (U) Int)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (assert (= (- (f a) (f b)) 1))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_euf_unsat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun p (U) Bool)
        (assert (= a b))
        (assert (p a))
        (assert (not (p b)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_euf_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun p (U) Bool)
        (assert (p a))
        (assert (not (p b)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

// test_executor_eq_diamond20_unsat moved to integration test with watchdog (#1535)

#[test]
fn test_executor_euf_congruence() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= a c)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_distinct() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (assert (distinct a b))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_multiple_check_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (check-sat)
        (assert (not a))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat", "unsat"]);
}

#[test]
fn test_executor_push_pop() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (push 1)
        (assert (not a))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // After push + assert (not a), should be unsat
    // After pop, only a is asserted, should be sat
    assert_eq!(outputs, vec!["unsat", "sat"]);
}

#[test]
fn test_executor_no_logic() {
    // Should work with default logic (treated as QF_UF)
    let input = r#"
        (declare-const a Bool)
        (assert a)
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
