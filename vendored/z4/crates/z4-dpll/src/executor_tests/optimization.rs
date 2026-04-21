// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Optimization (OMT) executor tests — single and multi-objective.

use crate::Executor;
use z4_frontend::parse;
use z4_frontend::sexp::parse_sexp;

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
fn test_executor_optimize_maximize_qf_lia_equality_pinned_objective() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 20))
        (maximize x)
        (check-sat)
        (get-objectives)
    "#;

    let commands = parse(input).expect("SMT-LIB input should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("optimizer should execute equality-pinned objective");

    assert_eq!(outputs.first().map(String::as_str), Some("sat"));

    let sexp = parse_sexp(&outputs[1]).expect("objective output should parse");
    let items = sexp.as_list().expect("objective output should be a list");
    assert_eq!(items[0].as_symbol(), Some("objectives"));
    assert_eq!(items.len(), 2);

    let pair = items[1]
        .as_list()
        .expect("objective entry should be a pair");
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

// --- Multi-objective (lexicographic) tests (#4128 Phase 2) ---

#[test]
fn test_executor_optimize_lex_two_objectives_qf_lia() {
    // Lexicographic: maximize x first, then maximize y.
    // Constraints: x + y <= 10, x >= 0, y >= 0.
    // Optimal: x = 10 (maximized first), then y = 0 (constrained by x = 10).
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (maximize x)
        (maximize y)
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
    assert_eq!(items.len(), 3);

    let pair_x = items[1].as_list().unwrap();
    assert_eq!(pair_x[1].as_numeral(), Some("10"));

    let pair_y = items[2].as_list().unwrap();
    assert_eq!(pair_y[1].as_numeral(), Some("0"));
}

#[test]
fn test_executor_optimize_lex_min_then_max_qf_lia() {
    // Lexicographic: minimize x first, then maximize y.
    // Constraints: x + y <= 10, x >= 0, y >= 0.
    // Optimal: x = 0 (minimized first), then y = 10 (x pinned to 0).
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= x 0))
        (assert (>= y 0))
        (assert (<= (+ x y) 10))
        (minimize x)
        (maximize y)
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
    assert_eq!(items.len(), 3);

    let pair_x = items[1].as_list().unwrap();
    assert_eq!(pair_x[1].as_numeral(), Some("0"));

    let pair_y = items[2].as_list().unwrap();
    assert_eq!(pair_y[1].as_numeral(), Some("10"));
}

#[test]
fn test_executor_optimize_lex_real_two_objectives() {
    // Lexicographic Real: maximize x first, then maximize y.
    // Use separate bounds (not x+y combined) so simplex converges exactly.
    // x in [0, 21/2], y in [0, 7/2].
    // Optimal: x = 21/2 (maximized first), then y = 7/2.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (>= x (/ 0 1)))
        (assert (<= x (/ 21 2)))
        (assert (>= y (/ 0 1)))
        (assert (<= y (/ 7 2)))
        (maximize x)
        (maximize y)
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
    assert_eq!(items.len(), 3);

    let pair_x = items[1].as_list().unwrap();
    let val_x = format!("{}", pair_x[1]);
    assert!(
        val_x.contains("21") && val_x.contains("2"),
        "expected 21/2 for x, got: {val_x}"
    );

    let pair_y = items[2].as_list().unwrap();
    let val_y = format!("{}", pair_y[1]);
    assert!(
        val_y.contains("7") && val_y.contains("2"),
        "expected 7/2 for y, got: {val_y}"
    );
}
