// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_get_value_uf_returning_int() {
    // Regression test for #385: get-value on UF application returning Int
    // should return the actual value, not placeholder 0
    let input = r#"
        (set-option :produce-models true)
        (set-logic QF_UFLIA)
        (declare-sort U 0)
        (declare-fun f (U) Int)
        (declare-fun x () U)
        (assert (= (f x) 100))
        (check-sat)
        (get-value ((f x)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // The function application should evaluate to 100, not 0
    assert!(
        outputs[1].contains("100"),
        "Expected 100 in get-value output for (f x): {}",
        outputs[1]
    );
    // Should NOT contain 0 as the value (the placeholder)
    assert!(
        !outputs[1].contains("(f x) 0)"),
        "Should not return placeholder 0 for (f x): {}",
        outputs[1]
    );
}
#[test]
fn test_get_value_uf_returning_real() {
    // Test UF returning Real sort
    let input = r#"
        (set-option :produce-models true)
        (set-logic QF_UFLRA)
        (declare-sort U 0)
        (declare-fun g (U) Real)
        (declare-fun y () U)
        (assert (= (g y) 3.14))
        (check-sat)
        (get-value ((g y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Real values may be formatted as ratio (/ num denom) or decimal
    assert!(
        outputs[1].contains("3.14") || outputs[1].contains("(/ 157 50)"),
        "Expected 3.14 or (/ 157 50) in get-value output for (g y): {}",
        outputs[1]
    );
    // Should NOT contain placeholder values (0.0 or (_ +zero ...))
    assert!(
        !outputs[1].contains("(g y) 0.0)") && !outputs[1].contains("+zero"),
        "Should not return placeholder value for (g y): {}",
        outputs[1]
    );
}

// QF_LRA (Linear Real Arithmetic) Tests
// =====================================
#[test]
fn test_executor_qf_uflia_simple_sat() {
    // Combine UF and LIA: f(x) = y, x >= 0
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-fun f (Int) Int)
        (assert (= (f x) y))
        (assert (>= x 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_uflia_function_equality_unsat() {
    // f(x) = 5, f(x) = 6 is contradictory
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-fun f (Int) Int)
        (assert (= (f x) 5))
        (assert (= (f x) 6))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_uflia_congruence_with_arithmetic() {
    // Test EUF congruence with arithmetic on the same function application
    // This test uses the SAME function application f(x) in both constraints
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-fun f (Int) Int)
        (assert (>= (f x) 10))
        (assert (< (f x) 5))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // f(x) >= 10 and f(x) < 5 is a contradiction
    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_uflia_arithmetic_constraint_unsat() {
    // UF with integer gap constraint
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const x Int)
        (declare-fun f (Int) Int)
        (assert (> x 5))
        (assert (< x 6))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // No integer between 5 and 6 exclusively
    assert_eq!(outputs, vec!["unsat"]);
}
/// Mirror of the QF_UFLIA integer-gap test under QF_AUFLIA (#6300).
/// Ensures both combined-int entry points are narrowed to pure LIA.
#[test]
fn test_executor_qf_auflia_arithmetic_constraint_unsat_6300() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const x Int)
        (declare-fun f (Int) Int)
        (assert (> x 5))
        (assert (< x 6))
        (check-sat)
    "#;

    let commands = parse(input).expect("parse QF_AUFLIA input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute QF_AUFLIA");

    // No integer between 5 and 6 exclusively — same as QF_UFLIA case.
    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_uflia_combined_sat() {
    // Combination of UF equality and separate arithmetic constraints
    // The UF equality (= (f a) (f b)) is independent of arithmetic
    let input = r#"
        (set-logic QF_UFLIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-fun f (Int) Int)
        (assert (>= a 0))
        (assert (<= b 10))
        (assert (= (f a) (f b)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

// QF_UFLRA (Uninterpreted Functions with Linear Real Arithmetic) Tests
