// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// QF_BV Division tests
// =========================================================================

#[test]
fn test_executor_qf_bv_udiv_sat() {
    // x / 3 = 2 means x can be 6, 7, or 8
    // With additional constraint x = 7
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const q (_ BitVec 8))
        (assert (= q (bvudiv x #x03)))
        (assert (= q #x02))
        (assert (= x #x07))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_udiv_unsat() {
    // x / 3 = 2 and x / 3 = 3 is unsatisfiable
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvudiv x #x03) #x02))
        (assert (= (bvudiv x #x03) #x03))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_bv_urem_sat() {
    // x % 3 = 1 should be satisfiable (e.g., x = 1, 4, 7, ...)
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvurem x #x03) #x01))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_urem_constraint_sat() {
    // x % 4 = 3 and x < 16 should be satisfiable (x = 3, 7, 11, 15)
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvurem x #x04) #x03))
        (assert (bvult x #x10))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_div_by_zero() {
    // Division by zero: x / 0 = 0xFF (all ones for 8-bit)
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x05))
        (assert (= (bvudiv x #x00) #xff))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_rem_by_zero() {
    // Remainder by zero: x % 0 = x
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x07))
        (assert (= (bvurem x #x00) x))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_sdiv_positive() {
    // Signed division: 7 / 2 = 3
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x07))
        (assert (= (bvsdiv x #x02) #x03))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_srem_positive() {
    // Signed remainder: 7 % 3 = 1
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x07))
        (assert (= (bvsrem x #x03) #x01))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_div_quotient_remainder() {
    // Quotient-remainder relationship: a = q * b + r
    // For a = 10, b = 3: q = 3, r = 1
    let input = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (declare-const q (_ BitVec 8))
        (declare-const r (_ BitVec 8))
        (assert (= a #x0a))
        (assert (= b #x03))
        (assert (= q (bvudiv a b)))
        (assert (= r (bvurem a b)))
        (assert (= a (bvadd (bvmul q b) r)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_bv_div_no_wraparound_unsat() {
    // Regression: prevent overflow-based "solutions" to udiv/urem.
    // In 4-bit unsigned, 1 / 15 = 0 and 1 % 15 = 1, so the asserted values are UNSAT.
    let input = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 4))
        (declare-const b (_ BitVec 4))
        (assert (= a #b0001))
        (assert (= b #b1111))
        (assert (= (bvudiv a b) #b1111))
        (assert (= (bvurem a b) #b0000))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
