// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// QF_UFBV (Quantifier-Free UF + Bitvectors) tests
// =========================================================================

#[test]
fn test_executor_qf_ufbv_simple_sat() {
    // Simple uninterpreted function with bitvector arguments and result
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (assert (= (f x) #x42))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_ufbv_functional_consistency() {
    // f(x) = f(x) should always be sat (same term)
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (assert (= (f x) (f x)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_ufbv_congruence_sat() {
    // x = y implies f(x) = f(y) (functional consistency)
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x y))
        (assert (= (f x) (f y)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_ufbv_congruence_unsat() {
    // x = y and f(x) != f(y) is unsat (violates congruence)
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x y))
        (assert (not (= (f x) (f y))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_ufbv_multi_arg_sat() {
    // Uninterpreted function with multiple arguments
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun g ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (g x y) #x05))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_ufbv_multi_arg_congruence_unsat() {
    // (x1 = y1 and x2 = y2) implies g(x1,x2) = g(y1,y2)
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun g ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-const x1 (_ BitVec 8))
        (declare-const x2 (_ BitVec 8))
        (declare-const y1 (_ BitVec 8))
        (declare-const y2 (_ BitVec 8))
        (assert (= x1 y1))
        (assert (= x2 y2))
        (assert (not (= (g x1 x2) (g y1 y2))))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_ufbv_bv_constraints_sat() {
    // Combine UF with BV arithmetic
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (assert (= x #x05))
        (assert (bvult (f x) #x10))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_ufbv_multiple_functions_sat() {
    // Multiple uninterpreted functions
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-fun h ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (assert (= (bvadd (f x) (h x)) #x0a))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_ufbv_nested_function_sat() {
    // Nested uninterpreted function applications
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (assert (= (f (f x)) #x42))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_ufbv_32bit_sat() {
    // 32-bit bitvectors with UF
    let input = r#"
        (set-logic QF_UFBV)
        (declare-fun f ((_ BitVec 32)) (_ BitVec 32))
        (declare-const x (_ BitVec 32))
        (assert (= x #x00000005))
        (assert (bvult (f x) #x00000100))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
