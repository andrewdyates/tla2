// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_executor_qf_auflia_simple_sat() {
    // Basic array with integer indices and UF
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-fun f (Int) Int)
        (assert (= (select a i) (f i)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_auflia_array_store_select() {
    // Test simple array read
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const v Int)
        (assert (= (select a i) v))
        (assert (>= v 0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_auflia_arithmetic_constraint_unsat() {
    // Array with contradictory arithmetic constraints on values
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (>= (select a i) 10))
        (assert (< (select a i) 5))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_auflia_function_equality_unsat() {
    // f(i) = 5, f(i) = 6 is contradictory (EUF reasoning)
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const i Int)
        (declare-fun f (Int) Int)
        (assert (= (f i) 5))
        (assert (= (f i) 6))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_auflia_combined_sat() {
    // Combination of arrays, UF, and arithmetic - all satisfiable
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-fun f (Int) Int)
        (assert (>= i 0))
        (assert (<= j 10))
        (assert (= (f i) (select a j)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_auflia_index_bounds() {
    // Array with integer index constraints
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (>= i 0))
        (assert (<= i 100))
        (assert (= (select a i) i))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
/// Regression test for #5086: store commutativity pattern.
/// store(store(a,i,v),j,v) = store(store(a,j,v),i,v) when i ≠ j.
/// Without eager ROW1/ROW2 lemma preprocessing, the solver returns `unknown`
/// because the SAT solver cannot reason about index equality relationships
/// that arise from extensionality Skolem variables.
#[test]
fn test_executor_qf_auflia_store_commutativity_unsat() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun v () Int)
        (assert (not (= i j)))
        (assert (not (= (store (store a i v) j v) (store (store a j v) i v))))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(outputs, vec!["unsat"]);
}
/// Regression test for #5086: extended store commutativity with read-back.
/// Tests that after two stores with disjoint indices, reading back gives the
/// correct values regardless of store order.
#[test]
fn test_executor_qf_auflia_store_commutativity_readback_unsat() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun v () Int)
        (declare-fun w () Int)
        (assert (not (= i j)))
        (assert (not (=
            (select (store (store a i v) j w) i)
            v)))
        (check-sat)
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execution succeeds");

    assert_eq!(outputs, vec!["unsat"]);
}

// QF_AUFLRA (Arrays + Uninterpreted Functions + Linear Real Arithmetic) Tests
