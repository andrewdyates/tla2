// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// QF_ABV (Quantifier-Free Arrays + Bitvectors) tests
// =========================================================================

#[test]
fn test_executor_qf_abv_simple_sat() {
    // Simple array with bitvector index and value
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (= v (select a i)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_store_select_same_index() {
    // select(store(a, i, v), i) = v (ROW1 axiom)
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (= (select (store a i v) i) v))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_store_different_value_unsat() {
    // select(store(a, i, v1), i) = v2 where v1 != v2 is unsat
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (assert (= (select (store a i #x05) i) #x06))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_bv_constraints_sat() {
    // Array with bitvector operations on indices/values
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const v (_ BitVec 8))
        (assert (= i #x05))
        (assert (= v (select a i)))
        (assert (bvult v #x10))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_multiple_stores_sat() {
    // Multiple stores to same array
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
        (assert (= b (store (store a #x00 #x01) #x01 #x02)))
        (assert (= (select b #x00) #x01))
        (assert (= (select b #x01) #x02))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_contradictory_values_unsat() {
    // Same index, different values - contradiction
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (assert (= (select a i) #x05))
        (assert (= (select a i) #x06))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_executor_qf_abv_bv_arithmetic_on_values() {
    // BV arithmetic on array values
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const i (_ BitVec 8))
        (declare-const j (_ BitVec 8))
        (assert (= (bvadd (select a i) (select a j)) #x0a))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_32bit_sat() {
    // 32-bit bitvectors (common for Kani workloads)
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 32) (_ BitVec 32)))
        (declare-const i (_ BitVec 32))
        (declare-const v (_ BitVec 32))
        (assert (= i #x00000005))
        (assert (= v (select a i)))
        (assert (bvult v #x00000100))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_memory_model_sat() {
    // Memory model pattern: store then select at different index
    let input = r#"
        (set-logic QF_ABV)
        (declare-const mem (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const ptr1 (_ BitVec 8))
        (declare-const ptr2 (_ BitVec 8))
        (declare-const val (_ BitVec 8))
        (assert (= ptr1 #x10))
        (assert (= ptr2 #x20))
        (assert (= val #x42))
        (assert (= (select (store mem ptr1 val) ptr2) (select mem ptr2)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_executor_qf_abv_overwrite_sat() {
    // Store overwrites previous value at same index
    let input = r#"
        (set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
        (assert (= b (store (store a #x05 #x01) #x05 #x02)))
        (assert (= (select b #x05) #x02))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
