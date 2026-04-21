// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::Executor;
use z4_frontend::parse;

fn run_script(input: &str) -> Vec<String> {
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("SMT-LIB script should execute")
}

// --- Core check-sat path tests ---

#[test]
fn bv_sat_simple_equality() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x0A))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn bv_check_sat_applies_random_seed_to_sat() {
    let input = r#"
        (set-logic QF_BV)
        (set-option :random-seed 42)
        (declare-const x (_ BitVec 8))
        (assert (= x #x0A))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("SMT-LIB script should execute");

    assert_eq!(outputs, vec!["sat"]);
    assert_eq!(exec.last_applied_sat_random_seed_for_test(), Some(42));
}

#[test]
fn bv_unsat_contradictory_values() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x01))
        (assert (= x #x02))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn bv_sat_arithmetic() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (bvadd x y) #x0A))
        (assert (= x #x05))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn bv_unsat_overflow() {
    // For 8-bit: bvadd wraps, so x + 1 = 0 means x = 255
    // Combined with x < 200 (unsigned), this should be unsat
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvadd x #x01) #x00))
        (assert (bvult x #xC8))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

#[test]
fn bv_empty_assertions_sat() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 32))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

#[test]
fn bv_sat_bitwise_ops() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= (bvand x #x0F) #x05))
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["sat"]);
}

// --- Incremental / push-pop tests ---

#[test]
fn incremental_bv_push_pop_roundtrip() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x01))
        (push 1)
        (assert (= x #x02))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    assert_eq!(run_script(input), vec!["unsat", "sat"]);
}

#[test]
fn incremental_bv_persistent_sat_inherits_random_seed() {
    let input = r#"
        (set-logic QF_BV)
        (set-option :random-seed 42)
        (declare-const x (_ BitVec 8))
        (push 1)
        (assert (= x #x01))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("SMT-LIB script should execute");

    assert_eq!(outputs, vec!["sat"]);

    let state = exec
        .incr_bv_state
        .as_ref()
        .expect("incremental BV state should exist");
    let solver = state
        .persistent_sat
        .as_ref()
        .expect("expected incremental BV to initialize a persistent SAT solver");
    assert_eq!(solver.random_seed(), 42);
}

#[test]
fn incremental_abv_persistent_sat_inherits_random_seed() {
    let input = r#"
        (set-logic QF_ABV)
        (set-option :random-seed 42)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (push 1)
        (assert (= (select a #x01) #x2A))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("incremental ABV script should execute");

    assert_eq!(outputs, vec!["sat"]);

    let state = exec
        .incr_bv_state
        .as_ref()
        .expect("incremental ABV state should exist");
    let solver = state
        .persistent_sat
        .as_ref()
        .expect("expected incremental ABV to initialize a persistent SAT solver");
    assert_eq!(solver.random_seed(), 42);
}

#[test]
fn incremental_ufbv_persistent_sat_inherits_random_seed() {
    let input = r#"
        (set-logic QF_UFBV)
        (set-option :random-seed 42)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const x (_ BitVec 8))
        (push 1)
        (assert (= (f x) #x2A))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("incremental UFBV script should execute");

    assert_eq!(outputs, vec!["sat"]);

    let state = exec
        .incr_bv_state
        .as_ref()
        .expect("incremental UFBV state should exist");
    let solver = state
        .persistent_sat
        .as_ref()
        .expect("expected incremental UFBV to initialize a persistent SAT solver");
    assert_eq!(solver.random_seed(), 42);
}

#[test]
fn incremental_aufbv_persistent_sat_inherits_random_seed() {
    let input = r#"
        (set-logic QF_AUFBV)
        (set-option :random-seed 42)
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (push 1)
        (assert (= (select a x) (f x)))
        (check-sat)
    "#;

    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("incremental AUFBV script should execute");

    assert_eq!(outputs, vec!["sat"]);

    let state = exec
        .incr_bv_state
        .as_ref()
        .expect("incremental AUFBV state should exist");
    let solver = state
        .persistent_sat
        .as_ref()
        .expect("expected incremental AUFBV to initialize a persistent SAT solver");
    assert_eq!(solver.random_seed(), 42);
}

#[test]
fn incremental_bv_contradiction_after_push_pop_cycle() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x01))
        (push 1)
        (assert (bvugt x #x00))
        (check-sat)
        (pop 1)
        (push 1)
        (assert (= x #x02))
        (check-sat)
        (pop 1)
    "#;
    let result = run_script(input);
    assert_eq!(
        result,
        vec!["sat", "unsat"],
        "x=#x01 and x=#x02 should be UNSAT after push/pop cycle, got {result:?}"
    );
}

#[test]
fn incremental_bv_nested_push_pop() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= x #x01))
        (push 1)
        (assert (bvugt x #x00))
        (push 1)
        (assert (= x #x02))
        (check-sat)
        (pop 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat", "sat", "sat"]);
}

#[test]
fn incremental_bv_empty_assertions_are_sat() {
    let input = r#"
        (set-logic QF_BV)
        (push 1)
        (check-sat)
        (pop 1)
        (check-sat)
    "#;

    assert_eq!(run_script(input), vec!["sat", "sat"]);
}

/// Regression test for #5441: incremental BV path missing equality congruence axioms.
#[test]
fn incremental_bv_eq_congruence_basic_5441() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (assert (= a b))
        (push 1)
        (assert (= a #x05))
        (assert (not (= b #x05)))
        (check-sat)
        (pop 1)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}

/// #5441: congruence axioms survive push/pop.
#[test]
fn incremental_bv_eq_congruence_push_pop_5441() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (assert (= a b))
        (push 1)
        (assert (= a #x05))
        (assert (not (= b #x05)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#;
    assert_eq!(run_script(input), vec!["unsat", "sat"]);
}

/// #5441: ITE-based congruence in incremental mode.
#[test]
fn incremental_bv_eq_congruence_ite_5441() {
    let input = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (declare-const r1 (_ BitVec 8))
        (declare-const r2 (_ BitVec 8))
        (assert (= a b))
        (push 1)
        (assert (= r1 (ite (= a #x05) #x01 #x00)))
        (assert (= r2 (ite (= b #x05) #x01 #x00)))
        (assert (not (= r1 r2)))
        (check-sat)
        (pop 1)
    "#;
    assert_eq!(run_script(input), vec!["unsat"]);
}
