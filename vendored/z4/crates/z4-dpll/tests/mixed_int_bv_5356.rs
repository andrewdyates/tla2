// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for mixed Int/BitVec formulas (#5356).
//!
//! When a formula uses both Int and BitVec sorts without conversion functions
//! (bv2nat/int2bv), the solver routes to the BV-first strategy: try BV solver
//! (which handles extract/concat/etc.), fall back to AUFLIA if model validation
//! fails on Int constraints.

use ntest::timeout;
mod common;

/// Core repro case from #5356: mixed Int + BitVec with `set-logic ALL`.
/// Previously returned `unknown` because AUFLIA treated BV extract as UF.
#[test]
#[timeout(60_000)]
fn test_mixed_int_bv_sat_all_logic_5356() {
    let smt = r#"
        (set-logic ALL)
        (declare-const x Int)
        (declare-const S (_ BitVec 2))
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (= x 0))
        (assert (= ((_ extract 0 0) S) #b1))
        (check-sat)
        (get-value (x S))
    "#;
    let outputs = common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "Expected sat for mixed Int/BV formula, got: {outputs:?}"
    );
}

/// Same formula without explicit logic (auto-detection).
#[test]
#[timeout(60_000)]
fn test_mixed_int_bv_sat_auto_detect_5356() {
    let smt = r#"
        (declare-const x Int)
        (declare-const S (_ BitVec 2))
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (= x 0))
        (assert (= ((_ extract 0 0) S) #b1))
        (check-sat)
    "#;
    let outputs = common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// Contradictory Int constraints with BV: must return UNSAT.
/// BV solver may produce false SAT (treats Int predicates as opaque),
/// but model validation catches it and falls back to AUFLIA.
#[test]
#[timeout(60_000)]
fn test_mixed_int_bv_unsat_contradictory_int_5356() {
    let smt = r#"
        (set-logic ALL)
        (declare-const x Int)
        (declare-const S (_ BitVec 2))
        (assert (>= x 2))
        (assert (<= x 1))
        (assert (= ((_ extract 0 0) S) #b1))
        (check-sat)
    "#;
    let outputs = common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Disjunction across Int and BV theories.
#[test]
#[timeout(60_000)]
fn test_mixed_int_bv_disjunction_5356() {
    let smt = r#"
        (set-logic ALL)
        (declare-const x Int)
        (declare-const S (_ BitVec 2))
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (or (and (= x 0) (= ((_ extract 0 0) S) #b1))
                    (and (= x 1) (= ((_ extract 1 1) S) #b1))))
        (check-sat)
        (get-value (x S))
    "#;
    let outputs = common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "Expected sat for disjunctive mixed formula, got: {outputs:?}"
    );
}

/// BV-only UNSAT should still work through the BV-first path.
#[test]
#[timeout(60_000)]
fn test_mixed_int_bv_unsat_bv_contradiction_5356() {
    let smt = r#"
        (set-logic ALL)
        (declare-const x Int)
        (declare-const S (_ BitVec 2))
        (assert (= x 0))
        (assert (= ((_ extract 0 0) S) #b1))
        (assert (= ((_ extract 0 0) S) #b0))
        (check-sat)
    "#;
    let outputs = common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}
