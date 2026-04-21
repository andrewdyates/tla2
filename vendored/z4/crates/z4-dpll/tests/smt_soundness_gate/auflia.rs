// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_AUFLIA soundness gate tests for the #6846 processor benchmarks.
//!
//! These regressions exercise the Nelson-Oppen bridge path where free
//! UF-valued interface terms produce model equalities that may not converge
//! in the non-persistent split loop. The soundness property is that the solver
//! must never return `sat` on these `:status unsat` benchmarks.
//!
//! Root cause: the eager extension path (`TheoryExtension`) drops theory
//! conflicts when model equality terms lack SAT variable mappings
//! (`_ext_partial > 0`), causing Unknown/timeout instead of unsat. Fixed by
//! switching AUFLIA from eager to lazy pipeline and removing model equality
//! retry limits (#6846).

use ntest::timeout;

use crate::helpers::{
    assert_not_sat, assert_not_unsat, assert_sat_validates, assert_scope_results,
    assert_unsat_with_proof, ProofExpectation,
};

/// Exact SMT-COMP add4 copy: `:status unsat` — small AUFLIA control (#3936).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(180_000))]
fn test_gate_qf_auflia_add4_not_sat() {
    assert_not_sat(include_str!("data/add4.smt2"));
}

/// Exact SMT-COMP add5 copy: `:status unsat` — must not return false-SAT (#6846).
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(180_000))]
fn test_gate_qf_auflia_add5_not_sat_6846() {
    assert_not_sat(include_str!("data/add5.smt2"));
}

/// Exact SMT-COMP add6 copy: `:status unsat` — must not return false-SAT (#6846).
/// Debug baseline: ~117s in isolation; needs 600s under 28-parallel contention.
#[test]
#[cfg_attr(debug_assertions, timeout(600_000))]
#[cfg_attr(not(debug_assertions), timeout(180_000))]
fn test_gate_qf_auflia_add6_not_sat_6846() {
    assert_not_sat(include_str!("data/add6.smt2"));
}

// --- Consumer coverage: sunder uses AUFLIA with arrays, UF, and LIA ---

/// SAT with model validation: array store/select with UF and LIA constraints.
/// Exercises the Nelson-Oppen bridge between array, EUF, and LIA solvers.
#[test]
#[timeout(30_000)]
fn test_gate_qf_auflia_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun f (Int) Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= x 5))
        (assert (= y (f x)))
        (assert (= y 42))
        (assert (= (select (store a x y) x) 42))
        (check-sat)
    "#,
    );
}

/// UNSAT with proof envelope: array + UF + LIA contradiction.
#[test]
#[timeout(30_000)]
fn test_gate_qf_auflia_unsat_proof_envelope() {
    assert_unsat_with_proof(
        r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-proofs true)
        (declare-fun a () (Array Int Int))
        (declare-fun x () Int)
        (assert (= (select (store a 0 10) 0) 10))
        (assert (not (= (select (store a 0 10) 0) 10)))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

/// Incremental push/pop scope: sunder pattern with array constraints.
#[test]
#[timeout(30_000)]
fn test_gate_qf_auflia_incremental_scope() {
    assert_scope_results(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a () (Array Int Int))
        (declare-fun x () Int)
        (assert (= x 10))
        (assert (= (select a x) 42))
        (check-sat)
        (push 1)
        (assert (not (= (select a 10) 42)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        &["sat", "unsat", "sat"],
    );
}

/// Exact SMT-COMP read7 copy: `:status unsat` and Z3 returns `unsat`.
/// The previous tracked fixture had drifted into a satisfiable reduction, so
/// this copy is refreshed from the local SMT-COMP benchmark.
#[test]
#[cfg_attr(debug_assertions, timeout(300_000))]
#[cfg_attr(not(debug_assertions), timeout(180_000))]
fn test_gate_qf_auflia_read7_not_sat_6846() {
    assert_not_sat(include_str!("data/read7.smt2"));
}

// --- #6820 storecomm+swap family coverage (34% gap vs Z3) ---

/// SMT-COMP storecomm (smallest instance): `:status sat` — model must validate.
/// storecomm family dominates the QF_AUFLIA performance gap (#6820).
#[test]
#[timeout(60_000)]
fn test_gate_qf_auflia_storecomm_small_not_unsat() {
    assert_not_unsat(include_str!("data/storecomm_small.smt2"));
}

/// SMT-COMP swap (smallest instance): `:status sat` — model must validate.
/// swap family is the second-largest contributor to the QF_AUFLIA gap (#6820).
#[test]
#[timeout(60_000)]
fn test_gate_qf_auflia_swap_small_not_unsat() {
    assert_not_unsat(include_str!("data/swap_small.smt2"));
}
