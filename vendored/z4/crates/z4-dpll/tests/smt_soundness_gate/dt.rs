// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_DT soundness gate tests.
//!
//! Datatype formulas do not currently dominate the consumer-triage queue, but
//! they are a supported public logic and already have known model-validation
//! edge cases. This gate keeps constructor/selector/tester basics under the
//! same soundness harness as the other SMT logics.

use ntest::timeout;

use crate::helpers::{
    assert_sat_validates, assert_scope_results, assert_unsat_with_proof, ProofExpectation,
};

// --- 1. SAT with model validation ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_DT)
        (declare-datatypes ((Maybe 0)) (((Nothing) (Just (value Int)))))
        (declare-const x Maybe)
        (assert (is-Just x))
        (assert (= (value x) 42))
        (check-sat)
    "#,
    );
}

// --- 2. UNSAT with proof envelope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_unsat_proof_envelope() {
    assert_unsat_with_proof(
        r#"
        (set-logic QF_DT)
        (set-option :produce-proofs true)
        (declare-datatypes ((Option 0)) (((None) (Some (value Int)))))
        (declare-const x Option)
        (declare-const y Int)
        (assert (= x None))
        (assert (= x (Some y)))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

// --- 3. Edge case: selector values must validate against constructor terms ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_selector_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_DT)
        (declare-datatypes ((Pair 0)) (((mk-pair (fst Int) (snd Int)))))
        (declare-const p Pair)
        (assert (= (fst p) 10))
        (assert (= (snd p) 20))
        (check-sat)
    "#,
    );
}

// --- 4. Incremental push/pop scope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_dt_incremental_scope() {
    assert_scope_results(
        r#"
        (set-logic QF_DT)
        (declare-datatype Color ((Red) (Green)))
        (declare-const c Color)
        (assert (= c Red))
        (check-sat)
        (push 1)
        (assert (= c Green))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        &["sat", "unsat", "sat"],
    );
}
