// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_LIA soundness gate tests (Packet 1).

use ntest::timeout;

use crate::helpers::{
    assert_sat_validates, assert_scope_results, assert_unsat_with_proof, ProofExpectation,
};

// --- 1. SAT with model validation ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_lia_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= x 4))
        (assert (= y (+ x 2)))
        (assert (> y 0))
        (check-sat)
    "#,
    );
}

// --- 2. UNSAT with proof envelope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_lia_unsat_proof_envelope() {
    // Multi-variable sum: x+y >= 10 with x <= 3 and y <= 3 is UNSAT.
    // Ported from lia_incremental_push_pop.rs:306-343.
    assert_unsat_with_proof(
        r#"
        (set-logic QF_LIA)
        (set-option :produce-proofs true)
        (declare-const x Int)
        (declare-const y Int)
        (assert (>= (+ x y) 10))
        (assert (<= x 3))
        (assert (<= y 3))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::InternalChecked,
    );
}

// --- 3. Edge case: negative/zero constants ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_lia_edge_case() {
    // Involves negative constants and multiplication by -1 (unary minus).
    // x <= -5 AND x >= 0 is UNSAT.
    assert_unsat_with_proof(
        r#"
        (set-logic QF_LIA)
        (set-option :produce-proofs true)
        (declare-const x Int)
        (assert (<= x (- 5)))
        (assert (>= x 0))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::InternalChecked,
    );
}

// --- 4. Incremental push/pop scope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_lia_incremental_scope() {
    // Ported from lia_incremental_push_pop.rs:30-56.
    // Scoped assertions must not leak after pop.
    assert_scope_results(
        r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (= (+ x y) 10))
        (check-sat)
        (push 1)
        (assert (>= x 100))
        (assert (>= y 100))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        &["sat", "unsat", "sat"],
    );
}
