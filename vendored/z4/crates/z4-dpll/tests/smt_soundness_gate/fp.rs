// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_FP soundness gate tests.
//!
//! Consumer: certus uses floating-point formulas directly and via mixed
//! bitvector/FP front-ends. The gate focuses on fully-ground FP formulas that
//! should produce definite answers and validate under the model checker.

use ntest::timeout;

use crate::helpers::{
    assert_sat_validates, assert_scope_results, assert_unsat_with_proof, ProofExpectation,
};

const FP32_POS_ONE: &str = "(fp #b0 #b01111111 #b00000000000000000000000)";
const FP32_POS_TWO: &str = "(fp #b0 #b10000000 #b00000000000000000000000)";
const FP32_POS_ZERO: &str = "(fp #b0 #b00000000 #b00000000000000000000000)";
const FP32_NEG_ZERO: &str = "(fp #b1 #b00000000 #b00000000000000000000000)";

// --- 1. SAT with model validation ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_fp_sat_validates_model() {
    assert_sat_validates(&format!(
        r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.eq x {FP32_POS_ONE}))
        (assert (fp.isNormal x))
        (check-sat)
    "#
    ));
}

// --- 2. UNSAT with proof envelope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_fp_unsat_proof_envelope() {
    assert_unsat_with_proof(
        &format!(
            r#"
        (set-logic QF_FP)
        (set-option :produce-proofs true)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.eq x {FP32_POS_ONE}))
        (assert (fp.eq x {FP32_POS_TWO}))
        (check-sat)
        (get-proof)
    "#
        ),
        ProofExpectation::TextOnly,
    );
}

// --- 3. Edge case: signed zero equality semantics ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_fp_signed_zero_sat_validates_model() {
    assert_sat_validates(&format!(
        r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.eq x {FP32_POS_ZERO}))
        (assert (fp.eq x {FP32_NEG_ZERO}))
        (check-sat)
    "#
    ));
}

// --- 4. Incremental push/pop scope ---

#[test]
#[timeout(10_000)]
fn test_gate_qf_fp_incremental_scope() {
    assert_scope_results(
        &format!(
            r#"
        (set-logic QF_FP)
        (declare-const x (_ FloatingPoint 8 24))
        (assert (fp.eq x {FP32_POS_ONE}))
        (check-sat)
        (push 1)
        (assert (fp.eq x {FP32_POS_TWO}))
        (check-sat)
        (pop 1)
        (check-sat)
    "#
        ),
        &["sat", "unsat", "sat"],
    );
}

// --- 5. Logic alias: QF_FPLRA must preserve mixed FP/Real soundness ---

#[test]
#[timeout(30_000)]
fn test_gate_qf_fplra_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_FPLRA)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const r Real)
        (assert (fp.eq x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= r (fp.to_real x)))
        (assert (>= r 0.5))
        (check-sat)
    "#,
    );
}

#[test]
#[timeout(30_000)]
fn test_gate_qf_fplra_incremental_scope() {
    assert_scope_results(
        r#"
        (set-logic QF_FPLRA)
        (declare-const x (_ FloatingPoint 8 24))
        (declare-const r Real)
        (assert (fp.eq x (fp #b0 #b01111111 #b00000000000000000000000)))
        (assert (= r (fp.to_real x)))
        (assert (> r 0.5))
        (check-sat)
        (push 1)
        (assert (< r 0.0))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        &["sat", "unsat", "sat"],
    );
}
