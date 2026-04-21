// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_detect_logic_qf_uf() {
    let smt2 = "(set-logic QF_UF)\n(declare-const a Bool)";
    assert_eq!(detect_logic(smt2), Some(Logic::QfUf));
}

#[test]
fn test_detect_logic_qf_lia() {
    let smt2 = "(set-logic QF_LIA)\n(declare-const x Int)";
    assert_eq!(detect_logic(smt2), Some(Logic::QfLia));
}

#[test]
fn test_detect_logic_missing() {
    let smt2 = "(declare-const a Bool)";
    assert!(detect_logic(smt2).is_none());
}

#[test]
fn test_certificate_qf_bool_unsat() {
    let smt2 = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (assert (not a))
    "#;

    let cert =
        export_unsat_certificate_from_smt2(smt2).expect("QF_BOOL UNSAT should produce certificate");

    assert!(!cert.alethe.is_empty());
    assert!(cert.quality.is_complete());
}

#[test]
fn test_certificate_qf_uf_unsat() {
    let smt2 = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun c () U)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= a c)))
    "#;

    let cert =
        export_unsat_certificate_from_smt2(smt2).expect("QF_UF UNSAT should produce certificate");

    assert!(!cert.alethe.is_empty());
    assert!(cert.quality.is_complete());
}

#[test]
fn test_certificate_sat_rejected() {
    let smt2 = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
    "#;

    let err = export_unsat_certificate_from_smt2(smt2).expect_err("SAT result should be rejected");

    assert!(
        matches!(err, LeanError::ProofFailed { .. }),
        "expected ProofFailed, got: {err:?}"
    );
}

#[test]
fn test_certificate_arithmetic_rejected() {
    // QF_LIA proofs use lia_generic rules not in the lean5 whitelist.
    let smt2 = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 10))
        (assert (< x 5))
    "#;

    let result = export_unsat_certificate_from_smt2(smt2);
    // Arithmetic proof should be rejected because lia_generic/la_generic
    // are not in the lean5 whitelist.
    assert!(
        result.is_err(),
        "QF_LIA proof should be rejected as unsupported"
    );
}
