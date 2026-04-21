// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;

use super::lia::{validate_lia_theory_lemma, LiaValidationError};
use crate::{CuttingPlaneAnnotation, FarkasAnnotation, LiaAnnotation, ProofId, Sort, TermStore};

#[test]
fn test_bounds_gap_simple_contradiction() {
    // x <= 5 AND x >= 10 is contradictory
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);

    // Blocking clause: {NOT(x <= 5), NOT(x >= 10)}
    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);
    let clause = vec![not_x_le_5, not_x_ge_10];

    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let lia = LiaAnnotation::BoundsGap;

    let result = validate_lia_theory_lemma(&terms, ProofId(0), &clause, Some(&farkas), &lia);
    assert!(result.is_ok(), "bounds gap should validate: {result:?}");
}

#[test]
fn test_bounds_gap_missing_farkas_returns_error() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let x_le_5 = terms.mk_le(x, five);
    let not_x_le_5 = terms.mk_not(x_le_5);
    let clause = vec![not_x_le_5];

    let lia = LiaAnnotation::BoundsGap;
    let result = validate_lia_theory_lemma(&terms, ProofId(0), &clause, None, &lia);
    assert!(
        matches!(
            result,
            Err(LiaValidationError::MissingFarkas { shape: "BoundsGap" })
        ),
        "expected MissingFarkas error, got: {result:?}"
    );
}

#[test]
fn test_divisibility_accepts_nonempty_clause() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let x_le_3 = terms.mk_le(x, three);
    let not_x_le_3 = terms.mk_not(x_le_3);

    let lia = LiaAnnotation::Divisibility;
    let result = validate_lia_theory_lemma(&terms, ProofId(0), &[not_x_le_3], None, &lia);
    assert!(
        result.is_ok(),
        "divisibility should accept non-empty clause: {result:?}"
    );
}

#[test]
fn test_divisibility_rejects_empty_clause() {
    let terms = TermStore::new();
    let lia = LiaAnnotation::Divisibility;
    let result = validate_lia_theory_lemma(&terms, ProofId(0), &[], None, &lia);
    assert!(result.is_err(), "divisibility should reject empty clause");
}

#[test]
fn test_cutting_plane_valid_divisor() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);
    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);
    let clause = vec![not_x_le_5, not_x_ge_10];

    let cp = CuttingPlaneAnnotation {
        farkas: FarkasAnnotation::from_ints(&[1, 1]),
        divisor: 2,
    };
    let lia = LiaAnnotation::CuttingPlane(cp);

    let result = validate_lia_theory_lemma(&terms, ProofId(0), &clause, None, &lia);
    assert!(
        result.is_ok(),
        "cutting plane with valid divisor should pass: {result:?}"
    );
}

#[test]
fn test_cutting_plane_zero_divisor_rejected() {
    let terms = TermStore::new();
    let cp = CuttingPlaneAnnotation {
        farkas: FarkasAnnotation::from_ints(&[]),
        divisor: 0,
    };
    let lia = LiaAnnotation::CuttingPlane(cp);

    let result = validate_lia_theory_lemma(&terms, ProofId(0), &[], None, &lia);
    assert!(
        matches!(
            result,
            Err(LiaValidationError::InvalidDivisor { divisor: 0 })
        ),
        "expected InvalidDivisor, got: {result:?}"
    );
}

#[test]
fn test_cutting_plane_negative_divisor_rejected() {
    let terms = TermStore::new();
    let cp = CuttingPlaneAnnotation {
        farkas: FarkasAnnotation::from_ints(&[]),
        divisor: -3,
    };
    let lia = LiaAnnotation::CuttingPlane(cp);

    let result = validate_lia_theory_lemma(&terms, ProofId(0), &[], None, &lia);
    assert!(
        matches!(
            result,
            Err(LiaValidationError::InvalidDivisor { divisor: -3 })
        ),
        "expected InvalidDivisor, got: {result:?}"
    );
}
