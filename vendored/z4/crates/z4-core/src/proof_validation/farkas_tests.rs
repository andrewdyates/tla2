// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;

use super::{verify_farkas_conflict_lits_full, FarkasValidationError};
use crate::{FarkasAnnotation, Sort, TermStore, TheoryLit};

#[test]
fn test_verify_farkas_conflict_lits_full_accepts_simple_bounds_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);

    let conflict = vec![TheoryLit::new(x_le_5, true), TheoryLit::new(x_ge_10, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);

    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("simple bounds conflict should validate");
}

#[test]
fn test_verify_farkas_conflict_lits_full_accepts_equality_orientation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));

    let x_eq_0 = terms.mk_eq(x, zero);
    let x_ge_1 = terms.mk_ge(x, one);

    let conflict = vec![TheoryLit::new(x_eq_0, true), TheoryLit::new(x_ge_1, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);

    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("equality orientation should validate");
}

#[test]
fn test_verify_farkas_conflict_lits_full_rejects_bad_coefficients() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);

    let conflict = vec![TheoryLit::new(x_le_5, true), TheoryLit::new(x_ge_10, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 0]);

    let err = verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect_err("invalid coefficients should be rejected");
    assert!(
        matches!(err, FarkasValidationError::VariablesNotEliminated { .. }),
        "unexpected error: {err:?}"
    );
}
