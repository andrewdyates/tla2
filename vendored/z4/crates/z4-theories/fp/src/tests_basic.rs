// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use z4_core::Sort;

#[test]
fn test_fp_precision() {
    assert_eq!(FpPrecision::Float32.exponent_bits(), 8);
    assert_eq!(FpPrecision::Float32.significand_bits(), 24);
    assert_eq!(FpPrecision::Float32.total_bits(), 32);
    assert_eq!(FpPrecision::Float32.bias(), 127);

    assert_eq!(FpPrecision::Float64.exponent_bits(), 11);
    assert_eq!(FpPrecision::Float64.significand_bits(), 53);
    assert_eq!(FpPrecision::Float64.total_bits(), 64);
    assert_eq!(FpPrecision::Float64.bias(), 1023);
}

#[test]
fn test_rounding_modes() {
    assert_eq!(RoundingMode::from_name("RNE"), Some(RoundingMode::RNE));
    assert_eq!(
        RoundingMode::from_name("roundNearestTiesToEven"),
        Some(RoundingMode::RNE)
    );
    assert_eq!(RoundingMode::from_name("RTZ"), Some(RoundingMode::RTZ));
    assert_eq!(RoundingMode::from_name("invalid"), None);
}

#[test]
fn test_make_zero() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);

    let pos_zero = solver.make_zero(FpPrecision::Float32, false);
    assert_eq!(pos_zero.exponent.len(), 8);
    assert_eq!(pos_zero.significand.len(), 23);

    let neg_zero = solver.make_zero(FpPrecision::Float32, true);
    assert_eq!(neg_zero.exponent.len(), 8);
}

#[test]
fn test_make_infinity() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);

    let pos_inf = solver.make_infinity(FpPrecision::Float64, false);
    assert_eq!(pos_inf.exponent.len(), 11);
    assert_eq!(pos_inf.significand.len(), 52);
}

#[test]
fn test_make_nan() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);

    let nan = solver.make_nan_value(FpPrecision::Float32);
    assert_eq!(nan.exponent.len(), 8);
    assert_eq!(nan.significand.len(), 23);
}

#[test]
fn test_classification_predicates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 24));

    let mut solver = FpSolver::new(&terms);

    let is_nan = solver.bitblast_is_nan(x);
    assert!(is_nan != 0);

    let is_inf = solver.bitblast_is_infinite(x);
    assert!(is_inf != 0);

    let is_zero = solver.bitblast_is_zero(x);
    assert!(is_zero != 0);
}

#[test]
fn test_comparison_predicates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 24));
    let y = terms.mk_var("y", Sort::FloatingPoint(8, 24));

    let mut solver = FpSolver::new(&terms);

    let eq = solver.bitblast_fp_eq(x, y);
    assert!(eq != 0);

    let lt = solver.bitblast_fp_lt(x, y);
    assert!(lt != 0);
}

#[test]
fn test_cnf_generation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 24));

    let mut solver = FpSolver::new(&terms);
    let _ = solver.bitblast_is_nan(x);

    let clauses = solver.clauses();
    assert!(!clauses.is_empty());
}

#[test]
fn test_arithmetic_special_cases() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 24));
    let y = terms.mk_var("y", Sort::FloatingPoint(8, 24));

    let mut solver = FpSolver::new(&terms);

    let fp_x = solver.get_fp(x);
    let fp_y = solver.get_fp(y);

    let _ = solver.make_add(&fp_x, &fp_y, RoundingMode::RNE);
    assert!(!solver.clauses().is_empty());

    let _ = solver.make_mul(&fp_x, &fp_y, RoundingMode::RTZ);
    let _ = solver.make_div(&fp_x, &fp_y, RoundingMode::RTP);
    let _ = solver.make_sqrt(&fp_x, RoundingMode::RTN);
}

#[test]
fn test_negation_and_abs() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 24));

    let mut solver = FpSolver::new(&terms);
    let fp_x = solver.get_fp(x);

    let neg_x = solver.make_neg(&fp_x);
    assert_eq!(neg_x.precision, FpPrecision::Float32);

    let abs_x = solver.make_abs(&fp_x);
    assert_eq!(abs_x.precision, FpPrecision::Float32);
}

#[test]
fn test_min_max() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 24));
    let y = terms.mk_var("y", Sort::FloatingPoint(8, 24));

    let mut solver = FpSolver::new(&terms);
    let fp_x = solver.get_fp(x);
    let fp_y = solver.get_fp(y);

    let min_xy = solver.make_min(&fp_x, &fp_y);
    assert_eq!(min_xy.precision, FpPrecision::Float32);

    let max_xy = solver.make_max(&fp_x, &fp_y);
    assert_eq!(max_xy.precision, FpPrecision::Float32);
}

#[test]
fn test_float16() {
    assert_eq!(FpPrecision::Float16.exponent_bits(), 5);
    assert_eq!(FpPrecision::Float16.significand_bits(), 11);
    assert_eq!(FpPrecision::Float16.total_bits(), 16);
    assert_eq!(FpPrecision::Float16.bias(), 15);
}

#[test]
fn test_float128() {
    assert_eq!(FpPrecision::Float128.exponent_bits(), 15);
    assert_eq!(FpPrecision::Float128.significand_bits(), 113);
    assert_eq!(FpPrecision::Float128.total_bits(), 128);
    assert_eq!(FpPrecision::Float128.bias(), 16383);
}

#[test]
fn test_custom_precision() {
    let custom = FpPrecision::Custom { eb: 6, sb: 10 };
    assert_eq!(custom.exponent_bits(), 6);
    assert_eq!(custom.significand_bits(), 10);
    assert_eq!(custom.total_bits(), 16);
    assert_eq!(custom.bias(), 31);

    assert_eq!(FpPrecision::from_eb_sb(8, 24), FpPrecision::Float32);
    assert_eq!(FpPrecision::from_eb_sb(11, 53), FpPrecision::Float64);
    assert!(matches!(
        FpPrecision::from_eb_sb(6, 10),
        FpPrecision::Custom { .. }
    ));
}
