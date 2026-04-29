// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// NOTE(#553): z4-dpll's QF_LIA does not currently solve `div`/`mod` terms.
// For BMC we keep correctness by only translating constant `\\div` and `%`
// via constant-folding, and rejecting non-constant uses.

/// IntDiv (\\div) on constants: 17 \\div 5 = 3
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_intdiv_constants() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::IntDiv(
            Box::new(spanned(Expr::Int(BigInt::from(17)))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        ))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    let safety = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(3)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// IntDiv (\\div) on constants with negative dividend: -17 \\div 5 = -4
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_intdiv_constants_negative_dividend() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::IntDiv(
            Box::new(spanned(Expr::Int(BigInt::from(-17)))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        ))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    let safety = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(-4)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// Mod (%) on constants: 17 % 5 = 2
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_mod_constants() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Mod(
            Box::new(spanned(Expr::Int(BigInt::from(17)))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        ))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    let safety = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(2)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// Mod (%) on constants with negative dividend: -17 % 5 = 3
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_mod_constants_negative_dividend() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let init = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Mod(
            Box::new(spanned(Expr::Int(BigInt::from(-17)))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        ))),
    ));
    let init_term = trans.translate_init(&init).unwrap();
    trans.assert(init_term);

    let safety = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(3)))),
    ));
    let not_safety = trans.translate_not_safety_all_steps(&safety, k).unwrap();
    trans.assert(not_safety);

    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

/// IntDiv with non-constant divisor is rejected (cannot linearize).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_intdiv_nonconstant_divisor_rejected() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();

    // x \div y (non-constant divisor) should be rejected
    let div_expr = spanned(Expr::IntDiv(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    assert!(trans.translate_int(&div_expr).is_err());
}

/// Mod with non-constant divisor is rejected (cannot linearize).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_mod_nonconstant_divisor_rejected() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();

    // x % y (non-constant divisor) should be rejected
    let mod_expr = spanned(Expr::Mod(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));
    assert!(trans.translate_int(&mod_expr).is_err());
}

/// IntDiv with negative constant divisor is rejected (linearization requires k > 0).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_intdiv_negative_divisor_rejected() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();

    // x \div -5 should be rejected
    let div_expr = spanned(Expr::IntDiv(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(-5)))),
    ));
    assert!(trans.translate_int(&div_expr).is_err());
}

/// IntDiv with zero divisor is rejected (division by zero).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_intdiv_zero_divisor_rejected() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();

    // x \div 0 should be rejected as division by zero
    let div_expr = spanned(Expr::IntDiv(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));
    assert!(trans.translate_int(&div_expr).is_err());
}

/// Mod with zero divisor is rejected (TLC requires divisor > 0).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_mod_zero_divisor_rejected() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();

    // x % 0 should be rejected (divisor must be > 0)
    let mod_expr = spanned(Expr::Mod(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));
    assert!(trans.translate_int(&mod_expr).is_err());
}

/// Mod with negative divisor is rejected (TLC requires divisor > 0).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_mod_negative_divisor_rejected() {
    let k = 0;
    let mut trans = BmcTranslator::new(k).unwrap();
    trans.declare_var("x", TlaSort::Int).unwrap();

    // x % -5 should be rejected (divisor must be > 0)
    let mod_expr = spanned(Expr::Mod(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(-5)))),
    ));
    assert!(trans.translate_int(&mod_expr).is_err());
}
