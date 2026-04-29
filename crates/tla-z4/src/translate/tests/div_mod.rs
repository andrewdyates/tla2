// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// Floor division and modulo tests (#631)
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_floor_div_negative_dividend() {
    // TLA+: -17 div 5 = -4 (floor), not -3 (truncating)
    let mut trans = Z4Translator::new();
    trans.declare_var("result", TlaSort::Int).unwrap();

    let div_expr = spanned(Expr::IntDiv(
        Box::new(spanned(Expr::Int(BigInt::from(-17)))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let eq_expr = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "result".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(div_expr),
    ));

    let term = trans.translate_bool(&eq_expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("result").cloned(), Some(bi(-4)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_floor_div_positive_dividend() {
    // TLA+: 17 div 5 = 3 (same as truncating)
    let mut trans = Z4Translator::new();
    trans.declare_var("result", TlaSort::Int).unwrap();

    let div_expr = spanned(Expr::IntDiv(
        Box::new(spanned(Expr::Int(BigInt::from(17)))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let eq_expr = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "result".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(div_expr),
    ));

    let term = trans.translate_bool(&eq_expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("result").cloned(), Some(bi(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_floor_div_negative_divisor() {
    // TLA+: 17 div -5 = -4 (floor), not -3 (truncating)
    let mut trans = Z4Translator::new();
    trans.declare_var("result", TlaSort::Int).unwrap();

    let div_expr = spanned(Expr::IntDiv(
        Box::new(spanned(Expr::Int(BigInt::from(17)))),
        Box::new(spanned(Expr::Int(BigInt::from(-5)))),
    ));
    let eq_expr = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "result".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(div_expr),
    ));

    let term = trans.translate_bool(&eq_expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("result").cloned(), Some(bi(-4)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_floor_div_both_negative() {
    // TLA+: -17 div -5 = 3 (floor(3.4) = 3)
    let mut trans = Z4Translator::new();
    trans.declare_var("result", TlaSort::Int).unwrap();

    let div_expr = spanned(Expr::IntDiv(
        Box::new(spanned(Expr::Int(BigInt::from(-17)))),
        Box::new(spanned(Expr::Int(BigInt::from(-5)))),
    ));
    let eq_expr = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "result".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(div_expr),
    ));

    let term = trans.translate_bool(&eq_expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("result").cloned(), Some(bi(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_floor_mod_negative_dividend() {
    // TLA+: -17 % 5 = 3 (always non-negative for positive divisor)
    let mut trans = Z4Translator::new();
    trans.declare_var("result", TlaSort::Int).unwrap();

    let mod_expr = spanned(Expr::Mod(
        Box::new(spanned(Expr::Int(BigInt::from(-17)))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let eq_expr = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "result".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(mod_expr),
    ));

    let term = trans.translate_bool(&eq_expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("result").cloned(), Some(bi(3)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_floor_mod_positive_dividend() {
    // TLA+: 17 % 5 = 2 (same as truncating)
    let mut trans = Z4Translator::new();
    trans.declare_var("result", TlaSort::Int).unwrap();

    let mod_expr = spanned(Expr::Mod(
        Box::new(spanned(Expr::Int(BigInt::from(17)))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let eq_expr = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "result".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(mod_expr),
    ));

    let term = trans.translate_bool(&eq_expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("result").cloned(), Some(bi(2)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_floor_div_exact_negative_dividend() {
    // TLA+: -20 div 5 = -4 (exact division, no remainder)
    let mut trans = Z4Translator::new();
    trans.declare_var("result", TlaSort::Int).unwrap();

    let div_expr = spanned(Expr::IntDiv(
        Box::new(spanned(Expr::Int(BigInt::from(-20)))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let eq_expr = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "result".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(div_expr),
    ));

    let term = trans.translate_bool(&eq_expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("result").cloned(), Some(bi(-4)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_floor_mod_exact_zero() {
    // TLA+: -20 % 5 = 0 (exact division, remainder is zero)
    let mut trans = Z4Translator::new();
    trans.declare_var("result", TlaSort::Int).unwrap();

    let mod_expr = spanned(Expr::Mod(
        Box::new(spanned(Expr::Int(BigInt::from(-20)))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let eq_expr = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "result".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(mod_expr),
    ));

    let term = trans.translate_bool(&eq_expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("result").cloned(), Some(bi(0)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_floor_div_exact_negative_divisor() {
    // TLA+: -20 div -5 = 4 (exact division, no remainder, negative divisor)
    // Tests that r_neg=true but has_remainder=false → no adjustment.
    let mut trans = Z4Translator::new();
    trans.declare_var("result", TlaSort::Int).unwrap();

    let div_expr = spanned(Expr::IntDiv(
        Box::new(spanned(Expr::Int(BigInt::from(-20)))),
        Box::new(spanned(Expr::Int(BigInt::from(-5)))),
    ));
    let eq_expr = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "result".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(div_expr),
    ));

    let term = trans.translate_bool(&eq_expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("result").cloned(), Some(bi(4)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_floor_mod_negative_divisor() {
    // TLA+ modulo requires positive divisor (TLC semantics, #554).
    // Literal negative divisor must be rejected at translation time.
    let mut trans = Z4Translator::new();

    let mod_expr = spanned(Expr::Mod(
        Box::new(spanned(Expr::Int(BigInt::from(17)))),
        Box::new(spanned(Expr::Int(BigInt::from(-5)))),
    ));

    let result = trans.translate_int(&mod_expr);
    assert!(result.is_err(), "negative divisor modulo should error");
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("positive divisor"),
        "error should mention positive divisor requirement, got: {err_msg}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_floor_div_of_zero() {
    // TLA+: 0 div 5 = 0 and 0 div -5 = 0
    // Division of zero by any nonzero value is zero.
    let mut trans = Z4Translator::new();
    trans.declare_var("r1", TlaSort::Int).unwrap();
    trans.declare_var("r2", TlaSort::Int).unwrap();

    // 0 div 5 = 0
    let div1 = spanned(Expr::IntDiv(
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let eq1 = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "r1".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(div1),
    ));

    // 0 div -5 = 0
    let div2 = spanned(Expr::IntDiv(
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
        Box::new(spanned(Expr::Int(BigInt::from(-5)))),
    ));
    let eq2 = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "r2".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(div2),
    ));

    let t1 = trans.translate_bool(&eq1).unwrap();
    let t2 = trans.translate_bool(&eq2).unwrap();
    trans.assert(t1);
    trans.assert(t2);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("r1").cloned(), Some(bi(0)));
    assert_eq!(model.int_val("r2").cloned(), Some(bi(0)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_floor_div_by_zero_error() {
    // Division by literal zero must be rejected at translation time.
    let mut trans = Z4Translator::new();

    let div_expr = spanned(Expr::IntDiv(
        Box::new(spanned(Expr::Int(BigInt::from(17)))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));

    let result = trans.translate_int(&div_expr);
    assert!(result.is_err(), "division by zero should error");
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("Division by zero"),
        "error should mention division by zero, got: {err_msg}"
    );
}
