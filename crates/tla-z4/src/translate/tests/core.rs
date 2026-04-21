// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_translate_bool_literal() {
    let mut trans = Z4Translator::new();

    let expr_true = spanned(Expr::Bool(true));
    let expr_false = spanned(Expr::Bool(false));

    let t = trans.translate_bool(&expr_true).unwrap();
    let _f = trans.translate_bool(&expr_false).unwrap();

    // Assert t and check SAT
    trans.assert(t);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));

    // Create new translator, assert false
    let mut trans2 = Z4Translator::new();
    let f2 = trans2.translate_bool(&expr_false).unwrap();
    trans2.assert(f2);
    assert!(matches!(trans2.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_translate_int_literal() {
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // x = 42
    let expr = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(42)))),
    ));

    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("x").cloned(), Some(bi(42)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tla_sort_to_z4_rejects_function_sort() {
    let sort = TlaSort::Function {
        domain_keys: vec!["k".to_string()],
        range: Box::new(TlaSort::Int),
    };

    let err = sort.to_z4().unwrap_err();
    assert!(matches!(err, Z4Error::UnsupportedOp(_)));
    assert!(
        err.to_string()
            .contains("Function sort cannot be directly converted"),
        "unexpected error: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tla_sort_to_z4_rejects_tuple_sort() {
    let sort = TlaSort::Tuple {
        element_sorts: vec![TlaSort::Int, TlaSort::Bool],
    };

    let err = sort.to_z4().unwrap_err();
    assert!(matches!(err, Z4Error::UnsupportedOp(_)));
    assert!(
        err.to_string()
            .contains("Tuple sort cannot be directly converted"),
        "unexpected error: {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_translate_rejects_non_linear_mul() {
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();
    trans.declare_var("y", TlaSort::Int).unwrap();

    let expr = spanned(Expr::Gt(
        Box::new(spanned(Expr::Mul(
            Box::new(spanned(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Ident(
                "y".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(0)))),
    ));

    let err = trans.translate_bool(&expr).unwrap_err();
    assert!(
        matches!(err, Z4Error::UnsupportedOp(_)),
        "expected UnsupportedOp, got {err:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_translate_and() {
    let mut trans = Z4Translator::new();

    // TRUE /\ FALSE should be UNSAT
    let expr = spanned(Expr::And(
        Box::new(spanned(Expr::Bool(true))),
        Box::new(spanned(Expr::Bool(false))),
    ));

    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_translate_or() {
    let mut trans = Z4Translator::new();

    // TRUE \/ FALSE should be SAT
    let expr = spanned(Expr::Or(
        Box::new(spanned(Expr::Bool(true))),
        Box::new(spanned(Expr::Bool(false))),
    ));

    let term = trans.translate_bool(&expr).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_translate_comparison() {
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // x > 5 /\ x < 3 should be UNSAT
    let gt = spanned(Expr::Gt(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));
    let lt = spanned(Expr::Lt(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(3)))),
    ));

    let gt_term = trans.translate_bool(&gt).unwrap();
    let lt_term = trans.translate_bool(&lt).unwrap();

    trans.assert(gt_term);
    trans.assert(lt_term);

    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_translate_arithmetic() {
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // x + 3 = 7 implies x = 4
    let sum = spanned(Expr::Add(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(3)))),
    ));
    let eq = spanned(Expr::Eq(
        Box::new(sum),
        Box::new(spanned(Expr::Int(BigInt::from(7)))),
    ));

    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("x").cloned(), Some(bi(4)));
}
