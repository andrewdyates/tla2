// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// Phase 3: String support tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_literal_equality_sat() {
    let mut trans = Z4Translator::new();
    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::String("hello".to_string()))),
        Box::new(spanned(Expr::String("hello".to_string()))),
    ));
    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_literal_inequality_unsat() {
    let mut trans = Z4Translator::new();
    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::String("hello".to_string()))),
        Box::new(spanned(Expr::String("world".to_string()))),
    ));
    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_variable() {
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::String).unwrap();
    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::String("hello".to_string()))),
    ));
    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("x").cloned(), Some(bi(1)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_literal_membership_sat() {
    let mut trans = Z4Translator::new();
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::String("hello".to_string()))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::String("hello".to_string())),
            spanned(Expr::String("world".to_string())),
        ]))),
    ));
    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_literal_membership_unsat() {
    let mut trans = Z4Translator::new();
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::String("nope".to_string()))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::String("hello".to_string())),
            spanned(Expr::String("world".to_string())),
        ]))),
    ));
    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_string_var_membership_sat() {
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::String).unwrap();
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::String("hello".to_string())),
            spanned(Expr::String("world".to_string())),
        ]))),
    ));
    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let x = model.int_val("x").unwrap();
    assert!(
        *x == bi(1) || *x == bi(2),
        "Expected x to be interned as 1 or 2, got {x}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_string_elem() {
    let mut trans = Z4Translator::new();
    trans
        .declare_tuple_var("p", vec![TlaSort::String, TlaSort::String, TlaSort::String])
        .unwrap();
    let p2 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "p".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(2)))),
    ));
    let eq = spanned(Expr::Eq(
        Box::new(p2),
        Box::new(spanned(Expr::String("mylk".to_string()))),
    ));
    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("p__2").cloned(), Some(bi(1)));
}
