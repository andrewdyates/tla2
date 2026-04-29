// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// Phase 2: Tuple translation tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_declare_tuple_var() {
    let mut trans = Z4Translator::new();

    // Declare t : <<Int, Int, Bool>>
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int, TlaSort::Bool])
        .unwrap();

    // Verify tuple info is stored
    let info = trans.get_tuple_var("t").unwrap();
    assert_eq!(info.element_sorts.len(), 3);
    assert_eq!(info.element_sorts[0], TlaSort::Int);
    assert_eq!(info.element_sorts[1], TlaSort::Int);
    assert_eq!(info.element_sorts[2], TlaSort::Bool);
    assert!(info.element_terms.contains_key(&1));
    assert!(info.element_terms.contains_key(&2));
    assert!(info.element_terms.contains_key(&3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_element_vars_are_scalar_idents() {
    let mut trans = Z4Translator::new();

    // Declare t : <<Int, Int>> which creates t__1 and t__2
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    // Directly constrain t__1 = 42 using an identifier expression
    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "t__1".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(42)))),
    ));

    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("t__1").cloned(), Some(bi(42)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_apply_constant_index() {
    let mut trans = Z4Translator::new();

    // Declare t : <<Int, Int, Int>>
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int, TlaSort::Int])
        .unwrap();

    // Assert t[1] = 10, t[2] = 20, t[3] = 30
    for (idx, val) in [(1, 10), (2, 20), (3, 30)] {
        let tuple_apply = spanned(Expr::FuncApply(
            Box::new(spanned(Expr::Ident(
                "t".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(idx)))),
        ));
        let eq = spanned(Expr::Eq(
            Box::new(tuple_apply),
            Box::new(spanned(Expr::Int(BigInt::from(val)))),
        ));

        let term = trans.translate_bool(&eq).unwrap();
        trans.assert(term);
    }

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("t__1").cloned(), Some(bi(10)));
    assert_eq!(model.int_val("t__2").cloned(), Some(bi(20)));
    assert_eq!(model.int_val("t__3").cloned(), Some(bi(30)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_with_constraint() {
    let mut trans = Z4Translator::new();

    // Declare t : <<Int, Int, Int>>
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int, TlaSort::Int])
        .unwrap();

    // Constraint: t[1] + t[2] = t[3]
    let t1 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));
    let t2 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(2)))),
    ));
    let t3 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(3)))),
    ));

    let sum = spanned(Expr::Add(Box::new(t1), Box::new(t2)));
    let eq = spanned(Expr::Eq(Box::new(sum), Box::new(t3)));

    let constraint = trans.translate_bool(&eq).unwrap();
    trans.assert(constraint);

    // Also constrain elements to be in 1..10
    for idx in 1..=3 {
        let elem = spanned(Expr::FuncApply(
            Box::new(spanned(Expr::Ident(
                "t".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(spanned(Expr::Int(BigInt::from(idx)))),
        ));
        let in_range = spanned(Expr::In(
            Box::new(elem),
            Box::new(spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(10)))),
            ))),
        ));
        let term = trans.translate_bool(&in_range).unwrap();
        trans.assert(term);
    }

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let v1 = model.int_val("t__1").unwrap();
    let v2 = model.int_val("t__2").unwrap();
    let v3 = model.int_val("t__3").unwrap();
    assert_eq!(v1 + v2, v3.clone(), "t[1] + t[2] should equal t[3]");
    assert!((bi(1)..=bi(10)).contains(v1));
    assert!((bi(1)..=bi(10)).contains(v2));
    assert!((bi(1)..=bi(10)).contains(v3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_with_bool_element() {
    let mut trans = Z4Translator::new();

    // Declare t : <<Int, Bool, Int>>
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Bool, TlaSort::Int])
        .unwrap();

    // Assert t[2] = TRUE (Bool element)
    let t2 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(2)))),
    ));
    let eq = spanned(Expr::Eq(Box::new(t2), Box::new(spanned(Expr::Bool(true)))));

    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.bool_val("t__2"), Some(true));
}
