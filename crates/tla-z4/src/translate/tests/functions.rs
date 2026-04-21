// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// Phase 2b: Function translation tests
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_declare_func_var() {
    let mut trans = Z4Translator::new();

    // Declare f : {1, 2} -> Int
    trans
        .declare_func_var("f", vec!["1".to_string(), "2".to_string()], TlaSort::Int)
        .unwrap();

    // Verify function info is stored
    let info = trans.get_func_var("f").unwrap();
    assert_eq!(info.domain_keys, vec!["1".to_string(), "2".to_string()]);
    assert_eq!(info.range_sort, TlaSort::Int);
    assert!(info.element_terms.contains_key("1"));
    assert!(info.element_terms.contains_key("2"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_element_vars_are_scalar_idents() {
    let mut trans = Z4Translator::new();

    // Declare f : {1, 2} -> Int, which creates f__1 and f__2
    trans
        .declare_func_var("f", vec!["1".to_string(), "2".to_string()], TlaSort::Int)
        .unwrap();

    // Directly constrain f__1 = 42 using an identifier expression.
    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "f__1".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(42)))),
    ));

    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("f__1").cloned(), Some(bi(42)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_apply_constant_arg() {
    let mut trans = Z4Translator::new();

    // Declare f : {1, 2} -> Int
    trans
        .declare_func_var("f", vec!["1".to_string(), "2".to_string()], TlaSort::Int)
        .unwrap();

    // Assert f[1] = 42
    let func_apply = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));
    let eq = spanned(Expr::Eq(
        Box::new(func_apply),
        Box::new(spanned(Expr::Int(BigInt::from(42)))),
    ));

    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("f__1").cloned(), Some(bi(42)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_set_membership() {
    let mut trans = Z4Translator::new();

    // f \in [{1, 2} -> 0..10]
    // This means f__1 \in 0..10 /\ f__2 \in 0..10
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::FuncSet(
            Box::new(spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
            ]))),
            Box::new(spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(0)))),
                Box::new(spanned(Expr::Int(BigInt::from(10)))),
            ))),
        ))),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let f1 = model.int_val("f__1").unwrap();
    let f2 = model.int_val("f__2").unwrap();
    assert!((bi(0)..=bi(10)).contains(f1));
    assert!((bi(0)..=bi(10)).contains(f2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_set_membership_with_constraint() {
    let mut trans = Z4Translator::new();

    // f \in [{1, 2, 3} -> 0..100] /\ f[1] + f[2] = f[3]
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::FuncSet(
            Box::new(spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::Int(BigInt::from(3))),
            ]))),
            Box::new(spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(0)))),
                Box::new(spanned(Expr::Int(BigInt::from(100)))),
            ))),
        ))),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    // f[1] + f[2] = f[3]
    let f1 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));
    let f2 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(2)))),
    ));
    let f3 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(3)))),
    ));

    let sum = spanned(Expr::Add(Box::new(f1), Box::new(f2)));
    let eq = spanned(Expr::Eq(Box::new(sum), Box::new(f3)));

    let constraint = trans.translate_bool(&eq).unwrap();
    trans.assert(constraint);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let v1 = model.int_val("f__1").unwrap();
    let v2 = model.int_val("f__2").unwrap();
    let v3 = model.int_val("f__3").unwrap();
    assert_eq!(&(v1 + v2), v3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_boolean_range() {
    let mut trans = Z4Translator::new();

    // f \in [{1, 2} -> BOOLEAN]
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::FuncSet(
            Box::new(spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
            ]))),
            Box::new(spanned(Expr::Ident(
                "BOOLEAN".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        ))),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    // This should be satisfiable - any assignment of booleans works
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_range_domain() {
    let mut trans = Z4Translator::new();

    // f \in [1..3 -> {0, 1}]
    // Domain: 1, 2, 3
    // Range: 0 or 1
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::FuncSet(
            Box::new(spanned(Expr::Range(
                Box::new(spanned(Expr::Int(BigInt::from(1)))),
                Box::new(spanned(Expr::Int(BigInt::from(3)))),
            ))),
            Box::new(spanned(Expr::SetEnum(vec![
                spanned(Expr::Int(BigInt::from(0))),
                spanned(Expr::Int(BigInt::from(1))),
            ]))),
        ))),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();

    // Each f__i should be 0 or 1
    for i in 1..=3 {
        let key = format!("f__{i}");
        let val = model.int_val(&key).unwrap();
        assert!(
            *val == bi(0) || *val == bi(1),
            "f__{i}={val} should be 0 or 1"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_func_unsatisfiable_constraint() {
    let mut trans = Z4Translator::new();

    // f \in [{1} -> {5}] /\ f[1] = 10
    // This is UNSAT because f[1] must be 5 but we assert it equals 10
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::FuncSet(
            Box::new(spanned(Expr::SetEnum(vec![spanned(Expr::Int(
                BigInt::from(1),
            ))]))),
            Box::new(spanned(Expr::SetEnum(vec![spanned(Expr::Int(
                BigInt::from(5),
            ))]))),
        ))),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    // f[1] = 10
    let f1 = spanned(Expr::FuncApply(
        Box::new(spanned(Expr::Ident(
            "f".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));
    let eq = spanned(Expr::Eq(
        Box::new(f1),
        Box::new(spanned(Expr::Int(BigInt::from(10)))),
    ));

    let constraint = trans.translate_bool(&eq).unwrap();
    trans.assert(constraint);

    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}
