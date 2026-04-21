// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// Phase 5: Cross-type semantics (#518)
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cross_type_equality_int_string_is_false() {
    // TLA+ semantics: 1 = "a" is FALSE (not an error)
    let mut trans = Z4Translator::new();

    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
        Box::new(spanned(Expr::String("a".to_string()))),
    ));

    let term = trans.translate_bool(&eq).unwrap();

    // Assert the negation of (1 = "a") - should be SAT since (1 = "a") is FALSE
    let neg = trans.solver.try_not(term).unwrap();
    trans.assert(neg);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cross_type_equality_string_int_is_false() {
    // TLA+ semantics: "a" = 1 is FALSE (not an error)
    let mut trans = Z4Translator::new();

    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::String("a".to_string()))),
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
    ));

    let term = trans.translate_bool(&eq).unwrap();

    // Assert the negation - should be SAT since ("a" = 1) is FALSE
    let neg = trans.solver.try_not(term).unwrap();
    trans.assert(neg);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cross_type_equality_int_bool_is_false() {
    // TLA+ semantics: 1 = TRUE is FALSE (not an error)
    let mut trans = Z4Translator::new();

    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
        Box::new(spanned(Expr::Bool(true))),
    ));

    let term = trans.translate_bool(&eq).unwrap();

    // Assert the negation - should be SAT since (1 = TRUE) is FALSE
    let neg = trans.solver.try_not(term).unwrap();
    trans.assert(neg);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cross_type_membership_int_in_string_set_is_false() {
    // TLA+ semantics: 1 \in {"a", "b"} is FALSE (not an error)
    let mut trans = Z4Translator::new();

    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::String("a".to_string())),
            spanned(Expr::String("b".to_string())),
        ]))),
    ));

    let term = trans.translate_bool(&membership).unwrap();

    // Assert the negation - should be SAT since (1 \in {"a", "b"}) is FALSE
    let neg = trans.solver.try_not(term).unwrap();
    trans.assert(neg);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cross_type_membership_string_in_int_set_is_false() {
    // TLA+ semantics: "a" \in {1, 2} is FALSE (not an error)
    let mut trans = Z4Translator::new();

    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::String("a".to_string()))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
        ]))),
    ));

    let term = trans.translate_bool(&membership).unwrap();

    // Assert the negation - should be SAT since ("a" \in {1, 2}) is FALSE
    let neg = trans.solver.try_not(term).unwrap();
    trans.assert(neg);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cross_type_var_equality_int_var_string_literal() {
    // TLA+ semantics: x = "a" where x is Int should be FALSE
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::String("a".to_string()))),
    ));

    let term = trans.translate_bool(&eq).unwrap();

    // Assert the negation - should be SAT since (x:Int = "a") is FALSE
    let neg = trans.solver.try_not(term).unwrap();
    trans.assert(neg);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cross_type_var_membership_int_var_in_string_set() {
    // TLA+ semantics: x \in {"a", "b"} where x is Int should be FALSE
    let mut trans = Z4Translator::new();
    trans.declare_var("x", TlaSort::Int).unwrap();

    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::String("a".to_string())),
            spanned(Expr::String("b".to_string())),
        ]))),
    ));

    let term = trans.translate_bool(&membership).unwrap();

    // Assert the negation - should be SAT since (x:Int \in {"a", "b"}) is FALSE
    let neg = trans.solver.try_not(term).unwrap();
    trans.assert(neg);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

// =========================================================================
// Phase 5b: Self-audit fixes (#518 audit round 1)
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cross_type_neq_int_string_is_true() {
    // TLA+ semantics: 1 /= "a" is TRUE (since 1 = "a" is FALSE)
    let mut trans = Z4Translator::new();

    let neq = spanned(Expr::Neq(
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
        Box::new(spanned(Expr::String("a".to_string()))),
    ));

    let term = trans.translate_bool(&neq).unwrap();
    trans.assert(term);

    // 1 /= "a" should be TRUE, so asserting it should be SAT
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_heterogeneous_set_membership_int_in_mixed_set() {
    // TLA+ semantics: 1 \in {1, "a"} is TRUE (1 equals the Int element)
    let mut trans = Z4Translator::new();

    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Int(BigInt::from(1)))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::String("a".to_string())),
        ]))),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    // Should be SAT since 1 is in the set
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_heterogeneous_set_membership_string_in_mixed_set() {
    // TLA+ semantics: "a" \in {1, "a"} is TRUE (matches the String element)
    let mut trans = Z4Translator::new();

    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::String("a".to_string()))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::String("a".to_string())),
        ]))),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    // Should be SAT since "a" is in the set
    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_var_eq_scalar_is_false() {
    // TLA+ semantics: tuple_var = 5 is FALSE (type mismatch)
    let mut trans = Z4Translator::new();
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Int(BigInt::from(5)))),
    ));

    let term = trans.translate_bool(&eq).unwrap();

    // Assert the negation - should be SAT since (t = 5) is FALSE
    let neg = trans.solver.try_not(term).unwrap();
    trans.assert(neg);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_cross_type_equality_bool_string_is_false() {
    // TLA+ semantics: TRUE = "a" is FALSE (type mismatch)
    let mut trans = Z4Translator::new();

    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Bool(true))),
        Box::new(spanned(Expr::String("a".to_string()))),
    ));

    let term = trans.translate_bool(&eq).unwrap();

    // Assert the negation - should be SAT since (TRUE = "a") is FALSE
    let neg = trans.solver.try_not(term).unwrap();
    trans.assert(neg);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}
