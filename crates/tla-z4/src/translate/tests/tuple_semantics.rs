// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// Phase 4: Tuple equality and membership (#517)
// =========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_equality_var_literal_sat() {
    // Test: t = <<1, 2>> where t is a declared tuple var
    let mut trans = Z4Translator::new();
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Tuple(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
        ]))),
    ));

    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("t__1").cloned(), Some(bi(1)));
    assert_eq!(model.int_val("t__2").cloned(), Some(bi(2)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_equality_literal_var_sat() {
    // Test: <<3, 4>> = t (literal on left, var on right)
    let mut trans = Z4Translator::new();
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Tuple(vec![
            spanned(Expr::Int(BigInt::from(3))),
            spanned(Expr::Int(BigInt::from(4))),
        ]))),
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert_eq!(model.int_val("t__1").cloned(), Some(bi(3)));
    assert_eq!(model.int_val("t__2").cloned(), Some(bi(4)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_equality_literal_literal_sat() {
    // Test: <<1, 2>> = <<1, 2>>
    let mut trans = Z4Translator::new();

    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Tuple(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
        ]))),
        Box::new(spanned(Expr::Tuple(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
        ]))),
    ));

    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_equality_literal_literal_unsat() {
    // Test: <<1, 2>> = <<1, 3>> should be UNSAT
    let mut trans = Z4Translator::new();

    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Tuple(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
        ]))),
        Box::new(spanned(Expr::Tuple(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(3))),
        ]))),
    ));

    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_membership_set_enum_sat() {
    // Test: t \in {<<1,2>>, <<3,4>>} with t = <<1,2>>
    let mut trans = Z4Translator::new();
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    // First constrain t = <<1, 2>>
    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Tuple(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
        ]))),
    ));
    let eq_term = trans.translate_bool(&eq).unwrap();
    trans.assert(eq_term);

    // Then check t \in {<<1,2>>, <<3,4>>}
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Tuple(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
            ])),
            spanned(Expr::Tuple(vec![
                spanned(Expr::Int(BigInt::from(3))),
                spanned(Expr::Int(BigInt::from(4))),
            ])),
        ]))),
    ));

    let mem_term = trans.translate_bool(&membership).unwrap();
    trans.assert(mem_term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_membership_set_enum_unsat() {
    // Test: t \in {<<1,2>>, <<3,4>>} with t = <<5,6>> should be UNSAT
    let mut trans = Z4Translator::new();
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    // First constrain t = <<5, 6>>
    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Tuple(vec![
            spanned(Expr::Int(BigInt::from(5))),
            spanned(Expr::Int(BigInt::from(6))),
        ]))),
    ));
    let eq_term = trans.translate_bool(&eq).unwrap();
    trans.assert(eq_term);

    // Then require t \in {<<1,2>>, <<3,4>>}
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Tuple(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
            ])),
            spanned(Expr::Tuple(vec![
                spanned(Expr::Int(BigInt::from(3))),
                spanned(Expr::Int(BigInt::from(4))),
            ])),
        ]))),
    ));

    let mem_term = trans.translate_bool(&membership).unwrap();
    trans.assert(mem_term);

    // Should be UNSAT because <<5,6>> is not in the set
    assert!(matches!(trans.check_sat(), SolveResult::Unsat(_)));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_membership_constraint_solving() {
    // Test: t \in {<<1,2>>, <<3,4>>} without prior constraint
    // Should find a valid tuple assignment
    let mut trans = Z4Translator::new();
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Tuple(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::Int(BigInt::from(2))),
            ])),
            spanned(Expr::Tuple(vec![
                spanned(Expr::Int(BigInt::from(3))),
                spanned(Expr::Int(BigInt::from(4))),
            ])),
        ]))),
    ));

    let mem_term = trans.translate_bool(&membership).unwrap();
    trans.assert(mem_term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let t1 = model.int_val("t__1").unwrap();
    let t2 = model.int_val("t__2").unwrap();
    // Should be either <<1,2>> or <<3,4>>
    assert!(
        (*t1 == bi(1) && *t2 == bi(2)) || (*t1 == bi(3) && *t2 == bi(4)),
        "Expected (1,2) or (3,4), got ({t1}, {t2})"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_equality_with_string_elements() {
    // Test: t = <<"a", "b">> with string elements
    let mut trans = Z4Translator::new();
    trans
        .declare_tuple_var("t", vec![TlaSort::String, TlaSort::String])
        .unwrap();

    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Tuple(vec![
            spanned(Expr::String("a".to_string())),
            spanned(Expr::String("b".to_string())),
        ]))),
    ));

    let term = trans.translate_bool(&eq).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    // "a" is interned as 1, "b" as 2
    assert_eq!(model.int_val("t__1").cloned(), Some(bi(1)));
    assert_eq!(model.int_val("t__2").cloned(), Some(bi(2)));
}

// =========================================================================
// Part of #525: Tuple membership edge cases
// =========================================================================

/// Test tuple arity mismatch: 2-element tuple vs 1-element tuples.
/// Fixed by #538: Returns FALSE (UNSAT) instead of error.
/// Per TLA+ semantics: <<1,2>> \in {<<1>>} is FALSE (different arity means not equal)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_membership_arity_mismatch_returns_false() {
    let mut trans = Z4Translator::new();
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    // t \in {<<1>>} - set contains 1-element tuples, t is 2-element
    // Since arity doesn't match, membership is FALSE for all values of t
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![spanned(Expr::Tuple(vec![
            spanned(Expr::Int(BigInt::from(1))),
        ]))]))),
    ));

    // Part of #538: This should now translate successfully and be UNSAT
    // (no 2-element tuple can be in a set of 1-element tuples)
    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);
    assert!(
        matches!(trans.check_sat(), SolveResult::Unsat(_)),
        "<<_,_>> \\in {{<<_>>}} should be UNSAT (arity mismatch => FALSE)"
    );
}

/// Test mixed element sorts in tuple-set enums.
/// `t \in {<<1,"a">>, <<2,"b">>}` should work with string interning.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_membership_mixed_sorts_sat() {
    let mut trans = Z4Translator::new();
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::String])
        .unwrap();

    // t \in {<<1,"a">>, <<2,"b">>}
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Tuple(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::String("a".to_string())),
            ])),
            spanned(Expr::Tuple(vec![
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::String("b".to_string())),
            ])),
        ]))),
    ));

    let mem_term = trans.translate_bool(&membership).unwrap();
    trans.assert(mem_term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));

    // Verify model has valid tuple from the set
    let model = trans.get_model().unwrap();
    let t1 = model.int_val("t__1").unwrap();
    let t2 = model.int_val("t__2").unwrap();

    // Should be either <<1,"a">> (t1=1, t2=intern("a")) or <<2,"b">> (t1=2, t2=intern("b"))
    // String "a" is interned first (ID=1), "b" second (ID=2)
    assert!(
        (*t1 == bi(1) && *t2 == bi(1)) || (*t1 == bi(2) && *t2 == bi(2)),
        "expected t to be <<1,1>> or <<2,2>> (with interned strings), got <<{t1},{t2}>>"
    );
}

/// Test mixed sorts with equality constraint.
/// Constrain t = <<2,"b">> and verify membership holds.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tuple_membership_mixed_sorts_with_equality() {
    let mut trans = Z4Translator::new();
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::String])
        .unwrap();

    // t \in {<<1,"a">>, <<2,"b">>}
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Tuple(vec![
                spanned(Expr::Int(BigInt::from(1))),
                spanned(Expr::String("a".to_string())),
            ])),
            spanned(Expr::Tuple(vec![
                spanned(Expr::Int(BigInt::from(2))),
                spanned(Expr::String("b".to_string())),
            ])),
        ]))),
    ));

    let mem_term = trans.translate_bool(&membership).unwrap();
    trans.assert(mem_term);

    // Also constrain t = <<2,"b">>
    let eq = spanned(Expr::Eq(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Tuple(vec![
            spanned(Expr::Int(BigInt::from(2))),
            spanned(Expr::String("b".to_string())),
        ]))),
    ));

    let eq_term = trans.translate_bool(&eq).unwrap();
    trans.assert(eq_term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));

    let model = trans.get_model().unwrap();
    // t must be <<2,"b">>
    assert_eq!(model.int_val("t__1").cloned(), Some(bi(2)));
    // "b" is interned as 2 (after "a" which is 1)
    assert_eq!(model.int_val("t__2").cloned(), Some(bi(2)));
}
