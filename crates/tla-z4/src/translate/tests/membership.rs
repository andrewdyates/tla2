// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::collections::HashMap;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_translate_set_membership() {
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // x \in {1, 2, 3}
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::SetEnum(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
            spanned(Expr::Int(BigInt::from(3))),
        ]))),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let x = model.int_val("x").unwrap();
    assert!((bi(1)..=bi(3)).contains(x));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_translate_range_membership() {
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // x \in 1..5
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Range(
            Box::new(spanned(Expr::Int(BigInt::from(1)))),
            Box::new(spanned(Expr::Int(BigInt::from(5)))),
        ))),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let x = model.int_val("x").unwrap();
    assert!((bi(1)..=bi(5)).contains(x));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_translate_boolean_membership() {
    let mut trans = Z4Translator::new();

    trans.declare_var("b", TlaSort::Bool).unwrap();

    // b \in BOOLEAN
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "b".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "BOOLEAN".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    assert!(model.bool_val("b").is_some());
}

/// Part of #522: Test that Ident references to constant definitions are resolved.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_membership_ident_resolution() {
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // Define constant: MySet == {1, 2, 3}
    let myset_def = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
    ]));
    let mut defs = HashMap::new();
    defs.insert("MySet".to_string(), myset_def);
    trans.set_constant_defs(defs);

    // x \in MySet (where MySet is an Ident reference to the constant)
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "MySet".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let x = model.int_val("x").unwrap();
    assert!(
        (bi(1)..=bi(3)).contains(x),
        "x should be in {{1, 2, 3}}, got {x}"
    );
}

/// Part of #522: Test Ident resolution with tuple sets.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_membership_ident_tuple_set() {
    let mut trans = Z4Translator::new();

    // Declare tuple variable
    trans
        .declare_tuple_var("t", vec![TlaSort::Int, TlaSort::Int])
        .unwrap();

    // Define constant: TupleSet == {<<1, 2>>, <<3, 4>>}
    let tupleset_def = spanned(Expr::SetEnum(vec![
        spanned(Expr::Tuple(vec![
            spanned(Expr::Int(BigInt::from(1))),
            spanned(Expr::Int(BigInt::from(2))),
        ])),
        spanned(Expr::Tuple(vec![
            spanned(Expr::Int(BigInt::from(3))),
            spanned(Expr::Int(BigInt::from(4))),
        ])),
    ]));
    let mut defs = HashMap::new();
    defs.insert("TupleSet".to_string(), tupleset_def);
    trans.set_constant_defs(defs);

    // t \in TupleSet
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "t".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "TupleSet".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let t1 = model.int_val("t__1").unwrap();
    let t2 = model.int_val("t__2").unwrap();
    assert!(
        (*t1 == bi(1) && *t2 == bi(2)) || (*t1 == bi(3) && *t2 == bi(4)),
        "t should be <<1,2>> or <<3,4>>, got <<{t1}, {t2}>>"
    );
}

/// Part of #522: Test that unknown Ident references produce an error.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_membership_unknown_ident_error() {
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // x \in UnknownSet (no definition for UnknownSet)
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "UnknownSet".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let result = trans.translate_bool(&membership);
    assert!(result.is_err(), "should error on unknown Ident");
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("UnknownSet"),
        "error should mention 'UnknownSet'"
    );
}

/// Part of #522: Test chained constant resolution (A == B, B == {1,2,3}).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_membership_ident_chained_resolution() {
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // Define: InnerSet == {1, 2, 3}
    let inner_def = spanned(Expr::SetEnum(vec![
        spanned(Expr::Int(BigInt::from(1))),
        spanned(Expr::Int(BigInt::from(2))),
        spanned(Expr::Int(BigInt::from(3))),
    ]));
    // Define: OuterSet == InnerSet (alias)
    let outer_def = spanned(Expr::Ident(
        "InnerSet".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));

    let mut defs = HashMap::new();
    defs.insert("InnerSet".to_string(), inner_def);
    defs.insert("OuterSet".to_string(), outer_def);
    trans.set_constant_defs(defs);

    // x \in OuterSet -> resolves OuterSet -> InnerSet -> {1,2,3}
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "OuterSet".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let term = trans.translate_bool(&membership).unwrap();
    trans.assert(term);

    assert!(matches!(trans.check_sat(), SolveResult::Sat));
    let model = trans.get_model().unwrap();
    let x = model.int_val("x").unwrap();
    assert!(
        (bi(1)..=bi(3)).contains(x),
        "x should be in {{1, 2, 3}}, got {x}"
    );
}

/// Part of #522: Test circular constant detection (A == B, B == A).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_membership_circular_constant_error() {
    let mut trans = Z4Translator::new();

    trans.declare_var("x", TlaSort::Int).unwrap();

    // Define: A == B, B == A (circular)
    let a_def = spanned(Expr::Ident(
        "B".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let b_def = spanned(Expr::Ident(
        "A".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));

    let mut defs = HashMap::new();
    defs.insert("A".to_string(), a_def);
    defs.insert("B".to_string(), b_def);
    trans.set_constant_defs(defs);

    // x \in A should detect cycle
    let membership = spanned(Expr::In(
        Box::new(spanned(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(spanned(Expr::Ident(
            "A".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
    ));

    let result = trans.translate_bool(&membership);
    assert!(result.is_err(), "should error on circular definition");
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("circular"),
        "error should mention 'circular'"
    );
}
