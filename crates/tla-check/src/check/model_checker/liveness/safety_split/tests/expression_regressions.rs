// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- Part of #1885: tests for previously-missed expression types ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_temporal_inside_if_then() {
    // IF x THEN <>y ELSE z -- the <> in `then` must be detected
    let expr = Expr::If(
        boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        boxed(Expr::Eventually(boxed(Expr::Ident(
            "y".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        boxed(Expr::Ident(
            "z".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );
    assert!(
        ModelChecker::contains_temporal_helper(&expr),
        "Should detect <> inside IF-THEN branch"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_temporal_inside_if_else() {
    // IF x THEN y ELSE <>z -- the <> in `else` must be detected
    let expr = Expr::If(
        boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        boxed(Expr::Ident(
            "y".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        boxed(Expr::Eventually(boxed(Expr::Ident(
            "z".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
    );
    assert!(
        ModelChecker::contains_temporal_helper(&expr),
        "Should detect <> inside IF-ELSE branch"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_temporal_inside_let_body() {
    // LET foo == x IN <>foo -- the <> in the LET body must be detected
    let expr = Expr::Let(
        vec![],
        boxed(Expr::Eventually(boxed(Expr::Ident(
            "foo".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
    );
    assert!(
        ModelChecker::contains_temporal_helper(&expr),
        "Should detect <> inside LET body"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_temporal_inside_case_arm() {
    // CASE guard -> <>P -- the <> in CASE arm body must be detected
    let arm = tla_core::ast::CaseArm {
        guard: dummy(Expr::Bool(true)),
        body: dummy(Expr::Eventually(boxed(Expr::Ident(
            "P".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
    };
    let expr = Expr::Case(vec![arm], None);
    assert!(
        ModelChecker::contains_temporal_helper(&expr),
        "Should detect <> inside CASE arm"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_no_temporal_in_plain_if() {
    // IF x THEN y ELSE z -- no temporal operators
    let expr = Expr::If(
        boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        boxed(Expr::Ident(
            "y".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        boxed(Expr::Ident(
            "z".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    );
    assert!(
        !ModelChecker::contains_temporal_helper(&expr),
        "Plain IF without temporal operators should return false"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_temporal_inside_func_apply() {
    // f(<>x) -- the <> inside FuncApply arg must be detected
    let expr = Expr::FuncApply(
        boxed(Expr::Ident(
            "f".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        boxed(Expr::Eventually(boxed(Expr::Ident(
            "x".into(),
            tla_core::name_intern::NameId::INVALID,
        )))),
    );
    assert!(
        ModelChecker::contains_temporal_helper(&expr),
        "Should detect <> inside FuncApply argument"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_temporal_inside_except_path_index() {
    // [f EXCEPT ![<>x] = y] -- the <> inside the EXCEPT path index must be detected
    let spec = tla_core::ast::ExceptSpec {
        path: vec![tla_core::ast::ExceptPathElement::Index(dummy(
            Expr::Eventually(boxed(Expr::Ident(
                "x".into(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        ))],
        value: dummy(Expr::Ident(
            "y".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    };
    let expr = Expr::Except(
        boxed(Expr::Ident(
            "f".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        vec![spec],
    );
    assert!(
        ModelChecker::contains_temporal_helper(&expr),
        "Should detect <> inside EXCEPT path index"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_enabled_inside_except_path_index() {
    // [f EXCEPT ![ENABLED(a)] = y] -- the ENABLED inside the EXCEPT path must be detected
    let spec = tla_core::ast::ExceptSpec {
        path: vec![tla_core::ast::ExceptPathElement::Index(dummy(
            Expr::Enabled(boxed(Expr::Ident(
                "a".into(),
                tla_core::name_intern::NameId::INVALID,
            ))),
        ))],
        value: dummy(Expr::Ident(
            "y".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
    };
    let expr = Expr::Except(
        boxed(Expr::Ident(
            "f".into(),
            tla_core::name_intern::NameId::INVALID,
        )),
        vec![spec],
    );
    assert!(
        ModelChecker::contains_enabled(&expr),
        "Should detect ENABLED inside EXCEPT path index"
    );
}
