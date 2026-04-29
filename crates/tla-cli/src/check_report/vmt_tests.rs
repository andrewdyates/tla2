// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for VMT output format. Part of #3755.

use super::vmt::*;
use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::span::Spanned;

fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::dummy(node)
}

fn make_ident(name: &str) -> Spanned<Expr> {
    spanned(Expr::Ident(
        name.to_string(),
        tla_core::name_intern::NameId::INVALID,
    ))
}

fn make_int(n: i64) -> Spanned<Expr> {
    spanned(Expr::Int(num_bigint::BigInt::from(n)))
}

fn make_bool(b: bool) -> Spanned<Expr> {
    spanned(Expr::Bool(b))
}

fn make_op_def(name: &str, body: Spanned<Expr>) -> Spanned<Unit> {
    spanned(Unit::Operator(OperatorDef {
        name: spanned(name.to_string()),
        params: vec![],
        body,
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    }))
}

fn make_module(units: Vec<Spanned<Unit>>) -> Module {
    Module {
        name: spanned("Test".to_string()),
        extends: vec![],
        units,
        action_subscript_spans: Default::default(),
        span: tla_core::span::Span::default(),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_vmt_simple_counter() {
    // VARIABLE x
    // Init == x = 0
    // Next == x' = x + 1
    // Inv == x <= 10
    let var_decl = spanned(Unit::Variable(vec![spanned("x".to_string())]));
    let init_body = spanned(Expr::Eq(Box::new(make_ident("x")), Box::new(make_int(0))));
    let next_body = spanned(Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(make_ident("x"))))),
        Box::new(spanned(Expr::Add(
            Box::new(make_ident("x")),
            Box::new(make_int(1)),
        ))),
    ));
    let inv_body = spanned(Expr::Leq(Box::new(make_ident("x")), Box::new(make_int(10))));

    let module = make_module(vec![
        var_decl,
        make_op_def("Init", init_body),
        make_op_def("Next", next_body),
        make_op_def("Inv", inv_body),
    ]);

    let result = spec_to_vmt(&module, "Init", "Next", &["Inv".to_string()]);
    let vmt = result.expect("should produce VMT output");

    // Check variable declarations.
    assert!(vmt.contains("(declare-fun x () Int)"), "missing x decl");
    assert!(
        vmt.contains("(declare-fun x_next () Int)"),
        "missing x_next decl"
    );

    // Check init formula.
    assert!(
        vmt.contains("(define-fun .init () Bool (= x 0))"),
        "bad init: {}",
        vmt
    );

    // Check transition formula.
    assert!(
        vmt.contains("(define-fun .trans () Bool (= x_next (+ x 1)))"),
        "bad trans: {}",
        vmt
    );

    // Check invariant.
    assert!(
        vmt.contains("(define-fun .prop () Bool (<= x 10))"),
        "bad prop: {}",
        vmt
    );

    // Check annotations.
    assert!(vmt.contains("(! x :next x_next)"), "missing :next");
    assert!(vmt.contains("(! .init :init true)"), "missing :init");
    assert!(vmt.contains("(! .trans :trans true)"), "missing :trans");
    assert!(
        vmt.contains("(! .prop :invar-property 0)"),
        "missing :invar-property"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_vmt_bool_sort_inference() {
    // VARIABLE flag
    // TypeOK == flag \in BOOLEAN
    // Init == flag = TRUE
    let var_decl = spanned(Unit::Variable(vec![spanned("flag".to_string())]));
    let typeok_body = spanned(Expr::In(
        Box::new(make_ident("flag")),
        Box::new(make_ident("BOOLEAN")),
    ));
    let init_body = spanned(Expr::Eq(
        Box::new(make_ident("flag")),
        Box::new(make_bool(true)),
    ));
    let next_body = spanned(Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(make_ident("flag"))))),
        Box::new(spanned(Expr::Not(Box::new(make_ident("flag"))))),
    ));
    let inv_body = spanned(Expr::Or(
        Box::new(make_ident("flag")),
        Box::new(spanned(Expr::Not(Box::new(make_ident("flag"))))),
    ));

    let module = make_module(vec![
        var_decl,
        make_op_def("TypeOK", typeok_body),
        make_op_def("Init", init_body),
        make_op_def("Next", next_body),
        make_op_def("Inv", inv_body),
    ]);

    let result = spec_to_vmt(&module, "Init", "Next", &["Inv".to_string()]);
    let vmt = result.expect("should produce VMT output");

    // Boolean sort should be inferred from TypeOK.
    assert!(
        vmt.contains("(declare-fun flag () Bool)"),
        "should infer Bool sort: {}",
        vmt
    );
    assert!(
        vmt.contains("(declare-fun flag_next () Bool)"),
        "missing flag_next: {}",
        vmt
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_vmt_multiple_invariants() {
    let var_decl = spanned(Unit::Variable(vec![spanned("x".to_string())]));
    let init_body = spanned(Expr::Eq(Box::new(make_ident("x")), Box::new(make_int(0))));
    let next_body = spanned(Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(make_ident("x"))))),
        Box::new(make_ident("x")),
    ));
    let inv1 = spanned(Expr::Geq(Box::new(make_ident("x")), Box::new(make_int(0))));
    let inv2 = spanned(Expr::Leq(
        Box::new(make_ident("x")),
        Box::new(make_int(100)),
    ));

    let module = make_module(vec![
        var_decl,
        make_op_def("Init", init_body),
        make_op_def("Next", next_body),
        make_op_def("Pos", inv1),
        make_op_def("Bounded", inv2),
    ]);

    let result = spec_to_vmt(
        &module,
        "Init",
        "Next",
        &["Pos".to_string(), "Bounded".to_string()],
    );
    let vmt = result.expect("should produce VMT output");

    // Multiple invariants get numbered names.
    assert!(vmt.contains(".prop_0"), "missing .prop_0");
    assert!(vmt.contains(".prop_1"), "missing .prop_1");
    assert!(
        vmt.contains("(! .prop_0 :invar-property 0)"),
        "missing prop_0 annotation"
    );
    assert!(
        vmt.contains("(! .prop_1 :invar-property 1)"),
        "missing prop_1 annotation"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_vmt_unchanged() {
    let var_decl = spanned(Unit::Variable(vec![
        spanned("x".to_string()),
        spanned("y".to_string()),
    ]));
    let init_body = spanned(Expr::And(
        Box::new(spanned(Expr::Eq(
            Box::new(make_ident("x")),
            Box::new(make_int(0)),
        ))),
        Box::new(spanned(Expr::Eq(
            Box::new(make_ident("y")),
            Box::new(make_int(0)),
        ))),
    ));
    // Next == x' = x + 1 /\ UNCHANGED y
    let next_body = spanned(Expr::And(
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(Expr::Prime(Box::new(make_ident("x"))))),
            Box::new(spanned(Expr::Add(
                Box::new(make_ident("x")),
                Box::new(make_int(1)),
            ))),
        ))),
        Box::new(spanned(Expr::Unchanged(Box::new(make_ident("y"))))),
    ));
    let inv_body = make_bool(true);

    let module = make_module(vec![
        var_decl,
        make_op_def("Init", init_body),
        make_op_def("Next", next_body),
        make_op_def("Inv", inv_body),
    ]);

    let result = spec_to_vmt(&module, "Init", "Next", &["Inv".to_string()]);
    let vmt = result.expect("should produce VMT output");

    // UNCHANGED y => y_next = y
    assert!(
        vmt.contains("(= y_next y)"),
        "UNCHANGED y not translated: {}",
        vmt
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_vmt_if_then_else() {
    let var_decl = spanned(Unit::Variable(vec![spanned("x".to_string())]));
    let init_body = spanned(Expr::Eq(Box::new(make_ident("x")), Box::new(make_int(0))));
    // Next == x' = IF x > 5 THEN 0 ELSE x + 1
    let next_body = spanned(Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(make_ident("x"))))),
        Box::new(spanned(Expr::If(
            Box::new(spanned(Expr::Gt(
                Box::new(make_ident("x")),
                Box::new(make_int(5)),
            ))),
            Box::new(make_int(0)),
            Box::new(spanned(Expr::Add(
                Box::new(make_ident("x")),
                Box::new(make_int(1)),
            ))),
        ))),
    ));
    let inv_body = spanned(Expr::Leq(Box::new(make_ident("x")), Box::new(make_int(10))));

    let module = make_module(vec![
        var_decl,
        make_op_def("Init", init_body),
        make_op_def("Next", next_body),
        make_op_def("Inv", inv_body),
    ]);

    let result = spec_to_vmt(&module, "Init", "Next", &["Inv".to_string()]);
    let vmt = result.expect("should produce VMT output");

    assert!(
        vmt.contains("(ite (> x 5) 0 (+ x 1))"),
        "IF/THEN/ELSE not translated: {}",
        vmt
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_vmt_no_vars_returns_error() {
    let module = make_module(vec![
        make_op_def("Init", make_bool(true)),
        make_op_def("Next", make_bool(true)),
    ]);
    let result = spec_to_vmt(&module, "Init", "Next", &["Init".to_string()]);
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("No state variables declared"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_vmt_missing_init_returns_error() {
    let var_decl = spanned(Unit::Variable(vec![spanned("x".to_string())]));
    let module = make_module(vec![var_decl, make_op_def("Next", make_bool(true))]);
    let result = spec_to_vmt(&module, "Init", "Next", &[]);
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("Init"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_smtlib_ident_simple() {
    assert_eq!(smtlib_ident("x"), "x");
    assert_eq!(smtlib_ident("foo_bar"), "foo_bar");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_smtlib_ident_special_chars() {
    assert_eq!(smtlib_ident("pc'"), "|pc'|");
    assert_eq!(smtlib_ident("a.b"), "|a.b|");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_smtlib_ident_leading_digit() {
    assert_eq!(smtlib_ident("3pc"), "|3pc|");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_vmt_negative_int() {
    let var_decl = spanned(Unit::Variable(vec![spanned("x".to_string())]));
    let init_body = spanned(Expr::Eq(Box::new(make_ident("x")), Box::new(make_int(-5))));
    let next_body = spanned(Expr::Eq(
        Box::new(spanned(Expr::Prime(Box::new(make_ident("x"))))),
        Box::new(make_ident("x")),
    ));
    let inv_body = make_bool(true);

    let module = make_module(vec![
        var_decl,
        make_op_def("Init", init_body),
        make_op_def("Next", next_body),
        make_op_def("Inv", inv_body),
    ]);

    let result = spec_to_vmt(&module, "Init", "Next", &["Inv".to_string()]);
    let vmt = result.expect("should produce VMT output");
    assert!(
        vmt.contains("(= x (- 5))"),
        "negative int not encoded: {}",
        vmt
    );
}
