// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::emit::build_test_emitter;
use std::collections::HashMap;
use tla_core::ast::{BoundVar, ExceptPathElement, ExceptSpec};
use tla_core::name_intern::NameId;
use tla_core::span::{FileId, Span};

fn make_span() -> Span {
    Span::new(FileId(0), 0, 0)
}

fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::new(node, make_span())
}

fn bound_var(name: &str, domain: Expr) -> BoundVar {
    BoundVar {
        name: spanned(name.to_string()),
        domain: Some(Box::new(spanned(domain))),
        pattern: None,
    }
}

fn floor_intdiv_expr(lhs: i64, rhs: i64) -> String {
    format!(
        "({{ let __a = {lhs}_i64; let __b = {rhs}_i64; let __q = __a / __b; if (__a ^ __b) < 0 && __a % __b != 0 {{ __q - 1 }} else {{ __q }} }})"
    )
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_to_rust_except_helper_translation() {
    let mut out = String::new();
    let var_types = HashMap::new();
    let op_defs = HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let except = Expr::Except(
        Box::new(spanned(Expr::Ident("f".to_string(), NameId::INVALID))),
        vec![ExceptSpec {
            path: vec![ExceptPathElement::Index(spanned(Expr::Int(1.into())))],
            value: spanned(Expr::Int(2.into())),
        }],
    );

    let result = emitter.expr_to_rust(&except);
    assert!(result.contains("let mut __tmp = f.clone();"), "{}", result);
    assert!(result.contains("__tmp.update(1_i64, 2_i64);"), "{}", result);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_to_rust_quantifier_and_set_builder_helpers() {
    let mut out = String::new();
    let var_types = HashMap::new();
    let op_defs = HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let range = Expr::Range(
        Box::new(spanned(Expr::Int(1.into()))),
        Box::new(spanned(Expr::Int(3.into()))),
    );
    let x = Expr::Ident("x".to_string(), NameId::INVALID);

    let forall = Expr::Forall(
        vec![bound_var("x", range.clone())],
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(x.clone())),
            Box::new(spanned(Expr::Int(0.into()))),
        ))),
    );
    assert_eq!(
        emitter.expr_to_rust(&forall),
        "range_set(1_i64, 3_i64).iter().all(|x| (x > 0_i64))"
    );

    let choose = Expr::Choose(
        bound_var("x", range.clone()),
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(x.clone())),
            Box::new(spanned(Expr::Int(1.into()))),
        ))),
    );
    assert_eq!(
        emitter.expr_to_rust(&choose),
        "range_set(1_i64, 3_i64).iter().find(|x| (x > 1_i64)).cloned().expect(\"CHOOSE: no element satisfies predicate\")"
    );

    let set_builder = Expr::SetBuilder(
        Box::new(spanned(x.clone())),
        vec![bound_var("x", range.clone())],
    );
    assert_eq!(
        emitter.expr_to_rust(&set_builder),
        "TlaSet::from_iter(range_set(1_i64, 3_i64).iter().map(|x| x))"
    );

    let set_filter = Expr::SetFilter(
        bound_var("x", range),
        Box::new(spanned(Expr::Gt(
            Box::new(spanned(x)),
            Box::new(spanned(Expr::Int(1.into()))),
        ))),
    );
    assert_eq!(
        emitter.expr_to_rust(&set_filter),
        "TlaSet::from_iter(range_set(1_i64, 3_i64).iter().filter(|x| (x > 1_i64)).cloned())"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_to_rust_function_builder_helpers() {
    let mut out = String::new();
    let var_types = HashMap::new();
    let op_defs = HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let range = Expr::Range(
        Box::new(spanned(Expr::Int(1.into()))),
        Box::new(spanned(Expr::Int(2.into()))),
    );
    let x = Expr::Ident("x".to_string(), NameId::INVALID);

    let func_def = Expr::FuncDef(vec![bound_var("x", range)], Box::new(spanned(x)));
    assert_eq!(
        emitter.expr_to_rust(&func_def),
        "TlaFunc::from_iter(range_set(1_i64, 2_i64).iter().map(|x| (x.clone(), x)))"
    );

    let func_set = Expr::FuncSet(
        Box::new(spanned(Expr::Ident("s".to_string(), NameId::INVALID))),
        Box::new(spanned(Expr::Ident("t".to_string(), NameId::INVALID))),
    );
    let result = emitter.expr_to_rust(&func_set);
    assert!(result.contains("let __domain: Vec<_> = (s).iter().cloned().collect();"));
    assert!(result.contains("let __range: Vec<_> = (t).iter().cloned().collect();"));
    assert!(result.contains("__result.insert(TlaFunc::from_iter(__f_entries));"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_to_rust_intdiv_negative_dividend() {
    let mut out = String::new();
    let var_types = HashMap::new();
    let op_defs = HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let expr = Expr::IntDiv(
        Box::new(spanned(Expr::Int((-7).into()))),
        Box::new(spanned(Expr::Int(2.into()))),
    );

    assert_eq!(emitter.expr_to_rust(&expr), floor_intdiv_expr(-7, 2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_to_rust_intdiv_negative_divisor() {
    let mut out = String::new();
    let var_types = HashMap::new();
    let op_defs = HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let expr = Expr::IntDiv(
        Box::new(spanned(Expr::Int(7.into()))),
        Box::new(spanned(Expr::Int((-2).into()))),
    );

    assert_eq!(emitter.expr_to_rust(&expr), floor_intdiv_expr(7, -2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_to_rust_intdiv_both_negative() {
    let mut out = String::new();
    let var_types = HashMap::new();
    let op_defs = HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let expr = Expr::IntDiv(
        Box::new(spanned(Expr::Int((-7).into()))),
        Box::new(spanned(Expr::Int((-2).into()))),
    );

    assert_eq!(emitter.expr_to_rust(&expr), floor_intdiv_expr(-7, -2));
}

fn floor_intmod_expr(lhs: i64, rhs: i64) -> String {
    format!(
        "({{ let __a = {lhs}_i64; let __b = {rhs}_i64; let __r = __a % __b; if __r < 0 {{ __r + __b }} else {{ __r }} }})"
    )
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_to_rust_mod_negative_dividend() {
    let mut out = String::new();
    let var_types = HashMap::new();
    let op_defs = HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let expr = Expr::Mod(
        Box::new(spanned(Expr::Int((-7).into()))),
        Box::new(spanned(Expr::Int(3.into()))),
    );

    // TLA+ (-7) % 3 = 2 (Euclidean mod, always non-negative for positive divisor)
    assert_eq!(emitter.expr_to_rust(&expr), floor_intmod_expr(-7, 3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_to_rust_mod_positive_both() {
    let mut out = String::new();
    let var_types = HashMap::new();
    let op_defs = HashMap::new();
    let emitter = build_test_emitter(&mut out, &var_types, &op_defs, Default::default());

    let expr = Expr::Mod(
        Box::new(spanned(Expr::Int(7.into()))),
        Box::new(spanned(Expr::Int(3.into()))),
    );

    // TLA+ 7 % 3 = 1
    assert_eq!(emitter.expr_to_rust(&expr), floor_intmod_expr(7, 3));
}
