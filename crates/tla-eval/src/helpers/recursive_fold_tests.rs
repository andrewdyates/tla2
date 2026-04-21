// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for RECURSIVE fold detection (Part of #2955).

use super::*;
use std::sync::Arc;
use tla_core::ast::{BoundVar, OpParam, OperatorDef};
use tla_core::name_intern::NameId;
use tla_core::Spanned;

fn spanned<T>(node: T) -> Spanned<T> {
    Spanned::dummy(node)
}

fn ident(name: &str) -> Expr {
    Expr::Ident(name.to_string(), NameId::INVALID)
}

fn dyadic(num: i64, den: i64) -> Value {
    Value::Record(
        vec![
            ("num".to_string(), Value::int(num)),
            ("den".to_string(), Value::int(den)),
        ]
        .into(),
    )
}

fn ctx_with_modules(modules: &[&str]) -> EvalCtx {
    let mut ctx = EvalCtx::new();
    let shared = Arc::make_mut(&mut ctx.stable_mut().shared);
    for module in modules {
        shared.extended_module_names.insert((*module).to_string());
    }
    ctx
}

/// Build a standard fold operator AST with configurable elem_expr.
fn make_fold_op_with_elem(
    name: &str,
    set_param: &str,
    val_param: &str,
    elem_var: &str,
    base: Expr,
    binop_ctor: fn(Box<Spanned<Expr>>, Box<Spanned<Expr>>) -> Expr,
    elem_expr: Spanned<Expr>,
) -> OperatorDef {
    let recursive_call = spanned(Expr::Apply(
        Box::new(spanned(ident(name))),
        vec![
            spanned(ident(val_param)),
            spanned(Expr::SetMinus(
                Box::new(spanned(ident(set_param))),
                Box::new(spanned(Expr::SetEnum(vec![spanned(ident(elem_var))]))),
            )),
        ],
    ));
    let accum = binop_ctor(Box::new(elem_expr), Box::new(recursive_call));
    let choose_def = OperatorDef {
        name: spanned(elem_var.to_string()),
        params: vec![],
        body: spanned(Expr::Choose(
            BoundVar {
                name: spanned(elem_var.to_string()),
                domain: Some(Box::new(spanned(ident(set_param)))),
                pattern: None,
            },
            Box::new(spanned(Expr::Bool(true))),
        )),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };
    let body = Expr::If(
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(ident(set_param))),
            Box::new(spanned(Expr::SetEnum(vec![]))),
        ))),
        Box::new(spanned(base)),
        Box::new(spanned(Expr::Let(
            vec![choose_def],
            Box::new(spanned(accum)),
        ))),
    );
    OperatorDef {
        name: spanned(name.to_string()),
        params: vec![
            OpParam {
                name: spanned(val_param.to_string()),
                arity: 0,
            },
            OpParam {
                name: spanned(set_param.to_string()),
                arity: 0,
            },
        ],
        body: spanned(body),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: true,
        self_call_count: 1,
    }
}

fn make_fold_op(
    name: &str,
    set_param: &str,
    val_param: &str,
    elem_var: &str,
    base: Expr,
    binop_ctor: fn(Box<Spanned<Expr>>, Box<Spanned<Expr>>) -> Expr,
) -> OperatorDef {
    let elem_expr = spanned(Expr::FuncApply(
        Box::new(spanned(ident(val_param))),
        Box::new(spanned(ident(elem_var))),
    ));
    make_fold_op_with_elem(
        name, set_param, val_param, elem_var, base, binop_ctor, elem_expr,
    )
}

fn make_named_fold_op(
    name: &str,
    set_param: &str,
    val_param: &str,
    elem_var: &str,
    base: Expr,
    op_name: &str,
) -> OperatorDef {
    let elem_expr = spanned(Expr::FuncApply(
        Box::new(spanned(ident(val_param))),
        Box::new(spanned(ident(elem_var))),
    ));
    let recursive_call = spanned(Expr::Apply(
        Box::new(spanned(ident(name))),
        vec![
            spanned(ident(val_param)),
            spanned(Expr::SetMinus(
                Box::new(spanned(ident(set_param))),
                Box::new(spanned(Expr::SetEnum(vec![spanned(ident(elem_var))]))),
            )),
        ],
    ));
    let accum = spanned(Expr::Apply(
        Box::new(spanned(ident(op_name))),
        vec![elem_expr, recursive_call],
    ));
    let choose_def = OperatorDef {
        name: spanned(elem_var.to_string()),
        params: vec![],
        body: spanned(Expr::Choose(
            BoundVar {
                name: spanned(elem_var.to_string()),
                domain: Some(Box::new(spanned(ident(set_param)))),
                pattern: None,
            },
            Box::new(spanned(Expr::Bool(true))),
        )),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    };
    let body = Expr::If(
        Box::new(spanned(Expr::Eq(
            Box::new(spanned(ident(set_param))),
            Box::new(spanned(Expr::SetEnum(vec![]))),
        ))),
        Box::new(spanned(base)),
        Box::new(spanned(Expr::Let(vec![choose_def], Box::new(accum)))),
    );
    OperatorDef {
        name: spanned(name.to_string()),
        params: vec![
            OpParam {
                name: spanned(val_param.to_string()),
                arity: 0,
            },
            OpParam {
                name: spanned(set_param.to_string()),
                arity: 0,
            },
        ],
        body: spanned(body),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: true,
        self_call_count: 1,
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_detect_fold_pattern_sum() {
    let def = make_fold_op("Sum", "S", "f", "x", Expr::Int(0.into()), Expr::Add);
    let pattern = detect_fold_pattern(&def).expect("should detect Sum as fold");
    assert_eq!(pattern.set_param_idx, 1);
    assert_eq!(pattern.elem_var_name, "x");
    assert!(!pattern.recursive_on_left);
    assert!(matches!(pattern.binop, FoldBinOp::Add));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_detect_fold_pattern_product() {
    let def = make_fold_op("Product", "S", "f", "x", Expr::Int(1.into()), Expr::Mul);
    let pattern = detect_fold_pattern(&def).expect("should detect Product as fold");
    assert!(matches!(pattern.binop, FoldBinOp::Mul));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_recursive_fold_detects_named_binary_op() {
    let def = make_named_fold_op("Sum", "S", "f", "x", Expr::Int(0.into()), "Add");
    let pattern = detect_fold_pattern(&def).expect("should detect named fold operator");
    assert!(matches!(&pattern.binop, FoldBinOp::Named(name) if name == "Add"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_detect_fold_rejects_non_recursive() {
    let mut def = make_fold_op("Sum", "S", "f", "x", Expr::Int(0.into()), Expr::Add);
    def.is_recursive = false;
    assert!(detect_fold_pattern(&def).is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_expr_references_name() {
    assert!(expr_references_name(&ident("S"), "S"));
    assert!(!expr_references_name(&ident("S"), "T"));
    assert!(expr_references_name(
        &Expr::Add(Box::new(spanned(ident("x"))), Box::new(spanned(ident("S")))),
        "S"
    ));
    assert!(!expr_references_name(
        &Expr::Add(Box::new(spanned(ident("x"))), Box::new(spanned(ident("y")))),
        "S"
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_detect_fold_rejects_elem_referencing_set_param() {
    // elem_expr = Cardinality(S) — references the set param, so fold is unsafe
    let bad_elem = spanned(Expr::Apply(
        Box::new(spanned(ident("Cardinality"))),
        vec![spanned(ident("S"))],
    ));
    let def = make_fold_op_with_elem("F", "S", "f", "x", Expr::Int(0.into()), Expr::Add, bad_elem);
    assert!(detect_fold_pattern(&def).is_none());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_recursive_fold_named_binary_op_uses_stdlib_override() {
    let ctx = ctx_with_modules(&["DyadicRationals"]);
    let result = apply_fold_binop(
        &FoldBinOp::Named("Add".to_string()),
        &ctx,
        dyadic(1, 1),
        dyadic(1, 2),
        None,
    )
    .expect("DyadicRationals.Add should use the stdlib override");
    assert_eq!(result, dyadic(3, 2));
}
