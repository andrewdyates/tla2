// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::tir::eval_tir;
use crate::StateEnvRef;
use num_bigint::BigInt;
use tla_core::ast::{Expr, Module, Unit};
use tla_core::name_intern::intern_name;
use tla_core::{lower, parse_to_syntax_tree, FileId, Span, Spanned};
use tla_tir::{lower_expr, TirExpr, TirNameKind, TirNameRef, TirOperatorRef, TirType};
use tla_value::CompactValue;

const DIRECT_PARAMETERIZED_MODULE: &str = r#"
---- MODULE TirDirectApplyContract ----
Double(x) == x + x
ApplyDirect == Double(3)
====
"#;

fn parse_module(src: &str) -> Module {
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors for module:\n{src}\n{:?}",
        lower_result.errors
    );
    lower_result.module.expect("module should lower")
}

fn find_operator_body<'a>(module: &'a Module, name: &str) -> &'a Spanned<Expr> {
    module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == name => Some(&def.body),
            _ => None,
        })
        .unwrap_or_else(|| panic!("operator '{name}' should exist"))
}

fn ast_value_for_named_op(module: &Module, name: &str) -> Value {
    clear_for_test_reset();
    let mut ctx = EvalCtx::new();
    ctx.load_module(module);
    ctx.eval_op(name)
        .unwrap_or_else(|err| panic!("AST eval of '{name}' should succeed: {err:?}"))
}

fn eval_lowered_tir_expr(module: &Module, expr: &Spanned<Expr>) -> Value {
    clear_for_test_reset();
    let lowered = lower_expr(module, expr).expect("expression should lower to TIR");
    let mut ctx = EvalCtx::new();
    ctx.load_module(module);
    eval_tir(&ctx, &lowered).expect("lowered TIR expression should evaluate")
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_contract_direct_apply_matches_ast() {
    let module = parse_module(DIRECT_PARAMETERIZED_MODULE);
    let ast_value = ast_value_for_named_op(&module, "ApplyDirect");
    let tir_value = eval_lowered_tir_expr(&module, find_operator_body(&module, "ApplyDirect"));
    assert_eq!(
        tir_value, ast_value,
        "direct lowered TIR apply should match AST for user-defined operator calls"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_contract_operator_ref_direct_apply_matches_ast() {
    let module = parse_module(DIRECT_PARAMETERIZED_MODULE);
    let ast_value = ast_value_for_named_op(&module, "ApplyDirect");

    clear_for_test_reset();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    let tir_expr = Spanned::new(
        TirExpr::OperatorRef(TirOperatorRef {
            path: vec![],
            operator: "Double".to_string(),
            operator_id: intern_name("Double"),
            args: vec![Spanned::new(
                TirExpr::Const {
                    value: Value::int(3),
                    ty: TirType::Int,
                },
                Span::dummy(),
            )],
        }),
        Span::dummy(),
    );
    let tir_value = eval_tir(&ctx, &tir_expr).expect("operator-ref TIR apply should evaluate");

    assert_eq!(
        tir_value, ast_value,
        "manual TIR OperatorRef apply should match AST for direct user-defined calls"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tir_unchanged_compact_state_env_matches_equivalent_heap_integer() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");

    let state = [CompactValue::from(Value::int(42))];
    let next = [CompactValue::from(Value::Int(Arc::new(BigInt::from(42))))];
    let _state_guard = ctx.bind_state_env_guard(StateEnvRef::from_compact_slice(&state));
    let _next_guard = ctx.bind_next_state_env_guard(StateEnvRef::from_compact_slice(&next));

    let expr = Spanned::new(
        TirExpr::Unchanged(Box::new(Spanned::new(
            TirExpr::Name(TirNameRef {
                name: "x".to_string(),
                name_id: intern_name("x"),
                kind: TirNameKind::StateVar { index: 0 },
                ty: TirType::Int,
            }),
            Span::dummy(),
        ))),
        Span::dummy(),
    );

    let value = eval_tir(&ctx, &expr).expect("compact TIR UNCHANGED should evaluate");
    assert_eq!(
        value,
        Value::Bool(true),
        "TIR UNCHANGED must preserve Value equality across compact inline/heap slots"
    );
}
