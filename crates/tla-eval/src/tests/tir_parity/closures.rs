// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lambda closure body and apply parity.

use super::*;
use crate::apply_closure_with_values;
use crate::cache::lifecycle::clear_for_test_reset;
use crate::tir::TirProgram;

const LAMBDA_MODULE: &str = "\
---- MODULE TirLambda ----
LambdaOp == (LAMBDA x: x + 1)
====";

#[test]
fn test_tir_parity_lambda_applies_via_tir_body() {
    let module = parse_module(LAMBDA_MODULE);
    let ast_closure = eval_ast_op(&module, "LambdaOp");

    clear_for_test_reset();
    let program = TirProgram::from_modules(&module, &[]);
    let ctx = EvalCtx::new();
    let tir_closure = program
        .eval_named_op(&ctx, "LambdaOp")
        .unwrap_or_else(|err| panic!("TIR eval of 'LambdaOp' should succeed: {err:?}"));

    let Value::Closure(ref ast_closure) = ast_closure else {
        panic!("AST eval of LambdaOp should produce a closure");
    };
    let Value::Closure(ref tir_closure) = tir_closure else {
        panic!("TIR eval of LambdaOp should produce a closure");
    };

    assert!(
        tir_closure.tir_body().is_some(),
        "TIR-created closures should retain their lowered body"
    );

    let ast_result = apply_closure_with_values(&ctx, ast_closure.as_ref(), &[Value::int(1)], None)
        .unwrap_or_else(|err| panic!("AST closure apply should succeed: {err:?}"));
    let tir_result = apply_closure_with_values(&ctx, tir_closure.as_ref(), &[Value::int(1)], None)
        .unwrap_or_else(|err| panic!("TIR closure apply should succeed: {err:?}"));

    assert_eq!(
        tir_result, ast_result,
        "TIR lambda closure apply should match AST closure apply"
    );
    assert_eq!(tir_result, Value::int(2));
}

// Multi-parameter lambda: LAMBDA x, y : x + y
const LAMBDA_MULTI_PARAM: &str = "\
---- MODULE TirLambdaMulti ----
MultiLambda == (LAMBDA x, y: x + y)
====";

#[test]
fn test_tir_parity_lambda_multi_param() {
    let module = parse_module(LAMBDA_MULTI_PARAM);
    let ast_closure = eval_ast_op(&module, "MultiLambda");
    let tir_closure = eval_tir_op(&module, "MultiLambda");

    let Value::Closure(ref ast_c) = ast_closure else {
        panic!("AST eval should produce a closure");
    };
    let Value::Closure(ref tir_c) = tir_closure else {
        panic!("TIR eval should produce a closure");
    };

    assert!(
        tir_c.tir_body().is_some(),
        "Multi-param TIR closure should retain lowered body"
    );

    let ctx = EvalCtx::new();
    let ast_result =
        apply_closure_with_values(&ctx, ast_c.as_ref(), &[Value::int(3), Value::int(4)], None)
            .expect("AST closure apply should succeed");
    let tir_result =
        apply_closure_with_values(&ctx, tir_c.as_ref(), &[Value::int(3), Value::int(4)], None)
            .expect("TIR closure apply should succeed");

    assert_eq!(
        tir_result, ast_result,
        "Multi-param lambda: TIR and AST should agree"
    );
    assert_eq!(tir_result, Value::int(7));
}

// Lambda with boolean body (exercises different TIR dispatch than arithmetic)
const LAMBDA_BOOLEAN: &str = "\
---- MODULE TirLambdaBool ----
Pred == (LAMBDA x: x > 0)
====";

#[test]
fn test_tir_parity_lambda_boolean_body() {
    let module = parse_module(LAMBDA_BOOLEAN);
    let tir_closure = eval_tir_op(&module, "Pred");

    let Value::Closure(ref tir_c) = tir_closure else {
        panic!("TIR eval should produce a closure");
    };
    assert!(
        tir_c.tir_body().is_some(),
        "Boolean-body TIR closure should retain lowered body"
    );

    let ctx = EvalCtx::new();
    let ast_closure = eval_ast_op(&module, "Pred");
    let Value::Closure(ref ast_c) = ast_closure else {
        panic!("AST eval should produce a closure");
    };

    // Apply with positive value
    let tir_pos = apply_closure_with_values(&ctx, tir_c.as_ref(), &[Value::int(5)], None)
        .expect("TIR closure apply should succeed");
    let ast_pos = apply_closure_with_values(&ctx, ast_c.as_ref(), &[Value::int(5)], None)
        .expect("AST closure apply should succeed");
    assert_eq!(tir_pos, ast_pos);
    assert_eq!(tir_pos, Value::Bool(true));

    // Apply with negative value
    let tir_neg = apply_closure_with_values(&ctx, tir_c.as_ref(), &[Value::int(-1)], None)
        .expect("TIR closure apply should succeed");
    let ast_neg = apply_closure_with_values(&ctx, ast_c.as_ref(), &[Value::int(-1)], None)
        .expect("AST closure apply should succeed");
    assert_eq!(tir_neg, ast_neg);
    assert_eq!(tir_neg, Value::Bool(false));
}
