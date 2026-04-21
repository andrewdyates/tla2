// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Prime-expression and partial-next-state parity.

use super::*;
use crate::cache::lifecycle::clear_for_test_reset;
use crate::tir::TirProgram;
use crate::Env;
use std::sync::Arc;

const PRIME_COMPLEX_MODULE: &str = "\
---- MODULE TirPrimeComplex ----
VARIABLE x, y
PrimeArith == (x + 1)'
PrimeTuple == <<x, y + 1>>'
PrimeSum == (x + y)'
====";

#[test]
fn test_tir_parity_prime_of_complex_expressions() {
    let module = parse_module(PRIME_COMPLEX_MODULE);
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    ctx.load_module(&module);

    let state_values = vec![Value::int(1), Value::int(2)];
    let next_values = vec![Value::int(10), Value::int(20)];
    let mut eval_ctx = ctx.clone();
    let _state_guard = eval_ctx.bind_state_array_guard(&state_values);
    let _next_guard = eval_ctx.bind_next_state_array_guard(&next_values);

    for name in ["PrimeArith", "PrimeTuple"] {
        let ast_result = eval_ctx
            .eval_op(name)
            .unwrap_or_else(|err| panic!("AST eval of '{name}' failed: {err}"));
        let program = TirProgram::from_modules(&module, &[]);
        let tir_result = program
            .eval_named_op(&eval_ctx, name)
            .unwrap_or_else(|err| panic!("TIR eval of '{name}' failed: {err}"));
        assert_eq!(
            ast_result, tir_result,
            "AST/TIR parity mismatch for '{name}': AST={ast_result:?}, TIR={tir_result:?}"
        );
    }
}

#[test]
fn test_tir_parity_prime_of_complex_expressions_with_partial_next_state_hashmap() {
    let module = parse_module(PRIME_COMPLEX_MODULE);
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    ctx.load_module(&module);

    let state_values = vec![Value::int(1), Value::int(7)];
    let mut eval_ctx = ctx.clone();
    eval_ctx.bind_state_array(&state_values);

    let mut next_state = Env::default();
    next_state.insert(Arc::from("x"), Value::int(100));
    eval_ctx.set_next_state(next_state);

    let ast_result = eval_ctx
        .eval_op("PrimeSum")
        .unwrap_or_else(|err| panic!("AST eval of 'PrimeSum' failed: {err}"));
    let program = TirProgram::from_modules(&module, &[]);
    let tir_result = program
        .eval_named_op(&eval_ctx, "PrimeSum")
        .unwrap_or_else(|err| panic!("TIR eval of 'PrimeSum' failed: {err}"));

    assert_eq!(
        ast_result, tir_result,
        "AST/TIR parity mismatch for 'PrimeSum': AST={ast_result:?}, TIR={tir_result:?}"
    );
    assert_eq!(ast_result, Value::int(107));
}
