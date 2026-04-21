// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Counter-style canary: the minimal spec from the design doc.

use super::*;
use crate::cache::lifecycle::clear_for_test_reset;
use crate::tir::TirProgram;
use tla_core::ast::Unit;

const COUNTER_MODULE: &str = "\
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Bound == x < 3
Add == 1 + 2
Sub == 5 - 3
Mul == 2 * 4
Neg == -(3)
CmpLt == 1 < 2
CmpLeq == 2 <= 2
CmpGt == 3 > 1
CmpGeq == 3 >= 3
Iff == TRUE <=> FALSE
Impl == FALSE => TRUE
OrTest == FALSE \\/ TRUE
AndTest == TRUE /\\ TRUE
NotTest == ~TRUE
IfTest == IF TRUE THEN 1 ELSE 2
EqTest == 3 = 3
NeqTest == 1 /= 2
NestedArith == (1 + 2) * (4 - 1)
====";

#[test]
fn test_tir_parity_counter_add() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "Add");
}

#[test]
fn test_tir_parity_counter_sub() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "Sub");
}

#[test]
fn test_tir_parity_counter_mul() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "Mul");
}

#[test]
fn test_tir_parity_counter_neg() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "Neg");
}

#[test]
fn test_tir_parity_counter_cmp_lt() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "CmpLt");
}

#[test]
fn test_tir_parity_counter_cmp_leq() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "CmpLeq");
}

#[test]
fn test_tir_parity_counter_cmp_gt() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "CmpGt");
}

#[test]
fn test_tir_parity_counter_cmp_geq() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "CmpGeq");
}

#[test]
fn test_tir_parity_counter_iff() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "Iff");
}

#[test]
fn test_tir_parity_counter_implies() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "Impl");
}

#[test]
fn test_tir_parity_counter_or() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "OrTest");
}

#[test]
fn test_tir_parity_counter_and() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "AndTest");
}

#[test]
fn test_tir_parity_counter_not() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "NotTest");
}

#[test]
fn test_tir_parity_counter_if() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "IfTest");
}

#[test]
fn test_tir_parity_counter_eq() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "EqTest");
}

#[test]
fn test_tir_parity_counter_neq() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "NeqTest");
}

#[test]
fn test_tir_parity_counter_nested_arith() {
    let module = parse_module(COUNTER_MODULE);
    assert_parity(&module, "NestedArith");
}

// ============================================================================
// State variable access: Init predicate with state context
// ============================================================================

#[test]
fn test_tir_parity_counter_init_with_state() {
    let module = parse_module(COUNTER_MODULE);
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.load_module(&module);

    let state_values = vec![Value::int(0)];
    let mut eval_ctx = ctx.clone();
    eval_ctx.bind_state_array(&state_values);

    let init_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node == "Init" => Some(def),
            _ => None,
        })
        .expect("Init not found");
    let ast_result = eval(&eval_ctx, &init_def.body).expect("AST eval failed");

    let program = TirProgram::from_modules(&module, &[]);
    let tir_result = program
        .eval_named_op(&eval_ctx, "Init")
        .expect("TIR eval failed");

    assert_eq!(
        ast_result, tir_result,
        "AST/TIR parity mismatch for Init: AST={ast_result:?}, TIR={tir_result:?}"
    );
    assert_eq!(ast_result, Value::Bool(true));
}

#[test]
fn test_tir_parity_counter_init_false_state() {
    let module = parse_module(COUNTER_MODULE);
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.load_module(&module);

    let state_values = vec![Value::int(5)];
    let mut eval_ctx = ctx.clone();
    eval_ctx.bind_state_array(&state_values);

    let init_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node == "Init" => Some(def),
            _ => None,
        })
        .expect("Init not found");
    let ast_result = eval(&eval_ctx, &init_def.body).expect("AST eval failed");

    let program = TirProgram::from_modules(&module, &[]);
    let tir_result = program
        .eval_named_op(&eval_ctx, "Init")
        .expect("TIR eval failed");

    assert_eq!(
        ast_result, tir_result,
        "AST/TIR parity mismatch for Init(x=5): AST={ast_result:?}, TIR={tir_result:?}"
    );
    assert_eq!(ast_result, Value::Bool(false));
}

#[test]
fn test_tir_parity_counter_bound_with_state() {
    let module = parse_module(COUNTER_MODULE);
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.load_module(&module);

    let state_values = vec![Value::int(2)];
    let mut eval_ctx = ctx.clone();
    eval_ctx.bind_state_array(&state_values);

    let bound_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node == "Bound" => Some(def),
            _ => None,
        })
        .expect("Bound not found");
    let ast_result = eval(&eval_ctx, &bound_def.body).expect("AST eval failed");

    let program = TirProgram::from_modules(&module, &[]);
    let tir_result = program
        .eval_named_op(&eval_ctx, "Bound")
        .expect("TIR eval failed");

    assert_eq!(
        ast_result, tir_result,
        "AST/TIR parity for Bound(x=2): AST={ast_result:?}, TIR={tir_result:?}"
    );
    assert_eq!(ast_result, Value::Bool(true));
}

#[test]
fn test_tir_parity_counter_next_with_transition() {
    let module = parse_module(COUNTER_MODULE);
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.load_module(&module);

    let state_values = vec![Value::int(0)];
    let next_values = vec![Value::int(1)];
    let mut eval_ctx = ctx.clone();
    let _state_guard = eval_ctx.bind_state_array_guard(&state_values);
    let _next_guard = eval_ctx.bind_next_state_array_guard(&next_values);

    let next_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node == "Next" => Some(def),
            _ => None,
        })
        .expect("Next not found");
    let ast_result = eval(&eval_ctx, &next_def.body).expect("AST eval failed");

    let program = TirProgram::from_modules(&module, &[]);
    let tir_result = program
        .eval_named_op(&eval_ctx, "Next")
        .expect("TIR eval failed");

    assert_eq!(
        ast_result, tir_result,
        "AST/TIR parity for Next(x=0, x'=1): AST={ast_result:?}, TIR={tir_result:?}"
    );
    assert_eq!(ast_result, Value::Bool(true));
}

#[test]
fn test_tir_parity_counter_next_false_transition() {
    let module = parse_module(COUNTER_MODULE);
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.load_module(&module);

    let state_values = vec![Value::int(0)];
    let next_values = vec![Value::int(2)];
    let mut eval_ctx = ctx.clone();
    let _state_guard = eval_ctx.bind_state_array_guard(&state_values);
    let _next_guard = eval_ctx.bind_next_state_array_guard(&next_values);

    let next_def = module
        .units
        .iter()
        .find_map(|u| match &u.node {
            Unit::Operator(def) if def.name.node == "Next" => Some(def),
            _ => None,
        })
        .expect("Next not found");
    let ast_result = eval(&eval_ctx, &next_def.body).expect("AST eval failed");

    let program = TirProgram::from_modules(&module, &[]);
    let tir_result = program
        .eval_named_op(&eval_ctx, "Next")
        .expect("TIR eval failed");

    assert_eq!(
        ast_result, tir_result,
        "AST/TIR parity for Next(x=0, x'=2): AST={ast_result:?}, TIR={tir_result:?}"
    );
    assert_eq!(ast_result, Value::Bool(false));
}
