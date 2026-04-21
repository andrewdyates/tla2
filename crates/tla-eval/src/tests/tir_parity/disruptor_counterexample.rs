// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Synthetic Disruptor NoDataRaces counterexample parity.

use super::*;
use crate::cache::lifecycle::clear_for_test_reset;
use crate::tir::TirProgram;
use std::sync::Arc;
use tla_value::IntIntervalFunc;

const DISRUPTOR_NODATARACES_COUNTEREXAMPLE_MODULE: &str = "\
---- MODULE TirDisruptorNoDataRaces ----
VARIABLE ringbuffer
Card1(S) == IF S = {} THEN 0 ELSE 1
Or0 == ringbuffer.readers[0] = {} \\/ ringbuffer.writers[0] = {}
Or2 == ringbuffer.readers[2] = {} \\/ ringbuffer.writers[2] = {}
Quant == \\A i \\in 0..3 : ringbuffer.readers[i] = {} \\/ ringbuffer.writers[i] = {}
Card0 == Card1(ringbuffer.writers[0]) <= 1
Card2 == Card1(ringbuffer.writers[2]) <= 1
NoDataRaces == \\A i \\in 0..3 :
  /\\ ringbuffer.readers[i] = {} \\/ ringbuffer.writers[i] = {}
  /\\ Card1(ringbuffer.writers[i]) <= 1
====";

const DISRUPTOR_NODATARACES_INSTANCE_INNER_MODULE: &str = "\
---- MODULE TirDisruptorNoDataRacesInner ----
VARIABLE ringbuffer
Card1(S) == IF S = {} THEN 0 ELSE 1
Or0 == ringbuffer.readers[0] = {} \\/ ringbuffer.writers[0] = {}
Or2 == ringbuffer.readers[2] = {} \\/ ringbuffer.writers[2] = {}
Quant == \\A i \\in 0..3 : ringbuffer.readers[i] = {} \\/ ringbuffer.writers[i] = {}
Card0 == Card1(ringbuffer.writers[0]) <= 1
Card2 == Card1(ringbuffer.writers[2]) <= 1
NoDataRaces == \\A i \\in 0..3 :
  /\\ ringbuffer.readers[i] = {} \\/ ringbuffer.writers[i] = {}
  /\\ Card1(ringbuffer.writers[i]) <= 1
====";

const DISRUPTOR_NODATARACES_INSTANCE_MAIN_MODULE: &str = "\
---- MODULE TirDisruptorNoDataRacesMain ----
Buffer == INSTANCE TirDisruptorNoDataRacesInner
Or0 == Buffer!Or0
Or2 == Buffer!Or2
Quant == Buffer!Quant
Card0 == Buffer!Card0
Card2 == Buffer!Card2
NoDataRaces == Buffer!NoDataRaces
====";

fn disruptor_nodataraces_counterexample_state() -> Value {
    let readers = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        0,
        3,
        vec![
            Value::set([Value::string("r1"), Value::string("r2")]),
            Value::empty_set(),
            Value::empty_set(),
            Value::empty_set(),
        ],
    )));
    let writers = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        0,
        3,
        vec![
            Value::empty_set(),
            Value::empty_set(),
            Value::set([Value::string("w2")]),
            Value::empty_set(),
        ],
    )));
    Value::record([("readers", readers), ("writers", writers)])
}

fn assert_parity_with_ringbuffer_state(module: &Module, name: &str) {
    let state = vec![disruptor_nodataraces_counterexample_state()];

    clear_for_test_reset();
    let mut ast_ctx = EvalCtx::new();
    ast_ctx.register_var("ringbuffer");
    ast_ctx.load_module(module);
    let ast_value = {
        let _state_guard = ast_ctx.bind_state_array_guard(&state);
        ast_ctx
            .eval_op(name)
            .unwrap_or_else(|err| panic!("AST eval of '{name}' failed: {err}"))
    };

    clear_for_test_reset();
    let program = TirProgram::from_modules(module, &[]);
    let mut tir_ctx = EvalCtx::new();
    tir_ctx.register_var("ringbuffer");
    tir_ctx.load_module(module);
    let tir_value = {
        let _state_guard = tir_ctx.bind_state_array_guard(&state);
        program
            .eval_named_op(&tir_ctx, name)
            .unwrap_or_else(|err| panic!("TIR eval of '{name}' failed: {err}"))
    };

    assert_eq!(
        ast_value, tir_value,
        "AST/TIR parity mismatch for '{name}' on the Disruptor NoDataRaces counterexample state: AST={ast_value:?}, TIR={tir_value:?}"
    );
}

fn assert_instance_wrapper_parity_with_ringbuffer_state(
    main_module: &Module,
    inner_module: &Module,
    name: &str,
) {
    let state = vec![disruptor_nodataraces_counterexample_state()];

    clear_for_test_reset();
    let mut ast_ctx = EvalCtx::new();
    ast_ctx.register_var("ringbuffer");
    ast_ctx.load_module(main_module);
    ast_ctx.load_instance_module(inner_module.name.node.clone(), inner_module);
    let ast_value = {
        let _state_guard = ast_ctx.bind_state_array_guard(&state);
        ast_ctx
            .eval_op(name)
            .unwrap_or_else(|err| panic!("AST eval of '{name}' failed: {err}"))
    };

    clear_for_test_reset();
    let program = TirProgram::from_modules(main_module, &[inner_module]);
    let mut tir_ctx = EvalCtx::new();
    tir_ctx.register_var("ringbuffer");
    tir_ctx.load_module(main_module);
    tir_ctx.load_instance_module(inner_module.name.node.clone(), inner_module);
    let tir_value = {
        let _state_guard = tir_ctx.bind_state_array_guard(&state);
        program
            .eval_named_op(&tir_ctx, name)
            .unwrap_or_else(|err| panic!("TIR eval of '{name}' failed: {err}"))
    };

    assert_eq!(
        ast_value, tir_value,
        "AST/TIR parity mismatch for instance-wrapped '{name}' on the Disruptor NoDataRaces counterexample state: AST={ast_value:?}, TIR={tir_value:?}"
    );
}

#[test]
fn test_tir_parity_disruptor_nodataraces_counterexample_slot0_disjunction() {
    let module = parse_module(DISRUPTOR_NODATARACES_COUNTEREXAMPLE_MODULE);
    assert_parity_with_ringbuffer_state(&module, "Or0");
}

#[test]
fn test_tir_parity_disruptor_nodataraces_counterexample_slot2_disjunction() {
    let module = parse_module(DISRUPTOR_NODATARACES_COUNTEREXAMPLE_MODULE);
    assert_parity_with_ringbuffer_state(&module, "Or2");
}

#[test]
fn test_tir_parity_disruptor_nodataraces_counterexample_quantifier_only() {
    let module = parse_module(DISRUPTOR_NODATARACES_COUNTEREXAMPLE_MODULE);
    assert_parity_with_ringbuffer_state(&module, "Quant");
}

#[test]
fn test_tir_parity_disruptor_nodataraces_counterexample_slot0_cardinality() {
    let module = parse_module(DISRUPTOR_NODATARACES_COUNTEREXAMPLE_MODULE);
    assert_parity_with_ringbuffer_state(&module, "Card0");
}

#[test]
fn test_tir_parity_disruptor_nodataraces_counterexample_slot2_cardinality() {
    let module = parse_module(DISRUPTOR_NODATARACES_COUNTEREXAMPLE_MODULE);
    assert_parity_with_ringbuffer_state(&module, "Card2");
}

#[test]
fn test_tir_parity_disruptor_nodataraces_counterexample_full_invariant() {
    let module = parse_module(DISRUPTOR_NODATARACES_COUNTEREXAMPLE_MODULE);
    assert_parity_with_ringbuffer_state(&module, "NoDataRaces");
}

#[test]
fn test_tir_parity_disruptor_nodataraces_instance_wrapper_slot0_disjunction() {
    let inner = parse_module(DISRUPTOR_NODATARACES_INSTANCE_INNER_MODULE);
    let main = parse_module(DISRUPTOR_NODATARACES_INSTANCE_MAIN_MODULE);
    assert_instance_wrapper_parity_with_ringbuffer_state(&main, &inner, "Or0");
}

#[test]
fn test_tir_parity_disruptor_nodataraces_instance_wrapper_quantifier_only() {
    let inner = parse_module(DISRUPTOR_NODATARACES_INSTANCE_INNER_MODULE);
    let main = parse_module(DISRUPTOR_NODATARACES_INSTANCE_MAIN_MODULE);
    assert_instance_wrapper_parity_with_ringbuffer_state(&main, &inner, "Quant");
}

#[test]
fn test_tir_parity_disruptor_nodataraces_instance_wrapper_full_invariant() {
    let inner = parse_module(DISRUPTOR_NODATARACES_INSTANCE_INNER_MODULE);
    let main = parse_module(DISRUPTOR_NODATARACES_INSTANCE_MAIN_MODULE);
    assert_instance_wrapper_parity_with_ringbuffer_state(&main, &inner, "NoDataRaces");
}
