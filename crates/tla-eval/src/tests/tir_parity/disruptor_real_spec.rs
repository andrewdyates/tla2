// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Real Disruptor_MPMC fixture loading and named-op reuse regressions.

use super::*;
use crate::cache::lifecycle::clear_for_test_reset;
use crate::tir::TirProgram;
use std::sync::Arc;
use tla_core::ast::Unit;
use tla_core::name_intern::intern_name;
use tla_value::{FuncBuilder, IntIntervalFunc};

const REAL_DISRUPTOR_MPMC_MODULE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../examples/test/disruptor/Disruptor_MPMC.tla"
));

const REAL_DISRUPTOR_RINGBUFFER_MODULE: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../examples/test/disruptor/RingBuffer.tla"
));

fn model_value(name: &str) -> Value {
    Value::try_model_value(name).unwrap_or_else(|err| {
        panic!("failed to create model value '{name}': {err}");
    })
}

fn general_func(entries: impl IntoIterator<Item = (Value, Value)>) -> Value {
    let mut builder = FuncBuilder::new();
    for (key, value) in entries {
        builder.insert(key, value);
    }
    Value::Func(Arc::new(builder.build()))
}

fn bind_precomputed_constant(ctx: &mut EvalCtx, name: &str, value: Value) {
    let key: Arc<str> = Arc::from(name);
    ctx.env_mut().insert(key, value.clone());
    let shared = Arc::make_mut(ctx.shared_arc_mut());
    shared.config_constants.insert(name.to_string());
    shared
        .precomputed_constants_mut()
        .insert(intern_name(name), value);
}

fn bind_disruptor_mpmc_constants(ctx: &mut EvalCtx) {
    bind_precomputed_constant(ctx, "MaxPublished", Value::int(10));
    bind_precomputed_constant(
        ctx,
        "Writers",
        Value::set([model_value("w1"), model_value("w2")]),
    );
    bind_precomputed_constant(
        ctx,
        "Readers",
        Value::set([model_value("r1"), model_value("r2"), model_value("r3")]),
    );
    bind_precomputed_constant(ctx, "Size", Value::int(4));
    bind_precomputed_constant(ctx, "NULL", model_value("NULL"));
}

fn register_state_vars_from_module(ctx: &mut EvalCtx, module: &Module) {
    for unit in &module.units {
        if let Unit::Variable(vars) = &unit.node {
            for name in vars {
                ctx.register_var(name.node.clone());
            }
        }
    }
}

fn build_real_disruptor_mpmc_ctx(main_module: &Module, ringbuffer_module: &Module) -> EvalCtx {
    let mut ctx = EvalCtx::new();
    {
        let shared = Arc::make_mut(ctx.shared_arc_mut());
        for ext in &main_module.extends {
            shared.extended_module_names.insert(ext.node.clone());
        }
    }
    ctx.load_module(main_module);
    ctx.load_instance_module_with_extends(
        ringbuffer_module.name.node.clone(),
        ringbuffer_module,
        &[(ringbuffer_module.name.node.as_str(), ringbuffer_module)]
            .into_iter()
            .collect::<rustc_hash::FxHashMap<_, _>>(),
    );
    register_state_vars_from_module(&mut ctx, main_module);
    ctx.resolve_state_vars_in_loaded_ops();
    bind_disruptor_mpmc_constants(&mut ctx);
    ctx
}

fn real_disruptor_mpmc_trace_state7() -> Vec<Value> {
    let ringbuffer = Value::record([
        (
            "readers",
            Value::IntFunc(Arc::new(IntIntervalFunc::new(
                0,
                3,
                vec![
                    Value::set([model_value("r1"), model_value("r2")]),
                    Value::empty_set(),
                    Value::empty_set(),
                    Value::empty_set(),
                ],
            ))),
        ),
        (
            "writers",
            Value::IntFunc(Arc::new(IntIntervalFunc::new(
                0,
                3,
                vec![
                    Value::empty_set(),
                    Value::set([model_value("w2")]),
                    Value::set([model_value("w1")]),
                    Value::empty_set(),
                ],
            ))),
        ),
        (
            "slots",
            Value::IntFunc(Arc::new(IntIntervalFunc::new(
                0,
                3,
                vec![
                    Value::int(0),
                    Value::int(1),
                    Value::int(2),
                    model_value("NULL"),
                ],
            ))),
        ),
    ]);
    let claimed_sequence = general_func([
        (model_value("w1"), Value::int(2)),
        (model_value("w2"), Value::int(1)),
    ]);
    let published = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        0,
        3,
        vec![
            Value::bool(true),
            Value::bool(false),
            Value::bool(false),
            Value::bool(false),
        ],
    )));
    let read = general_func([
        (model_value("r1"), Value::int(-1)),
        (model_value("r2"), Value::int(-1)),
        (model_value("r3"), Value::int(-1)),
    ]);
    let pc = general_func([
        (model_value("r1"), Value::string("Access")),
        (model_value("r2"), Value::string("Access")),
        (model_value("r3"), Value::string("Advance")),
        (model_value("w1"), Value::string("Access")),
        (model_value("w2"), Value::string("Access")),
    ]);
    let consumed = general_func([
        (model_value("r1"), Value::seq([Value::int(0)])),
        (model_value("r2"), Value::seq([Value::int(0)])),
        (model_value("r3"), Value::seq([])),
    ]);
    vec![
        ringbuffer,
        Value::int(3),
        claimed_sequence,
        published,
        read,
        pc,
        consumed,
    ]
}

fn real_disruptor_mpmc_trace_state8() -> Vec<Value> {
    let ringbuffer = Value::record([
        (
            "readers",
            Value::IntFunc(Arc::new(IntIntervalFunc::new(
                0,
                3,
                vec![
                    Value::set([model_value("r2")]),
                    Value::empty_set(),
                    Value::empty_set(),
                    Value::empty_set(),
                ],
            ))),
        ),
        (
            "writers",
            Value::IntFunc(Arc::new(IntIntervalFunc::new(
                0,
                3,
                vec![
                    Value::empty_set(),
                    Value::set([model_value("w2")]),
                    Value::set([model_value("w1")]),
                    Value::empty_set(),
                ],
            ))),
        ),
        (
            "slots",
            Value::IntFunc(Arc::new(IntIntervalFunc::new(
                0,
                3,
                vec![
                    Value::int(0),
                    Value::int(1),
                    Value::int(2),
                    model_value("NULL"),
                ],
            ))),
        ),
    ]);
    let claimed_sequence = general_func([
        (model_value("w1"), Value::int(2)),
        (model_value("w2"), Value::int(1)),
    ]);
    let published = Value::IntFunc(Arc::new(IntIntervalFunc::new(
        0,
        3,
        vec![
            Value::bool(true),
            Value::bool(false),
            Value::bool(false),
            Value::bool(false),
        ],
    )));
    let read = general_func([
        (model_value("r1"), Value::int(0)),
        (model_value("r2"), Value::int(-1)),
        (model_value("r3"), Value::int(-1)),
    ]);
    let pc = general_func([
        (model_value("r1"), Value::string("Advance")),
        (model_value("r2"), Value::string("Access")),
        (model_value("r3"), Value::string("Advance")),
        (model_value("w1"), Value::string("Access")),
        (model_value("w2"), Value::string("Access")),
    ]);
    let consumed = general_func([
        (model_value("r1"), Value::seq([Value::int(0)])),
        (model_value("r2"), Value::seq([Value::int(0)])),
        (model_value("r3"), Value::seq([])),
    ]);
    vec![
        ringbuffer,
        Value::int(3),
        claimed_sequence,
        published,
        read,
        pc,
        consumed,
    ]
}

#[test]
fn test_tir_parity_real_disruptor_mpmc_nodataraces_counterexample_state() {
    let main = parse_module_with_file_id(FileId(0), REAL_DISRUPTOR_MPMC_MODULE);
    let ringbuffer = parse_module_with_file_id(FileId(1), REAL_DISRUPTOR_RINGBUFFER_MODULE);
    let state = real_disruptor_mpmc_trace_state8();

    clear_for_test_reset();
    let mut ast_ctx = build_real_disruptor_mpmc_ctx(&main, &ringbuffer);
    let ast_value = {
        let _state_guard = ast_ctx.bind_state_array_guard(&state);
        ast_ctx.eval_op("NoDataRaces").unwrap_or_else(|err| {
            panic!("AST eval of real Disruptor_MPMC NoDataRaces failed: {err}")
        })
    };
    assert_eq!(
        ast_value,
        Value::bool(true),
        "real Disruptor_MPMC counterexample state should satisfy NoDataRaces under AST eval"
    );

    clear_for_test_reset();
    let program = TirProgram::from_modules(&main, &[&ringbuffer]);
    let mut tir_ctx = build_real_disruptor_mpmc_ctx(&main, &ringbuffer);
    let tir_value = {
        let _state_guard = tir_ctx.bind_state_array_guard(&state);
        program
            .eval_named_op(&tir_ctx, "NoDataRaces")
            .unwrap_or_else(|err| {
                panic!("TIR eval of real Disruptor_MPMC NoDataRaces failed: {err}")
            })
    };

    assert_eq!(
        tir_value, ast_value,
        "AST/TIR parity mismatch for real Disruptor_MPMC NoDataRaces on the checker counterexample state: AST={ast_value:?}, TIR={tir_value:?}"
    );
}

#[test]
fn test_tir_named_op_real_disruptor_mpmc_nodataraces_state_transition() {
    let main = parse_module_with_file_id(FileId(0), REAL_DISRUPTOR_MPMC_MODULE);
    let ringbuffer = parse_module_with_file_id(FileId(1), REAL_DISRUPTOR_RINGBUFFER_MODULE);
    let state7 = real_disruptor_mpmc_trace_state7();
    let state8 = real_disruptor_mpmc_trace_state8();

    clear_for_test_reset();
    let mut ast_ctx = build_real_disruptor_mpmc_ctx(&main, &ringbuffer);
    {
        let _state_guard = ast_ctx.bind_state_array_guard(&state7);
        assert_eq!(
            ast_ctx
                .eval_op("NoDataRaces")
                .expect("AST eval of state 7 NoDataRaces should succeed"),
            Value::bool(true),
            "trace state 7 should satisfy NoDataRaces under AST eval"
        );
    }
    let ast_state8 = {
        let _state_guard = ast_ctx.bind_state_array_guard(&state8);
        ast_ctx
            .eval_op("NoDataRaces")
            .expect("AST eval of state 8 NoDataRaces should succeed")
    };
    assert_eq!(
        ast_state8,
        Value::bool(true),
        "trace state 8 should satisfy NoDataRaces under AST eval after state 7"
    );

    clear_for_test_reset();
    let program = TirProgram::from_modules(&main, &[&ringbuffer]);
    let mut tir_ctx = build_real_disruptor_mpmc_ctx(&main, &ringbuffer);
    {
        let _state_guard = tir_ctx.bind_state_array_guard(&state7);
        assert_eq!(
            crate::eval_entry_with(&tir_ctx, || program.eval_named_op(&tir_ctx, "NoDataRaces"))
                .expect("TIR eval of state 7 NoDataRaces should succeed"),
            Value::bool(true),
            "trace state 7 should satisfy NoDataRaces under TIR eval"
        );
    }
    let tir_state8 = {
        let _state_guard = tir_ctx.bind_state_array_guard(&state8);
        crate::eval_entry_with(&tir_ctx, || program.eval_named_op(&tir_ctx, "NoDataRaces"))
            .expect("TIR eval of state 8 NoDataRaces should succeed")
    };

    assert_eq!(
        tir_state8, ast_state8,
        "reused TIR named-op evaluation should match AST on Disruptor_MPMC state 8 after evaluating state 7 first: AST={ast_state8:?}, TIR={tir_state8:?}"
    );
}
