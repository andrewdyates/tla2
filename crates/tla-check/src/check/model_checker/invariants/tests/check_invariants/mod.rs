// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `check_invariants_array`: pass, fail, non-boolean, empty, first-fail.

use super::*;
use crate::resolve_spec_from_config_with_extends;
use crate::EvalCheckError;
use std::path::PathBuf;
use std::sync::Arc;
use tla_core::{compute_is_recursive, parse_to_syntax_tree, FileId, ModuleLoader};
use tla_value::{FuncBuilder, IntIntervalFunc};

mod basics;
mod real_disruptor;
mod tir_eval;

fn model_value(name: &str) -> Value {
    Value::try_model_value(name).expect("test model value should intern")
}

fn general_func(entries: impl IntoIterator<Item = (Value, Value)>) -> Value {
    let mut builder = FuncBuilder::new();
    for (key, value) in entries {
        builder.insert(key, value);
    }
    Value::Func(Arc::new(builder.build()))
}

fn real_disruptor_mpmc_trace_state7() -> State {
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
    State::from_pairs([
        ("ringbuffer", ringbuffer),
        ("next_sequence", Value::int(3)),
        (
            "claimed_sequence",
            general_func([
                (model_value("w1"), Value::int(2)),
                (model_value("w2"), Value::int(1)),
            ]),
        ),
        (
            "published",
            Value::IntFunc(Arc::new(IntIntervalFunc::new(
                0,
                3,
                vec![
                    Value::bool(true),
                    Value::bool(false),
                    Value::bool(false),
                    Value::bool(false),
                ],
            ))),
        ),
        (
            "read",
            general_func([
                (model_value("r1"), Value::int(-1)),
                (model_value("r2"), Value::int(-1)),
                (model_value("r3"), Value::int(-1)),
            ]),
        ),
        (
            "pc",
            general_func([
                (model_value("r1"), Value::string("Access")),
                (model_value("r2"), Value::string("Access")),
                (model_value("r3"), Value::string("Advance")),
                (model_value("w1"), Value::string("Access")),
                (model_value("w2"), Value::string("Access")),
            ]),
        ),
        (
            "consumed",
            general_func([
                (model_value("r1"), Value::seq([Value::int(0)])),
                (model_value("r2"), Value::seq([Value::int(0)])),
                (model_value("r3"), Value::seq([])),
            ]),
        ),
    ])
}

fn real_disruptor_mpmc_counterexample_state() -> State {
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
    State::from_pairs([
        ("ringbuffer", ringbuffer),
        ("next_sequence", Value::int(3)),
        (
            "claimed_sequence",
            general_func([
                (model_value("w1"), Value::int(2)),
                (model_value("w2"), Value::int(1)),
            ]),
        ),
        (
            "published",
            Value::IntFunc(Arc::new(IntIntervalFunc::new(
                0,
                3,
                vec![
                    Value::bool(true),
                    Value::bool(false),
                    Value::bool(false),
                    Value::bool(false),
                ],
            ))),
        ),
        (
            "read",
            general_func([
                (model_value("r1"), Value::int(0)),
                (model_value("r2"), Value::int(-1)),
                (model_value("r3"), Value::int(-1)),
            ]),
        ),
        (
            "pc",
            general_func([
                (model_value("r1"), Value::string("Advance")),
                (model_value("r2"), Value::string("Access")),
                (model_value("r3"), Value::string("Advance")),
                (model_value("w1"), Value::string("Access")),
                (model_value("w2"), Value::string("Access")),
            ]),
        ),
        (
            "consumed",
            general_func([
                (model_value("r1"), Value::seq([Value::int(0)])),
                (model_value("r2"), Value::seq([Value::int(0)])),
                (model_value("r3"), Value::seq([])),
            ]),
        ),
    ])
}

fn load_real_disruptor_mpmc_modules_with_cfg(
    cfg_name: &str,
) -> (
    tla_core::ast::Module,
    Vec<tla_core::ast::Module>,
    Config,
    crate::ResolvedSpec,
) {
    let spec_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples/test/disruptor");
    let spec_path = spec_dir.join("Disruptor_MPMC.tla");
    let cfg_path = spec_dir.join(cfg_name);

    let spec_source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", spec_path.display(), e));
    let tree = parse_to_syntax_tree(&spec_source);
    let mut module = tla_core::lower(FileId(0), &tree)
        .module
        .expect("Disruptor_MPMC should lower successfully");
    compute_is_recursive(&mut module);

    let mut loader = ModuleLoader::new(&spec_path);
    loader.seed_from_syntax_tree(&tree, &spec_path);
    loader
        .load_extends(&module)
        .expect("Disruptor_MPMC EXTENDS dependencies should load");
    loader
        .load_instances(&module)
        .expect("Disruptor_MPMC INSTANCE dependencies should load");

    let (extended_modules_for_resolve, instanced_modules_for_resolve) =
        loader.modules_for_semantic_resolution(&module);
    let checker_modules: Vec<_> = loader
        .modules_for_model_checking(&module)
        .into_iter()
        .cloned()
        .collect();
    let spec_scope_module_names: Vec<&str> = extended_modules_for_resolve
        .iter()
        .chain(instanced_modules_for_resolve.iter())
        .map(|m| m.name.node.as_str())
        .collect();
    let extended_syntax_trees: Vec<_> = spec_scope_module_names
        .iter()
        .filter_map(|name| loader.get(name).map(|loaded| &loaded.syntax_tree))
        .collect();

    let config_source = std::fs::read_to_string(&cfg_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {}", cfg_path.display(), e));
    let mut config = Config::parse(&config_source).unwrap_or_else(|errors| {
        panic!(
            "Failed to parse {}: {} error(s)",
            cfg_path.display(),
            errors.len()
        )
    });
    let resolved = resolve_spec_from_config_with_extends(&config, &tree, &extended_syntax_trees)
        .expect("Disruptor_MPMC SPECIFICATION should resolve across extended modules");
    if config.init.is_none() {
        config.init = Some(resolved.init.clone());
    }
    if config.next.is_none() {
        config.next = Some(resolved.next.clone());
    }

    (module, checker_modules, config, resolved)
}

fn load_real_disruptor_mpmc_modules() -> (tla_core::ast::Module, Vec<tla_core::ast::Module>, Config)
{
    let (module, checker_modules, config, _resolved) =
        load_real_disruptor_mpmc_modules_with_cfg("Disruptor_MPMC.cfg");
    (module, checker_modules, config)
}

fn prepare_invariants_with_promoted_property(mc: &mut ModelChecker<'_>) {
    // Part of #3354 Slice 2: config invariants route through the canonical eval
    // path (ctx.eval_op / eval_named_op), not compiled guards. PROPERTY state
    // invariants route through eval_state_invariants.
    let classification = crate::checker_ops::classify_property_safety_parts(
        &mc.ctx,
        &mc.config.properties,
        &mc.module.op_defs,
    );
    mc.compiled.promoted_property_invariants = classification.promoted_invariant_properties;
    mc.compiled.eval_state_invariants = classification.eval_state_invariants;
}
