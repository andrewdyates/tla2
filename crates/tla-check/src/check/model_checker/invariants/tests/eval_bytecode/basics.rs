// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Foundational bytecode invariant tests: compact array state execution
//! and config-constant binding/compilation.

use super::*;
use crate::config::ConstantValue;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_invariants_array_bytecode_uses_compact_array_state() {
    let mut module = parse_module(
        r#"
---- MODULE BytecodeInvariantCompactState ----
VARIABLE x
Init == x = 42
Next == x' = x
Safety == x = 42
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };
    let registry = {
        let checker = ModelChecker::new(&module, &config);
        checker.ctx.var_registry().clone()
    };

    for unit in &mut module.units {
        if let Unit::Operator(def) = &mut unit.node {
            tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
        }
    }

    let bytecode =
        tla_eval::bytecode_vm::compile_operators_to_bytecode(&module, &[], &config.invariants);
    assert!(
        bytecode.op_indices.contains_key("Safety"),
        "test invariant should compile to bytecode"
    );
    let mut checker = ModelChecker::new(&module, &config);
    checker.bytecode = Some(bytecode);

    let pass = ArrayState::from_state(&State::from_pairs([("x", Value::int(42))]), &registry);
    assert_eq!(
        checker
            .check_invariants_array(&pass)
            .expect("bytecode invariant should pass"),
        None
    );

    let fail = ArrayState::from_state(&State::from_pairs([("x", Value::int(7))]), &registry);
    assert_eq!(
        checker
            .check_invariants_array(&fail)
            .expect("bytecode invariant should report violation"),
        Some("Safety".to_string())
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_invariants_array_bytecode_resolves_config_constants() {
    let mut module = parse_module(
        r#"
---- MODULE BytecodeInvariantConfigConst ----
CONSTANT N
VARIABLE x
Init == x = 2
Next == x' = x
Safety == x < N
====
"#,
    );
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };
    config
        .constants
        .insert("N".to_string(), ConstantValue::Value("3".to_string()));
    config.constants_order.push("N".to_string());

    let registry = {
        let checker = ModelChecker::new(&module, &config);
        checker.ctx.var_registry().clone()
    };

    for unit in &mut module.units {
        if let Unit::Operator(def) = &mut unit.node {
            tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
        }
    }

    let mut checker = ModelChecker::new(&module, &config);
    crate::constants::bind_constants_from_config(&mut checker.ctx, &config)
        .expect("config constant should bind");
    crate::check::model_checker::promote_env_constants_to_precomputed(&mut checker.ctx);

    let bytecode = tla_eval::bytecode_vm::compile_operators_to_bytecode_with_constants(
        &module,
        &[],
        &config.invariants,
        checker.ctx.precomputed_constants(),
    );
    assert!(
        bytecode.op_indices.contains_key("Safety"),
        "invariant using config constant should compile to bytecode"
    );
    checker.bytecode = Some(bytecode);

    let pass = ArrayState::from_state(&State::from_pairs([("x", Value::int(2))]), &registry);
    assert_eq!(
        checker
            .check_invariants_array(&pass)
            .expect("bytecode invariant should pass"),
        None
    );

    let fail = ArrayState::from_state(&State::from_pairs([("x", Value::int(3))]), &registry);
    assert_eq!(
        checker
            .check_invariants_array(&fail)
            .expect("bytecode invariant should report violation"),
        Some("Safety".to_string())
    );
}
