// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! JIT successor hot-path tests.

use super::*;
use tla_core::ast::{Expr, OperatorDef, Unit};
use tla_core::span::Spanned;

fn build_jit_cache(
    module: &tla_core::ast::Module,
    registry: &crate::var_index::VarRegistry,
    invariants: &[String],
) -> tla_jit::bytecode_lower::JitInvariantCache {
    let mut compiled_module = module.clone();
    for unit in &mut compiled_module.units {
        if let Unit::Operator(def) = &mut unit.node {
            tla_eval::state_var::resolve_state_vars_in_op_def(def, registry);
        }
    }

    let bytecode =
        tla_eval::bytecode_vm::compile_operators_to_bytecode(&compiled_module, &[], invariants);
    assert!(
        bytecode.op_indices.contains_key(&invariants[0]),
        "test invariant should compile to bytecode and JIT"
    );
    tla_jit::bytecode_lower::JitInvariantCache::build(&bytecode.chunk, &bytecode.op_indices)
        .expect("JIT cache should build for test invariant")
}

fn make_false_op(name: &str) -> OperatorDef {
    OperatorDef {
        name: Spanned::dummy(name.to_string()),
        params: vec![],
        body: Spanned::dummy(Expr::Bool(false)),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    }
}

fn make_true_op(name: &str) -> OperatorDef {
    OperatorDef {
        name: Spanned::dummy(name.to_string()),
        params: vec![],
        body: Spanned::dummy(Expr::Bool(true)),
        local: false,
        contains_prime: false,
        guards_depend_on_prime: false,
        has_primed_param: false,
        is_recursive: false,
        self_call_count: 0,
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_successor_invariant_jit_hot_path_precedes_tree_walk() {
    let module = parse_module(
        r#"
---- MODULE JitSuccessorHotPath ----
VARIABLE x
Init == x = 1
Next == x' = x
Inv == x > 0
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    mc.tir_parity = None;
    let registry = mc.ctx.var_registry().clone();

    mc.jit_cache = Some(build_jit_cache(&module, &registry, &config.invariants));
    mc.bytecode = None;
    mc.ctx.define_op("Inv".to_string(), make_false_op("Inv"));

    let succ = ArrayState::from_state(&State::from_pairs([("x", Value::int(1))]), &registry);
    let outcome = mc.check_successor_invariant(Fingerprint(0), &succ, Fingerprint(1), 1);

    assert!(
        matches!(outcome, crate::checker_ops::InvariantOutcome::Ok),
        "successor hot path should accept the JIT result before consulting the overridden eval op"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_flatten_state_to_i64_reuses_caller_buffer() {
    let module = parse_module(
        r#"
---- MODULE JitFlattenScratch ----
VARIABLE x, y
Init == /\ x = 1
        /\ y = TRUE
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        ..Default::default()
    };
    let mc = ModelChecker::new(&module, &config);
    let registry = mc.ctx.var_registry().clone();
    let state = ArrayState::from_state(
        &State::from_pairs([("x", Value::int(1)), ("y", Value::bool(true))]),
        &registry,
    );

    let mut scratch = Vec::with_capacity(state.len());
    // Use selective flattening with empty required_vars (all vars).
    assert!(crate::check::model_checker::invariants::flatten_state_to_i64_selective(
        &state,
        &mut scratch,
        &[],
    ));
    assert_eq!(scratch, vec![1, 1]);
    let scratch_ptr = scratch.as_ptr();

    assert!(crate::check::model_checker::invariants::flatten_state_to_i64_selective(
        &state,
        &mut scratch,
        &[],
    ));
    assert_eq!(scratch, vec![1, 1]);
    assert_eq!(
        scratch.as_ptr(),
        scratch_ptr,
        "flatten_state_to_i64_selective should reuse the caller-provided allocation"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_successor_invariant_jit_falls_back_for_unflattenable_state() {
    // Part of #3908: With selective flattening, the JIT path is no longer
    // blocked by unreferenced compound variables. When Inv only reads `x`
    // and `y` is a ModelValue, selective flattening skips serializing `y`
    // and the JIT evaluates successfully.
    //
    // The invariant `x > 0` is TRUE for x=1, so JIT returns Ok (no violation).
    // The tree-walk path (which uses the overridden FALSE op) is NOT reached.
    let module = parse_module(
        r#"
---- MODULE JitSuccessorFallback ----
VARIABLE x, y
Init == /\ x = 1
        /\ y = 0
Next == /\ x' = x
        /\ y' = y
Inv == x > 0
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    mc.tir_parity = None;
    let registry = mc.ctx.var_registry().clone();

    mc.jit_cache = Some(build_jit_cache(&module, &registry, &config.invariants));
    mc.bytecode = None;
    mc.ctx.define_op("Inv".to_string(), make_false_op("Inv"));

    // Construct state with a ModelValue for `y` — previously this would cause
    // flatten_state_to_i64 to return false, forcing fallback. With selective
    // flattening (#3908), `y` is not in the required_vars for Inv (which only
    // reads `x`), so flattening succeeds and JIT evaluates correctly.
    let succ = ArrayState::from_state(
        &State::from_pairs([("x", Value::int(1)), ("y", model_value("mv_unflattenable"))]),
        &registry,
    );
    let outcome = mc.check_successor_invariant(Fingerprint(0), &succ, Fingerprint(1), 1);

    // JIT evaluates `x > 0` with x=1 → TRUE. No violation.
    assert!(
        matches!(outcome, crate::checker_ops::InvariantOutcome::Ok),
        "selective flattening should let JIT succeed when unreferenced vars are unflattenable"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_successor_invariant_jit_skips_checked_prefix_on_tree_walk_fallback() {
    let module = parse_module(
        r#"
---- MODULE JitSuccessorMixedFallback ----
VARIABLE x
Init == x = 1
Next == x' = x
Helper(v) == v > 0
InvJit == x > 0
InvCall == Helper(x)
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InvJit".to_string(), "InvCall".to_string()],
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    mc.tir_parity = None;
    let registry = mc.ctx.var_registry().clone();

    let jit_cache = build_jit_cache(&module, &registry, &config.invariants);
    assert_eq!(jit_cache.check_invariant("InvCall", &[1]), None);
    mc.jit_cache = Some(jit_cache);
    mc.bytecode = None;
    mc.ctx
        .define_op("InvJit".to_string(), make_false_op("InvJit"));

    let succ = ArrayState::from_state(&State::from_pairs([("x", Value::int(1))]), &registry);
    let outcome = mc.check_successor_invariant(Fingerprint(0), &succ, Fingerprint(1), 1);

    assert!(
        matches!(outcome, crate::checker_ops::InvariantOutcome::Ok),
        "tree-walk fallback should start at the first JIT-unchecked invariant, not re-evaluate the JIT-checked prefix"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_invariants_array_jit_verify_uses_interpreter_result_on_pass_mismatch() {
    let module = parse_module(
        r#"
---- MODULE JitVerifyPassMismatch ----
VARIABLE x
Init == x = 1
Next == x' = x
Inv == x > 0
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        jit_verify: true,
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    mc.tir_parity = None;
    let registry = mc.ctx.var_registry().clone();

    mc.jit_cache = Some(build_jit_cache(&module, &registry, &config.invariants));
    mc.bytecode = None;
    mc.ctx.define_op("Inv".to_string(), make_false_op("Inv"));

    let succ = ArrayState::from_state(&State::from_pairs([("x", Value::int(1))]), &registry);
    let outcome = mc.check_invariants_array(&succ).unwrap();

    assert_eq!(outcome, Some("Inv".to_string()));
    assert_eq!(mc.jit_verify_checked, 1);
    assert_eq!(mc.jit_verify_mismatches, 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_check_invariants_array_jit_verify_uses_interpreter_result_on_violation_mismatch() {
    let module = parse_module(
        r#"
---- MODULE JitVerifyViolationMismatch ----
VARIABLE x
Init == x = 1
Next == x' = x
Inv == x <= 0
====
"#,
    );
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        jit_verify: true,
        ..Default::default()
    };
    let mut mc = ModelChecker::new(&module, &config);
    mc.tir_parity = None;
    let registry = mc.ctx.var_registry().clone();

    mc.jit_cache = Some(build_jit_cache(&module, &registry, &config.invariants));
    mc.bytecode = None;
    mc.ctx.define_op("Inv".to_string(), make_true_op("Inv"));

    let succ = ArrayState::from_state(&State::from_pairs([("x", Value::int(1))]), &registry);
    let outcome = mc.check_invariants_array(&succ).unwrap();

    assert_eq!(outcome, None);
    assert_eq!(mc.jit_verify_checked, 1);
    assert_eq!(mc.jit_verify_mismatches, 1);
}
