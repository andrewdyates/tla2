// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::Arc;
use tla_core::name_intern::intern_name;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_zero_arg_cache_validates_next_deps_against_state_env_in_next_mode() {
    use crate::cache::{
        op_cache_entry_valid, CachedOpResult, OpEvalDeps, StateLookupMode, StateLookupModeGuard,
        VarDepMap,
    };

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let x_idx = ctx.var_registry().get("x").expect("x should be registered");

    let swapped_next_state = vec![Value::int(11)];
    ctx.bind_state_array(&swapped_next_state);
    ctx.stable_mut().next_state = None;
    let _ = ctx.take_next_state_env();

    let entry = CachedOpResult {
        value: Value::int(0),
        deps: OpEvalDeps {
            local: smallvec::smallvec![],
            state: VarDepMap::default(),
            next: VarDepMap::from_entries(&[(x_idx, Value::int(11))]),
            inconsistent: false,
            ..Default::default()
        },
    };

    let valid = {
        let _guard = StateLookupModeGuard::new(&ctx, StateLookupMode::Next);
        op_cache_entry_valid(&ctx, &entry)
    };
    assert!(
        valid,
        "next deps should validate from state_env when Next mode has swapped arrays"
    );

    let mismatched_swapped_state = vec![Value::int(12)];
    ctx.bind_state_array(&mismatched_swapped_state);
    let invalid = {
        let _guard = StateLookupModeGuard::new(&ctx, StateLookupMode::Next);
        op_cache_entry_valid(&ctx, &entry)
    };
    assert!(
        !invalid,
        "next deps must fail when swapped state_env differs from cached next value"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_zero_arg_cache_validates_next_deps_against_local_overlay_in_next_mode() {
    use crate::cache::{
        op_cache_entry_valid, CachedOpResult, OpEvalDeps, StateLookupMode, StateLookupModeGuard,
        VarDepMap,
    };

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let x_idx = ctx.var_registry().get("x").expect("x should be registered");

    let current_state = vec![Value::int(1)];
    ctx.bind_state_array(&current_state);
    ctx.push_binding(Arc::from("x"), Value::int(2));

    let entry = CachedOpResult {
        value: Value::int(0),
        deps: OpEvalDeps {
            local: smallvec::smallvec![],
            state: VarDepMap::default(),
            next: VarDepMap::from_entries(&[(x_idx, Value::int(2))]),
            inconsistent: false,
            ..Default::default()
        },
    };

    let valid = {
        let _guard = StateLookupModeGuard::new(&ctx, StateLookupMode::Next);
        op_cache_entry_valid(&ctx, &entry)
    };
    assert!(
        valid,
        "next deps should validate from local overlay before falling back to state_env"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_zero_arg_cache_validates_next_deps_against_env_overlay_in_next_mode() {
    use crate::cache::{
        op_cache_entry_valid, CachedOpResult, OpEvalDeps, StateLookupMode, StateLookupModeGuard,
        VarDepMap,
    };

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let x_idx = ctx.var_registry().get("x").expect("x should be registered");
    ctx.bind_mut("x", Value::int(7));

    let entry = CachedOpResult {
        value: Value::int(0),
        deps: OpEvalDeps {
            local: smallvec::smallvec![],
            state: VarDepMap::default(),
            next: VarDepMap::from_entries(&[(x_idx, Value::int(7))]),
            inconsistent: false,
            ..Default::default()
        },
    };

    let valid = {
        let _guard = StateLookupModeGuard::new(&ctx, StateLookupMode::Next);
        op_cache_entry_valid(&ctx, &entry)
    };
    assert!(
        valid,
        "next deps should validate from env when Next mode has no state/next arrays"
    );

    ctx.bind_mut("x", Value::int(8));
    let invalid = {
        let _guard = StateLookupModeGuard::new(&ctx, StateLookupMode::Next);
        op_cache_entry_valid(&ctx, &entry)
    };
    assert!(
        !invalid,
        "next deps must fail when env overlay differs from cached next value"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_zero_arg_cache_validates_local_deps_against_eager_binding_chain() {
    use crate::cache::{op_cache_entry_valid, CachedOpResult, OpEvalDeps, VarDepMap};
    use tla_value::CompactValue;

    let x_id = intern_name("x");
    let ctx = EvalCtx::new().bind_local("x", Value::int(7));

    let entry = CachedOpResult {
        value: Value::int(0),
        deps: OpEvalDeps {
            local: smallvec::smallvec![(x_id, CompactValue::from(7_i64))],
            state: VarDepMap::default(),
            next: VarDepMap::default(),
            inconsistent: false,
            ..Default::default()
        },
    };
    assert!(
        op_cache_entry_valid(&ctx, &entry),
        "local deps should validate against eager compact BindingChain values"
    );

    let mismatched = CachedOpResult {
        value: Value::int(0),
        deps: OpEvalDeps {
            local: smallvec::smallvec![(x_id, CompactValue::from(8_i64))],
            state: VarDepMap::default(),
            next: VarDepMap::default(),
            inconsistent: false,
            ..Default::default()
        },
    };
    assert!(
        !op_cache_entry_valid(&ctx, &mismatched),
        "local dep validation must fail when the eager BindingChain value differs"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_zero_arg_prime_cache_reuses_entry_in_swapped_array_next_mode() {
    use crate::cache::{zero_arg_op_cache_clear, zero_arg_op_cache_entry_count};

    let src = r#"
---- MODULE Test ----
VARIABLE x
Foo == x
Op == Foo'
===="#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("lower produced no module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);

    let next = vec![Value::int(2)];
    ctx.bind_next_state_array(&next);

    zero_arg_op_cache_clear();
    let op_def = ctx.get_op("Op").expect("Op not found").clone();

    let first = eval(&ctx, &op_def.body).expect("first evaluation should succeed");
    assert_eq!(first, Value::int(2));
    let entries_after_first = zero_arg_op_cache_entry_count();
    assert!(
        entries_after_first >= 1,
        "first eval should cache at least one zero-arg operator result"
    );

    let second = eval(&ctx, &op_def.body).expect("second evaluation should succeed");
    assert_eq!(second, Value::int(2));
    let entries_after_second = zero_arg_op_cache_entry_count();
    assert_eq!(
        entries_after_second, entries_after_first,
        "re-evaluating Foo' in swapped-array next mode must hit cache instead of appending misses"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_ident_binding_chain_dep_recording() {
    // Part of #2955: Verifies that BindingChain reads are correctly recorded as
    // local deps during dep tracking. This was previously broken with FastBinding
    // (#1497) but is now fixed because BindingChain uses record_local_read.
    use crate::cache::eval_with_dep_tracking;

    let src = r#"
---- MODULE Test ----
VARIABLE x
Foo == x
===="#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("lower produced no module");

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");

    // Set x = 1 in state_env (the normal state variable path)
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);

    // Shadow x with a local binding (simulating a quantifier binding x = 5)
    let ctx_with_binding = ctx.bind("x", Value::int(5));

    // Evaluate Foo's body (which is just `x`) with dep tracking.
    // eval_ident should find x in BindingChain and return 5.
    let op_def = ctx_with_binding
        .get_op("Foo")
        .expect("Foo not found")
        .clone();
    let (value, deps) = eval_with_dep_tracking(&ctx_with_binding, &op_def.body)
        .expect("eval_with_dep_tracking should succeed");

    // BindingChain shadows state_env, so value should be 5
    assert_eq!(
        value,
        Value::int(5),
        "x should resolve from BindingChain (5) not state_env (1)"
    );

    // Part of #2955: BindingChain reads are properly recorded as local deps
    // (via record_local_read), fixing the #1497 bug where fast_bindings
    // reads were silently dropped.
    assert!(
        !deps.local.is_empty(),
        "deps.local should contain x binding (BindingChain records deps correctly)"
    );

    // BindingChain resolved before state_env, so no state dep is recorded.
    assert!(
        deps.state.is_empty(),
        "No state dep should be recorded — BindingChain resolved before state_env"
    );
}
