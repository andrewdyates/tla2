// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! UNCHANGED behavior tests for eval_unchanged.

use super::*;
use crate::StateEnvRef;
use num_bigint::BigInt;
use tla_value::CompactValue;

// ==========================================================================
// Hoist-cache regression for eval_unchanged (#3147)
// ==========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_unchanged_recomputes_next_state_value_inside_hoist_scope() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(2)];
    let _next_guard = ctx.bind_next_state_array_guard(&next);

    let x_id = intern_name("x");
    let inner = Spanned::dummy(Expr::Tuple(vec![Spanned::dummy(Expr::Ident(
        "x".to_string(),
        x_id,
    ))]));

    let mut hoistable = FxHashSet::default();
    hoistable.insert(std::ptr::addr_of!(inner.node) as usize);
    let _hoist_guard =
        enter_quantifier_hoist_scope(Rc::new(hoistable)).expect("manual hoist scope should push");

    let result = crate::eval_unchanged::eval_unchanged(&ctx, &inner, None)
        .expect("UNCHANGED tuple should evaluate");
    assert_eq!(
        result,
        Value::Bool(false),
        "UNCHANGED must compare fresh next-state values even when hoist caching is active"
    );

    clear_for_test_reset();
}

// ==========================================================================
// eval_unchanged
// ==========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_array_path_equal() {
    // UNCHANGED x with array-backed state: x' == x → TRUE
    let src = r#"
---- MODULE Test ----
VARIABLE x
Op == UNCHANGED x
===="#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty());
    let module = lower_result.module.expect("no module");

    clear_for_test_reset();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");
    ctx.bind_mut("x", Value::int(42));
    let state = vec![Value::int(42)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(42)]; // same as current
    let _guard = ctx.bind_next_state_array_guard(&next);

    let op_def = ctx.get_op("Op").expect("Op not found").clone();
    let v = eval(&ctx, &op_def.body).unwrap();
    assert_eq!(v, Value::Bool(true), "UNCHANGED x should be TRUE when x'=x");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_array_path_not_equal() {
    // UNCHANGED x with array-backed state: x' ≠ x → FALSE
    // Uses register_var + eval_str_with_ctx to avoid env shadowing state_env.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(2)]; // different
    let _guard = ctx.bind_next_state_array_guard(&next);

    let v = eval_str_with_ctx("UNCHANGED x", &ctx).expect("UNCHANGED x");
    assert_eq!(
        v,
        Value::Bool(false),
        "UNCHANGED x should be FALSE when x'≠x"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_hashmap_path_equal() {
    // UNCHANGED x with HashMap-based next_state.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.bind_mut("x", Value::int(5));

    let mut next = Env::new();
    next.insert(Arc::from("x"), Value::int(5));
    ctx.stable_mut().next_state = Some(Arc::new(next));

    let result = eval_str_with_ctx("UNCHANGED x", &ctx).expect("UNCHANGED x");
    assert_eq!(
        result,
        Value::Bool(true),
        "UNCHANGED with same HashMap values → TRUE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_hashmap_path_not_equal() {
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.bind_mut("x", Value::int(5));

    let mut next = Env::new();
    next.insert(Arc::from("x"), Value::int(99));
    ctx.stable_mut().next_state = Some(Arc::new(next));

    let result = eval_str_with_ctx("UNCHANGED x", &ctx).expect("UNCHANGED x");
    assert_eq!(
        result,
        Value::Bool(false),
        "UNCHANGED with different HashMap values → FALSE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_tuple_multiple_vars() {
    // UNCHANGED <<x, y>> — tests the tuple/complex expression path.
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Op == UNCHANGED <<x, y>>
===="#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty());
    let module = lower_result.module.expect("no module");

    clear_for_test_reset();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");
    ctx.register_var("y");
    ctx.bind_mut("x", Value::int(1));
    ctx.bind_mut("y", Value::int(2));
    let state = vec![Value::int(1), Value::int(2)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(1), Value::int(2)]; // same
    let _guard = ctx.bind_next_state_array_guard(&next);

    let op_def = ctx.get_op("Op").expect("Op not found").clone();
    let v = eval(&ctx, &op_def.body).unwrap();
    assert_eq!(
        v,
        Value::Bool(true),
        "UNCHANGED <<x,y>> with same values → TRUE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_tuple_partial_change() {
    // UNCHANGED <<x, y>> where only y changes → FALSE.
    // Uses register_var + eval_str_with_ctx to avoid env shadowing state_env.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    let state = vec![Value::int(1), Value::int(2)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(1), Value::int(99)]; // y changed
    let _guard = ctx.bind_next_state_array_guard(&next);

    let v = eval_str_with_ctx("UNCHANGED <<x, y>>", &ctx).expect("UNCHANGED <<x,y>>");
    assert_eq!(
        v,
        Value::Bool(false),
        "UNCHANGED <<x,y>> with y changed → FALSE"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_compact_array_path_matches_equivalent_heap_integer() {
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.register_var("x");

    let state = [CompactValue::from(Value::int(42))];
    let next = [CompactValue::from(Value::Int(Arc::new(BigInt::from(42))))];
    let _state_guard = ctx.bind_state_env_guard(StateEnvRef::from_compact_slice(&state));
    let _next_guard = ctx.bind_next_state_env_guard(StateEnvRef::from_compact_slice(&next));

    let value = eval_str_with_ctx("UNCHANGED x", &ctx).expect("compact UNCHANGED should evaluate");
    assert_eq!(
        value,
        Value::Bool(true),
        "compact current/next slots must preserve Value equality semantics"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_without_next_state_returns_error() {
    // UNCHANGED x without any next-state context should fail.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.bind_mut("x", Value::int(1));

    let result = eval_str_with_ctx("UNCHANGED x", &ctx);
    assert!(
        result.is_err(),
        "UNCHANGED without next_state should return error"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_hashmap_with_state_env_full() {
    // UNCHANGED with HashMap next_state and state_env set (full coverage path).
    let src = r#"
---- MODULE Test ----
VARIABLE x
Op == UNCHANGED x
===="#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(lower_result.errors.is_empty());
    let module = lower_result.module.expect("no module");

    clear_for_test_reset();
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_var("x");
    ctx.bind_mut("x", Value::int(42));
    let state = vec![Value::int(42)];
    ctx.bind_state_array(&state);

    // Full HashMap next_state
    let mut next = Env::new();
    next.insert(Arc::from("x"), Value::int(42));
    ctx.stable_mut().next_state = Some(Arc::new(next));
    let _ = ctx.take_next_state_env();

    let op_def = ctx.get_op("Op").expect("Op not found").clone();
    let v = eval(&ctx, &op_def.body).unwrap();
    assert_eq!(
        v,
        Value::Bool(true),
        "UNCHANGED with full HashMap and state_env → TRUE"
    );
}
