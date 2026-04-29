// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tier 1: Array and StateVar fast path tests for eval_prime.

use super::*;

// ==========================================================================
// Tier 1: Array fast path (O(1) via VarIndex) — unsafe get_unchecked
// ==========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier1_array_fast_path_ident_single_var() {
    // Tier 1: Expr::Ident("x", NameId::INVALID) with next_state_env set -> unsafe O(1) lookup.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(42)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    let result = eval_str_with_ctx("x'", &ctx).expect("x' should evaluate");
    assert_eq!(
        result,
        Value::int(42),
        "Tier 1 should return next-state value"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier1_array_fast_path_multiple_vars() {
    // Tier 1 with multiple state variables at different indices.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    ctx.register_var("z");
    let state = vec![Value::int(1), Value::int(2), Value::int(3)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(10), Value::int(20), Value::int(30)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    let rx = eval_str_with_ctx("x'", &ctx).expect("x'");
    let ry = eval_str_with_ctx("y'", &ctx).expect("y'");
    let rz = eval_str_with_ctx("z'", &ctx).expect("z'");
    assert_eq!(rx, Value::int(10));
    assert_eq!(ry, Value::int(20));
    assert_eq!(rz, Value::int(30));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier1_array_fast_path_boundary_first_index() {
    // Boundary: first variable at VarIndex(0).
    let mut ctx = EvalCtx::new();
    ctx.register_var("a");
    let state = vec![Value::int(0)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(999)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    let result = eval_str_with_ctx("a'", &ctx).expect("a'");
    assert_eq!(result, Value::int(999));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier1_array_fast_path_boundary_last_index() {
    // Boundary: last variable at maximum registered index.
    let mut ctx = EvalCtx::new();
    ctx.register_var("a");
    ctx.register_var("b");
    ctx.register_var("c");
    ctx.register_var("d");
    let state = vec![Value::int(0), Value::int(0), Value::int(0), Value::int(0)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(1), Value::int(2), Value::int(3), Value::int(777)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    let result = eval_str_with_ctx("d'", &ctx).expect("d'");
    assert_eq!(result, Value::int(777), "last index should work correctly");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier1_array_fast_path_non_int_values() {
    // Tier 1 with non-integer values (strings, booleans).
    let mut ctx = EvalCtx::new();
    ctx.register_var("flag");
    ctx.register_var("name");
    let state = vec![Value::Bool(false), Value::string("old")];
    ctx.bind_state_array(&state);
    let next = vec![Value::Bool(true), Value::string("new")];
    let _guard = ctx.bind_next_state_array_guard(&next);

    let r_flag = eval_str_with_ctx("flag'", &ctx).expect("flag'");
    let r_name = eval_str_with_ctx("name'", &ctx).expect("name'");
    assert_eq!(r_flag, Value::Bool(true));
    assert_eq!(r_name, Value::string("new"));
}

// ==========================================================================
// Tier 1: StateVar path — unsafe get_unchecked at line 87
// ==========================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier1_state_var_fast_path() {
    // When the inner expression is Expr::StateVar (with embedded VarIndex),
    // eval_prime uses the second unsafe fast path at line 87 (get_unchecked).
    // lower() produces Ident nodes, not StateVar — only the model checker's
    // compilation phase creates StateVar — so we construct the AST manually.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    let state = vec![Value::int(1)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(55)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    let name_id = intern_name("x");
    let state_var = Spanned::dummy(Expr::StateVar("x".to_string(), 0, name_id));
    let prime_expr = Spanned::dummy(Expr::Prime(Box::new(state_var)));
    let v = eval(&ctx, &prime_expr).unwrap();
    assert_eq!(
        v,
        Value::int(55),
        "StateVar fast path should use next_state_env"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier1_state_var_multiple_vars() {
    // Multiple StateVar nodes at different VarIndex positions exercise the
    // unsafe get_unchecked path at line 87 for each index.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    let state = vec![Value::int(1), Value::int(2)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(10), Value::int(20)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    let x_id = intern_name("x");
    let y_id = intern_name("y");
    let prime_x = Spanned::dummy(Expr::Prime(Box::new(Spanned::dummy(Expr::StateVar(
        "x".to_string(),
        0,
        x_id,
    )))));
    let prime_y = Spanned::dummy(Expr::Prime(Box::new(Spanned::dummy(Expr::StateVar(
        "y".to_string(),
        1,
        y_id,
    )))));

    let vx = eval(&ctx, &prime_x).unwrap();
    let vy = eval(&ctx, &prime_y).unwrap();
    assert_eq!(vx, Value::int(10));
    assert_eq!(vy, Value::int(20));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier1_state_var_boundary_last_index() {
    // Boundary: last StateVar index in a larger array (4 elements).
    // Exercises unsafe get_unchecked at line 87 with idx = N-1 = 3.
    let mut ctx = EvalCtx::new();
    ctx.register_var("a");
    ctx.register_var("b");
    ctx.register_var("c");
    ctx.register_var("d");
    let state = vec![Value::int(0), Value::int(0), Value::int(0), Value::int(0)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(1), Value::int(2), Value::int(3), Value::int(888)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    let d_id = intern_name("d");
    let prime_d = Spanned::dummy(Expr::Prime(Box::new(Spanned::dummy(Expr::StateVar(
        "d".to_string(),
        3,
        d_id,
    )))));

    let v = eval(&ctx, &prime_d).unwrap();
    assert_eq!(
        v,
        Value::int(888),
        "StateVar at last index (3) should return correct next-state value"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier1_state_var_call_by_name_blocks_fast_path() {
    // When a StateVar has a matching call-by-name substitution, the unsafe
    // get_unchecked fast path at line 87 must be bypassed. This tests the
    // has_cbn_sub guard at lines 80-82 which was previously uncovered.
    let mut ctx = EvalCtx::new();
    ctx.register_var("x");
    ctx.register_var("y");
    let state = vec![Value::int(1), Value::int(2)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(10), Value::int(20)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    // x -> y call-by-name substitution
    let ctx_with_cbn = ctx.with_call_by_name_subs(vec![Substitution {
        from: Spanned::dummy("x".to_string()),
        to: Spanned::dummy(Expr::Ident(
            "y".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
    }]);

    // Construct Prime(StateVar("x", 0, ...)) — the StateVar path
    let x_id = intern_name("x");
    let prime_sv = Spanned::dummy(Expr::Prime(Box::new(Spanned::dummy(Expr::StateVar(
        "x".to_string(),
        0,
        x_id,
    )))));

    let v = eval(&ctx_with_cbn, &prime_sv).unwrap();
    // x' should resolve via CBN: x -> y, so x' -> y' -> next[1] = 20
    // NOT via fast path: next[0] = 10
    assert_eq!(
        v,
        Value::int(20),
        "StateVar with CBN sub x->y must bypass fast path: x' should be y'=20, not x'=10"
    );
}
