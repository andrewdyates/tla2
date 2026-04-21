// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use tla_core::ast::Expr;
use tla_core::name_intern::intern_name;
use tla_core::Spanned;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_var_uses_current_registry_slot_when_embedded_idx_is_stale() {
    let mut ctx = EvalCtx::new();
    ctx.register_var("coordinator");
    ctx.register_var("participant");
    let state = vec![Value::int(1), Value::int(99)];
    ctx.bind_state_array(&state);

    let participant_id = intern_name("participant");
    let stale_state_var =
        Spanned::dummy(Expr::StateVar("participant".to_string(), 0, participant_id));

    let value = eval(&ctx, &stale_state_var).expect("stale StateVar should evaluate");
    assert_eq!(
        value,
        Value::int(99),
        "StateVar should follow the current registry slot for participant, not the stale embedded idx"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier1_state_var_fast_path_repairs_stale_idx_in_prime() {
    let mut ctx = EvalCtx::new();
    ctx.register_var("coordinator");
    ctx.register_var("participant");
    let state = vec![Value::int(1), Value::int(2)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(10), Value::int(20)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    let participant_id = intern_name("participant");
    let stale_state_var =
        Spanned::dummy(Expr::StateVar("participant".to_string(), 0, participant_id));
    let prime_expr = Spanned::dummy(Expr::Prime(Box::new(stale_state_var)));

    let value = eval(&ctx, &prime_expr).expect("stale primed StateVar should evaluate");
    assert_eq!(
        value,
        Value::int(20),
        "primed StateVar should use the current registry slot for participant"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_array_path_repairs_stale_state_var_idx() {
    let mut ctx = EvalCtx::new();
    ctx.register_var("coordinator");
    ctx.register_var("participant");
    let state = vec![Value::int(1), Value::int(99)];
    ctx.bind_state_array(&state);
    let next = vec![Value::int(2), Value::int(99)];
    let _guard = ctx.bind_next_state_array_guard(&next);

    let participant_id = intern_name("participant");
    let expr = Spanned::dummy(Expr::Unchanged(Box::new(Spanned::dummy(Expr::Tuple(
        vec![Spanned::dummy(Expr::StateVar(
            "participant".to_string(),
            0,
            participant_id,
        ))],
    )))));

    let value = eval(&ctx, &expr).expect("UNCHANGED with stale StateVar should evaluate");
    assert_eq!(
        value,
        Value::Bool(true),
        "UNCHANGED should compare participant across states even if the embedded idx is stale"
    );
}
