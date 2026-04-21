// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::error::EvalError;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_live_expr_enabled_true_when_action_satisfiable() {
    let ctx = EvalCtx::new();
    let current_state = State::from_pairs([("x", Value::int(5))]);

    // Create action: x' = x + 1
    let x = Spanned::dummy(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = Spanned::dummy(Expr::Prime(Box::new(x.clone())));
    let x_plus_1 = Spanned::dummy(Expr::Add(
        Box::new(x),
        Box::new(Spanned::dummy(Expr::Int(1.into()))),
    ));
    let action_expr = Arc::new(Spanned::dummy(Expr::Eq(
        Box::new(x_prime),
        Box::new(x_plus_1),
    )));

    let enabled = LiveExpr::enabled(action_expr, 1);

    // Bind current state variable in ctx.
    let mut ctx_current = ctx.clone();
    ctx_current.bind_mut("x".to_string(), Value::int(5));

    // Provide a successor where the action holds (x' = 6).
    let mut get_successors = |_s: &State| Ok(vec![State::from_pairs([("x", Value::int(6))])]);

    let result = eval_live_expr(
        &ctx_current,
        &enabled,
        &current_state,
        None,
        &mut get_successors,
        None,
    )
    .unwrap();
    assert!(result);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_live_expr_enabled_false_when_no_successor_satisfies_action() {
    let ctx = EvalCtx::new();
    let current_state = State::from_pairs([("x", Value::int(5))]);

    // Create action: x' = x + 1
    let x = Spanned::dummy(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = Spanned::dummy(Expr::Prime(Box::new(x.clone())));
    let x_plus_1 = Spanned::dummy(Expr::Add(
        Box::new(x),
        Box::new(Spanned::dummy(Expr::Int(1.into()))),
    ));
    let action_expr = Arc::new(Spanned::dummy(Expr::Eq(
        Box::new(x_prime),
        Box::new(x_plus_1),
    )));

    let enabled = LiveExpr::enabled(action_expr, 1);

    // Bind current state variable in ctx.
    let mut ctx_current = ctx.clone();
    ctx_current.bind_mut("x".to_string(), Value::int(5));

    // Provide a successor where the action does NOT hold (x' = 7).
    let mut get_successors = |_s: &State| Ok(vec![State::from_pairs([("x", Value::int(7))])]);

    let result = eval_live_expr(
        &ctx_current,
        &enabled,
        &current_state,
        None,
        &mut get_successors,
        None,
    )
    .unwrap();
    assert!(!result);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_live_expr_enabled_cache_skips_empty_registry_fallback_mode() {
    // In empty-registry fallback mode, ENABLED depends on the caller-provided
    // successor callback. The shared cache must not reuse (fingerprint, tag)
    // entries across different callbacks.
    crate::liveness::clear_enabled_cache();

    let ctx = EvalCtx::new();
    let current_state = State::from_pairs([("x", Value::int(0))]);

    let x = Spanned::dummy(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = Spanned::dummy(Expr::Prime(Box::new(x.clone())));
    let x_plus_1 = Spanned::dummy(Expr::Add(
        Box::new(x),
        Box::new(Spanned::dummy(Expr::Int(1.into()))),
    ));
    let action_expr = Arc::new(Spanned::dummy(Expr::Eq(
        Box::new(x_prime),
        Box::new(x_plus_1),
    )));
    let enabled = LiveExpr::enabled(action_expr, 77);

    let mut ctx_current = ctx.clone();
    ctx_current.bind_mut("x".to_string(), Value::int(0));

    let mut get_successors_true = |_s: &State| Ok(vec![State::from_pairs([("x", Value::int(1))])]);
    let first = eval_live_expr(
        &ctx_current,
        &enabled,
        &current_state,
        None,
        &mut get_successors_true,
        None,
    )
    .unwrap();
    assert!(first);

    // Same (state, tag), but different successor callback: result must be recomputed.
    let mut get_successors_false = |_s: &State| Ok(vec![State::from_pairs([("x", Value::int(2))])]);
    let second = eval_live_expr(
        &ctx_current,
        &enabled,
        &current_state,
        None,
        &mut get_successors_false,
        None,
    )
    .unwrap();
    assert!(
        !second,
        "fallback-mode ENABLED result must not leak from prior callback"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_live_expr_enabled_subscripted_division_by_zero_disables_action() {
    // Match checker/eval.rs semantics: runtime disabled-action errors in ENABLED
    // become false instead of propagating.
    let mut ctx = EvalCtx::new();
    ctx.register_var(Arc::from("x"));
    let current_state = State::from_pairs([("x", Value::int(5))]);
    let mut get_successors = empty_successors;

    // Action: x' = 10 \div 0
    let x = Spanned::dummy(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = Spanned::dummy(Expr::Prime(Box::new(x)));
    let div_zero = Spanned::dummy(Expr::Div(
        Box::new(Spanned::dummy(Expr::Int(10.into()))),
        Box::new(Spanned::dummy(Expr::Int(0.into()))),
    ));
    let action = Arc::new(Spanned::dummy(Expr::Eq(
        Box::new(x_prime),
        Box::new(div_zero),
    )));
    let enabled = LiveExpr::enabled_subscripted(action, None, 1);

    let result = eval_live_expr(
        &ctx,
        &enabled,
        &current_state,
        None,
        &mut get_successors,
        None,
    )
    .expect("DivisionByZero in ENABLED should be treated as disabled");
    assert!(!result);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_live_expr_enabled_subscripted_argument_error_propagates() {
    // Only the disabled-action error subset is suppressed; ArgumentError must propagate.
    let mut ctx = EvalCtx::new();
    ctx.register_var(Arc::from("x"));
    let current_state = State::from_pairs([("x", Value::int(5))]);
    let mut get_successors = empty_successors;

    // Action: x' = (TRUE + 1) => ArgumentError (boolean given to arithmetic op).
    let x = Spanned::dummy(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = Spanned::dummy(Expr::Prime(Box::new(x)));
    let rhs = Spanned::dummy(Expr::Add(
        Box::new(Spanned::dummy(Expr::Bool(true))),
        Box::new(Spanned::dummy(Expr::Int(1.into()))),
    ));
    let action = Arc::new(Spanned::dummy(Expr::Eq(Box::new(x_prime), Box::new(rhs))));
    let enabled = LiveExpr::enabled_subscripted(action, None, 1);

    let err = eval_live_expr(
        &ctx,
        &enabled,
        &current_state,
        None,
        &mut get_successors,
        None,
    )
    .expect_err("ArgumentError in ENABLED must propagate");
    assert!(
        matches!(err, EvalError::ArgumentError { .. }),
        "expected ArgumentError, got {err:?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_live_expr_enabled_subscripted_ignores_non_subscript_changes() {
    let ctx = EvalCtx::new();
    let current_state = State::from_pairs([("x", Value::int(0)), ("y", Value::int(0))]);

    // ENABLED<<TRUE>>_x should be false if the only successor changes y but not x.
    let action_expr = Arc::new(Spanned::dummy(Expr::Bool(true)));
    let subscript = Some(Arc::new(Spanned::dummy(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ))));
    let enabled = LiveExpr::enabled_with_bindings(action_expr, true, subscript, 1, None);

    let mut get_successors = |_s: &State| {
        Ok(vec![State::from_pairs([
            ("x", Value::int(0)),
            ("y", Value::int(1)),
        ])])
    };

    let result = eval_live_expr(
        &ctx,
        &enabled,
        &current_state,
        None,
        &mut get_successors,
        None,
    )
    .unwrap();
    assert!(!result);
}

/// Regression test for #2151: eval_enabled_fallback must suppress disabled-action
/// errors (DivisionByZero, etc.) identically to fast_path_satisfies_action.
/// The fallback path is taken when var_registry is empty (no registered vars).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_fallback_division_by_zero_returns_false() {
    crate::liveness::clear_enabled_cache();

    // No registered vars → empty VarRegistry → fallback path in eval_enabled_uncached
    let ctx = EvalCtx::new();
    let current_state = State::from_pairs([("x", Value::int(5))]);

    // Action: x' = 10 \div 0 → produces DivisionByZero in transition_satisfies_action
    let x = Spanned::dummy(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = Spanned::dummy(Expr::Prime(Box::new(x)));
    let div_zero = Spanned::dummy(Expr::Div(
        Box::new(Spanned::dummy(Expr::Int(10.into()))),
        Box::new(Spanned::dummy(Expr::Int(0.into()))),
    ));
    let action = Arc::new(Spanned::dummy(Expr::Eq(
        Box::new(x_prime),
        Box::new(div_zero),
    )));
    let enabled = LiveExpr::enabled(action, 2151);

    // Provide a successor so fallback has states to iterate over.
    let mut get_successors = |_s: &State| Ok(vec![State::from_pairs([("x", Value::int(6))])]);

    let result = eval_live_expr(
        &ctx,
        &enabled,
        &current_state,
        None,
        &mut get_successors,
        None,
    )
    .expect("DivisionByZero in fallback ENABLED must be treated as disabled, not propagated");
    assert!(
        !result,
        "fallback path must return false for disabled-action errors (Part of #2151)"
    );
}

/// Companion to the above: non-disabled errors (ArgumentError) must still propagate
/// through the fallback path, not be silently swallowed.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_enabled_fallback_argument_error_propagates() {
    crate::liveness::clear_enabled_cache();

    // No registered vars → fallback path
    let ctx = EvalCtx::new();
    let current_state = State::from_pairs([("x", Value::int(5))]);

    // Action: x' = (TRUE + 1) → ArgumentError (boolean in arithmetic)
    let x = Spanned::dummy(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = Spanned::dummy(Expr::Prime(Box::new(x)));
    let rhs = Spanned::dummy(Expr::Add(
        Box::new(Spanned::dummy(Expr::Bool(true))),
        Box::new(Spanned::dummy(Expr::Int(1.into()))),
    ));
    let action = Arc::new(Spanned::dummy(Expr::Eq(Box::new(x_prime), Box::new(rhs))));
    let enabled = LiveExpr::enabled(action, 2151);

    let mut get_successors = |_s: &State| Ok(vec![State::from_pairs([("x", Value::int(6))])]);

    let err = eval_live_expr(
        &ctx,
        &enabled,
        &current_state,
        None,
        &mut get_successors,
        None,
    )
    .expect_err("ArgumentError in fallback ENABLED must propagate");
    assert!(
        matches!(err, EvalError::ArgumentError { .. }),
        "expected ArgumentError, got {err:?}"
    );
}
