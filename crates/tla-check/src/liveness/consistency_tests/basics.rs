// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::error::EvalError;
use crate::eval::{BindingChain, BindingValue, Env};

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_live_expr_bool() {
    let ctx = EvalCtx::new();
    let state = State::new();
    let mut get_successors = empty_successors;

    assert!(eval_live_expr(
        &ctx,
        &LiveExpr::Bool(true),
        &state,
        None,
        &mut get_successors,
        None
    )
    .unwrap());
    assert!(!eval_live_expr(
        &ctx,
        &LiveExpr::Bool(false),
        &state,
        None,
        &mut get_successors,
        None
    )
    .unwrap());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_live_expr_not() {
    let ctx = EvalCtx::new();
    let state = State::new();
    let mut get_successors = empty_successors;

    let not_true = LiveExpr::not(LiveExpr::Bool(true));
    let not_false = LiveExpr::not(LiveExpr::Bool(false));

    assert!(!eval_live_expr(&ctx, &not_true, &state, None, &mut get_successors, None).unwrap());
    assert!(eval_live_expr(&ctx, &not_false, &state, None, &mut get_successors, None).unwrap());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_live_expr_and() {
    let ctx = EvalCtx::new();
    let state = State::new();
    let mut get_successors = empty_successors;

    let tt = LiveExpr::and(vec![LiveExpr::Bool(true), LiveExpr::Bool(true)]);
    let tf = LiveExpr::and(vec![LiveExpr::Bool(true), LiveExpr::Bool(false)]);
    let ff = LiveExpr::and(vec![LiveExpr::Bool(false), LiveExpr::Bool(false)]);

    assert!(eval_live_expr(&ctx, &tt, &state, None, &mut get_successors, None).unwrap());
    assert!(!eval_live_expr(&ctx, &tf, &state, None, &mut get_successors, None).unwrap());
    assert!(!eval_live_expr(&ctx, &ff, &state, None, &mut get_successors, None).unwrap());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_live_expr_or() {
    let ctx = EvalCtx::new();
    let state = State::new();
    let mut get_successors = empty_successors;

    let tt = LiveExpr::or(vec![LiveExpr::Bool(true), LiveExpr::Bool(true)]);
    let tf = LiveExpr::or(vec![LiveExpr::Bool(true), LiveExpr::Bool(false)]);
    let ff = LiveExpr::or(vec![LiveExpr::Bool(false), LiveExpr::Bool(false)]);

    assert!(eval_live_expr(&ctx, &tt, &state, None, &mut get_successors, None).unwrap());
    assert!(eval_live_expr(&ctx, &tf, &state, None, &mut get_successors, None).unwrap());
    assert!(!eval_live_expr(&ctx, &ff, &state, None, &mut get_successors, None).unwrap());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_live_expr_state_pred_with_binding() {
    // Create a state predicate that checks x > 0
    let x_gt_0 = Expr::Gt(
        Box::new(Spanned::dummy(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        ))),
        Box::new(Spanned::dummy(Expr::Int(0.into()))),
    );
    let pred = LiveExpr::StatePred {
        expr: Arc::new(Spanned::dummy(x_gt_0)),
        bindings: None,
        tag: 1,
    };

    let ctx = EvalCtx::new();
    let mut get_successors = empty_successors;

    // State where x = 5 (should be true)
    let state_pos = State::from_pairs([("x", Value::int(5))]);
    let mut ctx_pos = ctx.clone();
    ctx_pos.bind_mut("x".to_string(), Value::int(5));
    assert!(eval_live_expr(&ctx_pos, &pred, &state_pos, None, &mut get_successors, None).unwrap());

    // State where x = -1 (should be false)
    let state_neg = State::from_pairs([("x", Value::int(-1))]);
    let mut ctx_neg = ctx.clone();
    ctx_neg.bind_mut("x".to_string(), Value::int(-1));
    assert!(!eval_live_expr(&ctx_neg, &pred, &state_neg, None, &mut get_successors, None).unwrap());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_live_expr_state_pred_applies_fast_bindings() {
    // Part of #2895: Uses BindingChain instead of FastBinding.
    let name_id = tla_core::name_intern::intern_name("x");
    let pred = LiveExpr::state_pred_with_bindings(
        Arc::new(Spanned::dummy(Expr::Eq(
            Box::new(Spanned::dummy(Expr::Ident(
                "x".to_string(),
                tla_core::name_intern::NameId::INVALID,
            ))),
            Box::new(Spanned::dummy(Expr::Int(1.into()))),
        ))),
        1,
        Some(BindingChain::empty().cons(name_id, BindingValue::eager(Value::int(1)))),
    );

    let ctx = EvalCtx::new();
    let state = State::new();
    let mut get_successors = empty_successors;

    assert!(eval_live_expr(&ctx, &pred, &state, None, &mut get_successors, None).unwrap());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_temporal_operators_return_error() {
    let ctx = EvalCtx::new();
    let state = State::new();
    let mut get_successors = empty_successors;

    // Temporal operators must error — they should never reach state-level
    // evaluation. Returning Ok(true) would silently accept any state as
    // consistent if a temporal operator leaked through the tableau.
    let always = LiveExpr::always(LiveExpr::Bool(false));
    let eventually = LiveExpr::eventually(LiveExpr::Bool(false));
    let next = LiveExpr::next(LiveExpr::Bool(false));

    let err = eval_live_expr(&ctx, &always, &state, None, &mut get_successors, None)
        .expect_err("Always must error in state-level eval");
    assert!(
        err.to_string().contains("unexpected temporal operator"),
        "Expected 'unexpected temporal operator', got: {err}"
    );

    let err = eval_live_expr(&ctx, &eventually, &state, None, &mut get_successors, None)
        .expect_err("Eventually must error in state-level eval");
    assert!(
        err.to_string().contains("unexpected temporal operator"),
        "Expected 'unexpected temporal operator', got: {err}"
    );

    let err = eval_live_expr(&ctx, &next, &state, None, &mut get_successors, None)
        .expect_err("Next must error in state-level eval");
    assert!(
        err.to_string().contains("unexpected temporal operator"),
        "Expected 'unexpected temporal operator', got: {err}"
    );
}

/// After #2286, evaluating an ActionPred with primed variables but no
/// next_state is treated as a classification bug. In debug/test builds
/// this fires a debug_assert panic; in release builds it returns
/// `Err(EvalError::Internal)`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_action_pred_with_primed_vars_no_next_state() {
    let ctx = EvalCtx::new();
    let state = State::from_pairs([("x", Value::int(5))]);
    let mut get_successors = empty_successors;

    // Create action predicate: x' = x + 1 (contains primed variable)
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

    let action_pred = LiveExpr::action_pred(action_expr, 1);

    let mut ctx_with_x = ctx.clone();
    ctx_with_x.bind_mut("x".to_string(), Value::int(5));
    // Debug builds panic via debug_assert; release builds return Internal.
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        eval_live_expr(
            &ctx_with_x,
            &action_pred,
            &state,
            None,
            &mut get_successors,
            None,
        )
    }));

    if cfg!(debug_assertions) {
        assert!(
            outcome.is_err(),
            "debug builds must panic for ActionPred without next_state"
        );
    } else {
        let eval_result = outcome.expect("release builds should return Err(EvalError::Internal)");
        let err =
            eval_result.expect_err("ActionPred without next_state must error in release builds");
        assert!(
            matches!(err, EvalError::Internal { .. }),
            "expected EvalError::Internal, got: {err:?}"
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_action_pred_with_primed_vars_with_next_state() {
    // Test that action predicates with primed variables work when next state is provided
    let ctx = EvalCtx::new();
    let current_state = State::from_pairs([("x", Value::int(5))]);
    let next_state = State::from_pairs([("x", Value::int(6))]);
    let mut get_successors = empty_successors;

    // Create action predicate: x' = x + 1
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

    let action_pred = LiveExpr::action_pred(action_expr, 1);

    // Set up context with current state variables
    let mut ctx_current = ctx.clone();
    ctx_current.bind_mut("x", Value::int(5));

    // Set up next state bindings
    let mut next_env = Env::new();
    next_env.insert(Arc::from("x"), Value::int(6));
    let ctx_with_next = ctx_current.with_next_state(next_env);

    // With next state context, should evaluate correctly: 6 = 5 + 1 = true
    let result = eval_live_expr(
        &ctx_with_next,
        &action_pred,
        &current_state,
        Some(&next_state),
        &mut get_successors,
        None,
    )
    .unwrap();
    assert!(result);

    // Test with non-matching next state (x' = 7, but we expect x + 1 = 6)
    let wrong_next_state = State::from_pairs([("x", Value::int(7))]);
    let mut wrong_next_env = Env::new();
    wrong_next_env.insert(Arc::from("x"), Value::int(7));
    let ctx_wrong_next = ctx_current.clone().with_next_state(wrong_next_env);

    let result = eval_live_expr(
        &ctx_wrong_next,
        &action_pred,
        &current_state,
        Some(&wrong_next_state),
        &mut get_successors,
        None,
    )
    .unwrap();
    assert!(!result); // 7 != 5 + 1
}
