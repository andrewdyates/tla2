// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::liveness::tableau::{Particle, TableauNode};
use tla_core::ast::Substitution;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_live_expr_state_changed_subscript_uses_subscript_values() {
    let ctx = EvalCtx::new();
    let current_state = State::from_pairs([("x", Value::int(1)), ("y", Value::int(0))]);
    let next_state = State::from_pairs([("x", Value::int(1)), ("y", Value::int(1))]);
    let mut get_successors = empty_successors;

    // CHANGED(x) should be false when only y changes.
    let changed = LiveExpr::state_changed_with_bindings(
        Some(Arc::new(Spanned::dummy(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        1,
        None,
    );

    let result = eval_live_expr(
        &ctx,
        &changed,
        &current_state,
        Some(&next_state),
        &mut get_successors,
        None,
    )
    .unwrap();
    assert!(!result);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_changed_subscript_preserves_constant_env_bindings() {
    // Regression for #2330:
    // Subscript evaluation must preserve base env constants (e.g., `Node`) while
    // swapping concrete state vars; otherwise Node-based subscripts fail with
    // UndefinedVar in liveness EAAction checks.
    let mut ctx = EvalCtx::new();
    ctx.bind_mut(
        Arc::from("Node"),
        Value::set([Value::int(1), Value::int(2), Value::int(3)]),
    );

    let current_state = State::from_pairs([("x", Value::int(0))]);
    let next_state = State::from_pairs([("x", Value::int(1))]);
    let mut get_successors = empty_successors;

    let changed = LiveExpr::state_changed_with_bindings(
        Some(Arc::new(Spanned::dummy(Expr::Ident(
            "Node".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        2330,
        None,
    );

    let result = eval_live_expr(
        &ctx,
        &changed,
        &current_state,
        Some(&next_state),
        &mut get_successors,
        None,
    )
    .expect("constant subscript should evaluate with preserved env bindings");

    assert!(
        !result,
        "constant subscript Node should be unchanged across states"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_state_changed_subscript_clears_instance_subst_cache_between_states() {
    // Regression for #2111:
    // If eval_subscript_changed uses raw eval(), SUBST_CACHE can leak across the two
    // state evaluations and make this report no change.
    let ctx = EvalCtx::new().with_instance_substitutions(vec![Substitution {
        from: Spanned::dummy("inst_x".to_string()),
        to: Spanned::dummy(Expr::Ident(
            "x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )),
    }]);
    let current_state = State::from_pairs([("x", Value::int(0))]);
    let next_state = State::from_pairs([("x", Value::int(1))]);
    let mut get_successors = empty_successors;

    let changed = LiveExpr::state_changed_with_bindings(
        Some(Arc::new(Spanned::dummy(Expr::Ident(
            "inst_x".to_string(),
            tla_core::name_intern::NameId::INVALID,
        )))),
        2111,
        None,
    );

    let result = eval_live_expr(
        &ctx,
        &changed,
        &current_state,
        Some(&next_state),
        &mut get_successors,
        None,
    )
    .unwrap();
    assert!(
        result,
        "subscript INSTANCE substitution must re-evaluate per state"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_transition_consistent_with_action_pred() {
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

    // Create a particle with this action predicate
    let particle = Particle::from_vec(vec![action_pred]);
    let node = TableauNode::new(particle, 0);

    // Transition from x=5 to x=6 should satisfy x' = x + 1
    let result = is_transition_consistent(
        &ctx,
        &current_state,
        &next_state,
        &node,
        &mut get_successors,
    )
    .unwrap();
    assert!(result);

    // Transition from x=5 to x=7 should NOT satisfy x' = x + 1
    let wrong_next_state = State::from_pairs([("x", Value::int(7))]);
    let result = is_transition_consistent(
        &ctx,
        &current_state,
        &wrong_next_state,
        &node,
        &mut get_successors,
    )
    .unwrap();
    assert!(!result);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_transition_consistent_skips_temporal_formulas() {
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

    // Create a temporal formula that would error if evaluated
    let temporal = LiveExpr::Always(Box::new(LiveExpr::Bool(true)));

    // Particle with BOTH action pred and temporal formula
    let particle = Particle::from_vec(vec![action_pred, temporal]);
    let node = TableauNode::new(particle, 0);

    // Should succeed: temporal formula is skipped, action pred passes
    let result = is_transition_consistent(
        &ctx,
        &current_state,
        &next_state,
        &node,
        &mut get_successors,
    )
    .unwrap();
    assert!(result, "temporal formulas in particle must be skipped");
}
