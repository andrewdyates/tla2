// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::action::action_leaf_preserves_batch_boundary;
use super::state::state_leaf_preserves_batch_boundary;
use super::*;
use crate::eval::EvalCtx;
use crate::liveness::LiveExpr;
use crate::state::{ArrayState, State};
use crate::test_support::parse_module;
use crate::Value;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;

const INLINE_LEAF_EVAL_SPEC: &str = r#"
---- MODULE InlineLeafEval ----
EXTENDS Integers
VARIABLE x
IsZero == x = 0
SetOne == x' = 1
XValue == x
====
"#;

fn dummy_expr() -> Arc<Spanned<Expr>> {
    Arc::new(Spanned::dummy(Expr::Bool(true)))
}

fn op_body(module: &tla_core::ast::Module, name: &str) -> Arc<Spanned<Expr>> {
    module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            tla_core::ast::Unit::Operator(def) if def.name.node == name => {
                Some(Arc::new(def.body.clone()))
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("missing operator {name}"))
}

#[test]
fn state_leaf_boundary_reuse_stays_disabled_after_enabled() {
    assert!(!state_leaf_preserves_batch_boundary(&LiveExpr::enabled(
        dummy_expr(),
        1,
    )));
}

#[test]
fn state_leaf_boundary_reuse_allows_plain_state_predicates() {
    assert!(state_leaf_preserves_batch_boundary(&LiveExpr::state_pred(
        dummy_expr(),
        1,
    )));
}

#[test]
fn action_leaf_boundary_reuse_disables_subscripted_state_change() {
    assert!(!action_leaf_preserves_batch_boundary(
        &LiveExpr::StateChanged {
            subscript: Some(dummy_expr()),
            bindings: None,
            tag: 1,
        }
    ));
}

#[test]
fn action_leaf_boundary_reuse_allows_plain_action_predicates() {
    assert!(action_leaf_preserves_batch_boundary(
        &LiveExpr::action_pred(dummy_expr(), 1,)
    ));
}

#[test]
fn state_leaf_boundary_reuse_recovers_after_enabled_leaf() {
    let module = parse_module(INLINE_LEAF_EVAL_SPEC);
    let mut ctx = EvalCtx::new();
    ctx.register_vars(["x".to_string()]);

    let registry = ctx.var_registry().clone();
    let current = State::from_pairs([("x", Value::int(0))]);
    let next = State::from_pairs([("x", Value::int(1))]);
    let current_arr = ArrayState::from_state(&current, &registry);
    let next_arr = ArrayState::from_state(&next, &registry);

    let enabled_leaf = LiveExpr::enabled(op_body(&module, "SetOne"), 1);
    let is_zero_leaf = LiveExpr::state_pred(op_body(&module, "IsZero"), 2);
    let leaves = [&enabled_leaf, &is_zero_leaf];

    let results = eval_state_leaves_with_array_successors(
        &mut ctx,
        &leaves,
        current.fingerprint(),
        &current_arr,
        &[(&next_arr, next.fingerprint())],
    )
    .expect("mixed state leaves should evaluate successfully");

    assert_eq!(
        results,
        vec![(1, true), (2, true)],
        "plain state predicates must still evaluate correctly after an ENABLED leaf forces a fresh boundary",
    );
}

#[test]
fn action_leaf_boundary_reuse_recovers_after_subscripted_change_leaf() {
    let module = parse_module(INLINE_LEAF_EVAL_SPEC);
    let mut ctx = EvalCtx::new();
    ctx.register_vars(["x".to_string()]);

    let registry = ctx.var_registry().clone();
    let current = State::from_pairs([("x", Value::int(0))]);
    let next = State::from_pairs([("x", Value::int(1))]);
    let current_arr = ArrayState::from_state(&current, &registry);
    let next_arr = ArrayState::from_state(&next, &registry);

    let changed_leaf = LiveExpr::state_changed(Some(op_body(&module, "XValue")), 1);
    let set_one_leaf = LiveExpr::action_pred(op_body(&module, "SetOne"), 2);
    let leaves = [&changed_leaf, &set_one_leaf];

    let results = eval_action_leaves_array(
        &mut ctx,
        &leaves,
        current.fingerprint(),
        &current_arr,
        next.fingerprint(),
        &next_arr,
    )
    .expect("mixed action leaves should evaluate successfully");

    assert_eq!(
        results,
        vec![(1, true), (2, true)],
        "plain action predicates must still evaluate correctly after a subscripted change leaf forces a fresh boundary",
    );
}
