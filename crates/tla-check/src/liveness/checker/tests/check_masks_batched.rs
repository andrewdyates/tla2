// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! batched vs fallback populate_node_check_masks equivalence tests
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use super::helpers::{action_pred_xprime_eq_x, action_pred_xprime_eq_x_plus_1, state_pred_x_eq};
use super::*;
use crate::liveness::test_helpers::{
    empty_successors, make_checker, make_checker_with_vars, spanned,
};
use crate::liveness::LiveExpr;
use crate::Value;
use std::sync::Arc;
use tla_core::ast::Expr;

/// Test that the batched eval path produces identical results to the fallback path.
///
/// Creates two checkers with the same graph/checks — one with VarRegistry (batched)
/// and one without (fallback) — and verifies the masks are identical.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_batched_vs_fallback_produce_identical_masks() {
    let formula = LiveExpr::always(LiveExpr::Bool(true));
    let check_state = vec![state_pred_x_eq(0, 9010)];
    let check_action = vec![action_pred_xprime_eq_x_plus_1(9011)];
    let state_used = vec![true];
    let action_used = vec![true];

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    // Run with fallback path (empty VarRegistry)
    let mut fallback = make_checker(formula.clone());
    let mut get_successors = empty_successors;
    let init = fallback
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    let n0_fb = init[0];
    let added = fallback
        .add_successors(n0_fb, std::slice::from_ref(&s1), &mut get_successors, None)
        .unwrap();
    let n1_fb = added[0];
    let _ = fallback
        .add_successors(n1_fb, std::slice::from_ref(&s0), &mut get_successors, None)
        .unwrap();
    fallback
        .populate_node_check_masks(&check_action, &check_state, &action_used, &state_used, 0)
        .unwrap();

    // Run with batched path (populated VarRegistry)
    let mut batched = make_checker_with_vars(formula, &["x"]);
    let init = batched
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    let n0_bt = init[0];
    let added = batched
        .add_successors(n0_bt, std::slice::from_ref(&s1), &mut get_successors, None)
        .unwrap();
    let n1_bt = added[0];
    let _ = batched
        .add_successors(n1_bt, std::slice::from_ref(&s0), &mut get_successors, None)
        .unwrap();
    batched
        .populate_node_check_masks(&check_action, &check_state, &action_used, &state_used, 0)
        .unwrap();

    // Compare masks — both paths must produce identical results
    let fb_n0 = fallback.graph().get_node_info(&n0_fb).unwrap();
    let fb_n1 = fallback.graph().get_node_info(&n1_fb).unwrap();
    let bt_n0 = batched.graph().get_node_info(&n0_bt).unwrap();
    let bt_n1 = batched.graph().get_node_info(&n1_bt).unwrap();

    assert_eq!(
        fb_n0.state_check_mask, bt_n0.state_check_mask,
        "state mask for n0 must be identical between fallback and batched paths"
    );
    assert_eq!(
        fb_n1.state_check_mask, bt_n1.state_check_mask,
        "state mask for n1 must be identical between fallback and batched paths"
    );
    assert_eq!(
        fb_n0.action_check_masks, bt_n0.action_check_masks,
        "action masks for n0 must be identical between fallback and batched paths"
    );
    assert_eq!(
        fb_n1.action_check_masks, bt_n1.action_check_masks,
        "action masks for n1 must be identical between fallback and batched paths"
    );
}

/// Multi-check variant of `test_batched_vs_fallback_produce_identical_masks`.
///
/// Uses 2 state checks and 2 action checks to verify bitmask indexing is correct
/// when multiple checks share the same transition's state-binding epoch. A bug
/// where bit N is written to slot N-1, or where check[1]'s INSTANCE chain is not
/// reused from check[0], would produce divergent masks (#2364).
///
/// Graph: s0 <-> s1, plus self-loop s0 -> s0 to exercise both action check bits.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_batched_vs_fallback_multi_check_masks() {
    let formula = LiveExpr::always(LiveExpr::Bool(true));
    // Two state checks: x==0 (true on s0) and x==1 (true on s1)
    let check_state = vec![state_pred_x_eq(0, 9020), state_pred_x_eq(1, 9021)];
    // Two action checks: x'==x+1 (true on 0->1) and x'==x (true on stuttering 0->0)
    let check_action = vec![
        action_pred_xprime_eq_x_plus_1(9022),
        action_pred_xprime_eq_x(9023),
    ];
    let state_used = vec![true, true];
    let action_used = vec![true, true];

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    // Run with fallback path (empty VarRegistry)
    let (fb_n0, fb_n1) = {
        let mut fallback = make_checker(formula.clone());
        let mut get_successors = empty_successors;
        let init = fallback
            .add_initial_state(&s0, &mut get_successors, None)
            .unwrap();
        let n0 = init[0];
        let added = fallback
            .add_successors(n0, std::slice::from_ref(&s1), &mut get_successors, None)
            .unwrap();
        let n1 = added[0];
        let _ = fallback
            .add_successors(n1, std::slice::from_ref(&s0), &mut get_successors, None)
            .unwrap();
        // Self-loop s0 -> s0 (stuttering)
        let _ = fallback
            .add_successors(n0, std::slice::from_ref(&s0), &mut get_successors, None)
            .unwrap();
        fallback
            .populate_node_check_masks(&check_action, &check_state, &action_used, &state_used, 0)
            .unwrap();
        let n0_info = fallback.graph().get_node_info(&n0).unwrap().into_owned();
        let n1_info = fallback.graph().get_node_info(&n1).unwrap().into_owned();
        (n0_info, n1_info)
    };

    // Run with batched path (populated VarRegistry)
    let (bt_n0, bt_n1) = {
        let mut batched = make_checker_with_vars(formula, &["x"]);
        let mut get_successors = empty_successors;
        let init = batched
            .add_initial_state(&s0, &mut get_successors, None)
            .unwrap();
        let n0 = init[0];
        let added = batched
            .add_successors(n0, std::slice::from_ref(&s1), &mut get_successors, None)
            .unwrap();
        let n1 = added[0];
        let _ = batched
            .add_successors(n1, std::slice::from_ref(&s0), &mut get_successors, None)
            .unwrap();
        // Self-loop s0 -> s0 (stuttering)
        let _ = batched
            .add_successors(n0, std::slice::from_ref(&s0), &mut get_successors, None)
            .unwrap();
        batched
            .populate_node_check_masks(&check_action, &check_state, &action_used, &state_used, 0)
            .unwrap();
        let n0_info = batched.graph().get_node_info(&n0).unwrap().into_owned();
        let n1_info = batched.graph().get_node_info(&n1).unwrap().into_owned();
        (n0_info, n1_info)
    };

    // Compare masks — both paths must produce identical results
    assert_eq!(
        fb_n0.state_check_mask, bt_n0.state_check_mask,
        "state mask for n0 must match: x==0 should be bit 0"
    );
    assert_eq!(
        fb_n1.state_check_mask, bt_n1.state_check_mask,
        "state mask for n1 must match: x==1 should be bit 1"
    );
    assert_eq!(
        fb_n0.action_check_masks, bt_n0.action_check_masks,
        "action masks for n0 must match (2 successors with different bit patterns)"
    );
    assert_eq!(
        fb_n1.action_check_masks, bt_n1.action_check_masks,
        "action masks for n1 must match (1 successor, no checks true)"
    );

    // Verify non-triviality: state masks differ between nodes
    assert_ne!(
        fb_n0.state_check_mask, fb_n1.state_check_mask,
        "n0 and n1 should have different state masks (x==0 vs x==1)"
    );

    // Verify non-triviality: n0 has two successors with different action masks
    assert_eq!(
        fb_n0.action_check_masks.len(),
        2,
        "n0 should have 2 successors (n1 and self-loop)"
    );
    assert_ne!(
        fb_n0.action_check_masks[0], fb_n0.action_check_masks[1],
        "n0's two successor edges should have different action masks (bit 0 vs bit 1)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_composite_action_check_populates_cross_property_leaf_caches() {
    let formula = LiveExpr::always(LiveExpr::Bool(true));
    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
    let x_plus_1 = spanned(Expr::Add(
        Box::new(x),
        Box::new(spanned(Expr::Int(1.into()))),
    ));
    let inc_expr = Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(x_plus_1))));
    let composite_check = LiveExpr::or(vec![
        LiveExpr::not(LiveExpr::enabled(Arc::clone(&inc_expr), 9100)),
        LiveExpr::action_pred(Arc::clone(&inc_expr), 9101),
    ]);
    let check_action = vec![composite_check];
    let action_used = vec![true];

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    // Part of #3174: Verify eval fallback produces correct results
    // without cross-property per-tag caches.
    let mut checker = make_checker_with_vars(formula, &["x"]);
    let mut get_successors = empty_successors;
    let init = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    let n0 = init[0];
    let added = checker
        .add_successors(n0, std::slice::from_ref(&s1), &mut get_successors, None)
        .unwrap();
    let n1 = added[0];
    let _ = checker
        .add_successors(n0, std::slice::from_ref(&s0), &mut get_successors, None)
        .unwrap();
    let _ = checker
        .add_successors(n1, std::slice::from_ref(&s0), &mut get_successors, None)
        .unwrap();
    checker
        .populate_node_check_masks(&check_action, &[], &action_used, &[], 0)
        .unwrap();

    let n0_info = checker.graph().get_node_info(&n0).unwrap();
    let n1_info = checker.graph().get_node_info(&n1).unwrap();
    assert!(
        n0_info.action_check_masks.iter().any(|mask| mask.get(0)),
        "~ENABLED Inc \\/ Inc should pass on the Inc transition"
    );
    assert!(
        n0_info.action_check_masks.iter().any(|mask| !mask.get(0)),
        "~ENABLED Inc \\/ Inc should fail on a stuttering transition while Inc is enabled"
    );
    assert!(
        n1_info
            .action_check_masks
            .first()
            .is_some_and(|mask| mask.get(0)),
        "~ENABLED Inc \\/ Inc should pass when Inc is disabled at the source state"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_composite_action_checks_batched_leaf_reconstruction_matches_fallback() {
    let formula = LiveExpr::always(LiveExpr::Bool(true));
    let x = spanned(Expr::Ident(
        "x".to_string(),
        tla_core::name_intern::NameId::INVALID,
    ));
    let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
    let x_plus_1 = spanned(Expr::Add(
        Box::new(x.clone()),
        Box::new(spanned(Expr::Int(1.into()))),
    ));
    let inc_expr = Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(x_plus_1))));
    let enabled_inc = LiveExpr::enabled(Arc::clone(&inc_expr), 9200);
    let action_inc = LiveExpr::action_pred(Arc::clone(&inc_expr), 9201);
    let state_changed = LiveExpr::state_changed(None, 9202);
    let check_action = vec![
        LiveExpr::or(vec![LiveExpr::not(enabled_inc.clone()), action_inc.clone()]),
        LiveExpr::and(vec![state_changed.clone(), action_inc.clone()]),
        LiveExpr::and(vec![LiveExpr::not(enabled_inc), state_changed]),
    ];
    let action_used = vec![true, true, true];

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let fallback_masks = {
        let mut checker = make_checker(formula.clone());
        let mut get_successors = empty_successors;
        let init = checker
            .add_initial_state(&s0, &mut get_successors, None)
            .unwrap();
        let n0 = init[0];
        let added = checker
            .add_successors(n0, std::slice::from_ref(&s1), &mut get_successors, None)
            .unwrap();
        let n1 = added[0];
        let _ = checker
            .add_successors(n0, std::slice::from_ref(&s0), &mut get_successors, None)
            .unwrap();
        let _ = checker
            .add_successors(n1, std::slice::from_ref(&s0), &mut get_successors, None)
            .unwrap();
        checker
            .populate_node_check_masks(&check_action, &[], &action_used, &[], 0)
            .unwrap();
        (
            checker.graph().get_node_info(&n0).unwrap().into_owned(),
            checker.graph().get_node_info(&n1).unwrap().into_owned(),
        )
    };

    let batched_masks = {
        let mut checker = make_checker_with_vars(formula, &["x"]);
        let mut get_successors = empty_successors;
        let init = checker
            .add_initial_state(&s0, &mut get_successors, None)
            .unwrap();
        let n0 = init[0];
        let added = checker
            .add_successors(n0, std::slice::from_ref(&s1), &mut get_successors, None)
            .unwrap();
        let n1 = added[0];
        let _ = checker
            .add_successors(n0, std::slice::from_ref(&s0), &mut get_successors, None)
            .unwrap();
        let _ = checker
            .add_successors(n1, std::slice::from_ref(&s0), &mut get_successors, None)
            .unwrap();
        checker
            .populate_node_check_masks(&check_action, &[], &action_used, &[], 0)
            .unwrap();
        (
            checker.graph().get_node_info(&n0).unwrap().into_owned(),
            checker.graph().get_node_info(&n1).unwrap().into_owned(),
        )
    };

    assert_eq!(
        fallback_masks.0.action_check_masks,
        batched_masks.0.action_check_masks
    );
    assert_eq!(
        fallback_masks.1.action_check_masks,
        batched_masks.1.action_check_masks
    );
}
