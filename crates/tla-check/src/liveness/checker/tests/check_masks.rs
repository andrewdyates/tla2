// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! populate_node_check_masks
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use super::helpers::{action_pred_xprime_eq_x, action_pred_xprime_eq_x_plus_1, state_pred_x_eq};
use super::*;
use crate::liveness::test_helpers::{empty_successors, make_checker, make_checker_with_vars};
use crate::liveness::LiveExpr;
use crate::Value;

// =============================================================================
// Direct unit test for populate_node_check_masks (#2572, replaces #2497)
// =============================================================================

/// Test `populate_node_check_masks` directly — verify per-node bitmask values
/// for a known 2-state graph with one action check and one state check.
///
/// Graph: s0(x=0) -> s1(x=1) -> s0(x=0)
/// State check[0]: x=0 (passes on s0, fails on s1)
/// Action check[0]: x'=x+1 (passes on s0->s1, fails on s1->s0)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_populate_node_check_masks_produces_correct_bitmasks() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("add_initial_state");
    assert_eq!(init_nodes.len(), 1);
    let n0 = init_nodes[0];
    let added = checker
        .add_successors(n0, std::slice::from_ref(&s1), &mut get_successors, None)
        .expect("add_successors s0->s1");
    assert_eq!(added.len(), 1);
    let n1 = added[0];
    let _ = checker
        .add_successors(n1, std::slice::from_ref(&s0), &mut get_successors, None)
        .expect("add_successors s1->s0");

    // State check: x=0 (passes on s0, fails on s1)
    let check_state = vec![state_pred_x_eq(0, 8001)];
    // Action check: x'=x+1 (passes on 0->1, fails on 1->0)
    let check_action = vec![action_pred_xprime_eq_x_plus_1(8002)];
    let state_used = vec![true];
    let action_used = vec![true];

    checker
        .populate_node_check_masks(&check_action, &check_state, &action_used, &state_used, 0)
        .expect("populate_node_check_masks should succeed");

    // Read per-node state masks
    let n0_info = checker.graph().get_node_info(&n0).unwrap();
    let n1_info = checker.graph().get_node_info(&n1).unwrap();

    // State mask: n0 (x=0) should have bit 0 set, n1 (x=1) should not
    assert!(
        n0_info.state_check_mask.get(0),
        "state check x=0 should pass on n0 (x=0)"
    );
    assert!(
        !n1_info.state_check_mask.get(0),
        "state check x=0 should fail on n1 (x=1)"
    );

    // Action mask: n0->n1 (successor[0]) should have bit 0 set
    assert!(
        n0_info.action_check_masks.first().is_some_and(|m| m.get(0)),
        "action check x'=x+1 should pass on edge n0->n1"
    );
    // n1->n0 (successor[0]) should NOT have bit 0 set
    assert!(
        !n1_info.action_check_masks.first().is_some_and(|m| m.get(0)),
        "action check x'=x+1 should fail on edge n1->n0"
    );

    // Round-trip: EaEdgeCheck should produce correct result (#2704)
    use crate::liveness::checker::ea_bitmask_query::EaEdgeCheck;
    let ec = EaEdgeCheck::new(&[0], &[0]).expect("should return Some when indices are non-empty");
    // Edge n0->n1: action passes, state(n0)=pass, state(n1)=fail → excluded
    // Edge n1->n0: action fails → excluded
    assert!(
        !ec.allows_edge_pair(checker.graph(), &n0, &n1),
        "n0->n1 should fail EA check when state x=0 fails on n1"
    );
    assert!(
        !ec.allows_edge_pair(checker.graph(), &n1, &n0),
        "n1->n0 should fail EA check when action x'=x+1 fails"
    );
}

/// Regression for #2732 Slice E: disk-backed graph node rewrites must keep
/// working after the pointer table reaches its insertion load limit.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_populate_node_check_masks_disk_graph_at_pointer_table_limit() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    checker.graph = crate::liveness::behavior_graph::BehaviorGraph::new_disk_backed(4).unwrap();
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s2 = State::from_pairs([("x", Value::int(2))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("add_initial_state");
    let n0 = init_nodes[0];
    let added = checker
        .add_successors(n0, std::slice::from_ref(&s1), &mut get_successors, None)
        .expect("add_successors s0->s1");
    let n1 = added[0];
    let added = checker
        .add_successors(n1, std::slice::from_ref(&s2), &mut get_successors, None)
        .expect("add_successors s1->s2");
    let n2 = added[0];
    let _ = checker
        .add_successors(n2, std::slice::from_ref(&s0), &mut get_successors, None)
        .expect("add_successors s2->s0");

    let check_state = vec![state_pred_x_eq(0, 8012)];
    let check_action = vec![action_pred_xprime_eq_x_plus_1(8013)];
    let state_used = vec![true];
    let action_used = vec![true];

    checker
        .populate_node_check_masks(&check_action, &check_state, &action_used, &state_used, 0)
        .expect("disk-backed populate_node_check_masks should update existing nodes at capacity threshold");

    let n0_info = checker.graph().get_node_info(&n0).unwrap();
    assert!(n0_info.state_check_mask.get(0));
    assert!(n0_info.action_check_masks.first().is_some_and(|m| m.get(0)));
}

/// Test `populate_node_check_masks` with unused check indices — verifies
/// that *_used=false causes the check to be skipped (masks stay zero).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_populate_node_check_masks_skips_unused_checks() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("add_initial_state");
    let n0 = init_nodes[0];
    let _ = checker
        .add_successors(
            init_nodes[0],
            std::slice::from_ref(&s0),
            &mut get_successors,
            None,
        )
        .expect("add self-loop");

    // Provide checks but mark them as unused
    let check_state = vec![state_pred_x_eq(0, 8010)];
    let check_action = vec![action_pred_xprime_eq_x(8011)];
    let state_used = vec![false]; // unused
    let action_used = vec![false]; // unused

    checker
        .populate_node_check_masks(&check_action, &check_state, &action_used, &state_used, 0)
        .expect("populate_node_check_masks should succeed");

    // All masks should be zero because no checks were evaluated
    let info = checker.graph().get_node_info(&n0).unwrap();
    assert!(
        info.state_check_mask.is_empty(),
        "unused state check should leave state_check_mask at 0"
    );
    for (idx, mask) in info.action_check_masks.iter().enumerate() {
        assert!(
            mask.is_empty(),
            "unused action check should leave action_check_masks[{idx}] at 0"
        );
    }
}

// =============================================================================
// Batched eval path coverage (#2364 — eval_action_checks_batched)
// =============================================================================

/// Test `populate_node_check_masks` via the array-based batching path.
///
/// `make_checker_with_vars` creates an EvalCtx with populated VarRegistry,
/// which causes `eval_action_checks_batched` to take the optimized batch path
/// (`!registry_is_empty` branch) instead of the per-check fallback.
/// This test mirrors `test_populate_node_check_masks_produces_correct_bitmasks`
/// but exercises the code path that was previously untested.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_populate_node_check_masks_batched_path() {
    let mut checker = make_checker_with_vars(LiveExpr::always(LiveExpr::Bool(true)), &["x"]);
    let mut get_successors = empty_successors;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("add_initial_state");
    assert_eq!(init_nodes.len(), 1);
    let n0 = init_nodes[0];
    let added = checker
        .add_successors(n0, std::slice::from_ref(&s1), &mut get_successors, None)
        .expect("add_successors s0->s1");
    assert_eq!(added.len(), 1);
    let n1 = added[0];
    let _ = checker
        .add_successors(n1, std::slice::from_ref(&s0), &mut get_successors, None)
        .expect("add_successors s1->s0");

    // State check: x=0 (passes on s0, fails on s1)
    let check_state = vec![state_pred_x_eq(0, 9001)];
    // Action check: x'=x+1 (passes on 0->1, fails on 1->0)
    let check_action = vec![action_pred_xprime_eq_x_plus_1(9002)];
    let state_used = vec![true];
    let action_used = vec![true];

    checker
        .populate_node_check_masks(&check_action, &check_state, &action_used, &state_used, 0)
        .expect("populate_node_check_masks should succeed via batched path");

    let n0_info = checker.graph().get_node_info(&n0).unwrap();
    let n1_info = checker.graph().get_node_info(&n1).unwrap();

    // State mask: n0 (x=0) should have bit 0 set, n1 (x=1) should not
    assert!(
        n0_info.state_check_mask.get(0),
        "batched: state check x=0 should pass on n0 (x=0)"
    );
    assert!(
        !n1_info.state_check_mask.get(0),
        "batched: state check x=0 should fail on n1 (x=1)"
    );

    // Action mask: n0->n1 (successor[0]) should have bit 0 set
    assert!(
        n0_info.action_check_masks.first().is_some_and(|m| m.get(0)),
        "batched: action check x'=x+1 should pass on edge n0->n1"
    );
    // n1->n0 (successor[0]) should NOT have bit 0 set
    assert!(
        !n1_info.action_check_masks.first().is_some_and(|m| m.get(0)),
        "batched: action check x'=x+1 should fail on edge n1->n0"
    );
}
