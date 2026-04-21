// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EaEdgeCheck inline bitmask edge filtering and build_counterexample error cases
//!
//! Split from liveness/checker/tests.rs — Part of #2779
//! Updated for #2704: EaEdgeCheck replaces build_allowed_edges_from_nodes

use super::*;
use crate::liveness::checker::check_mask::CheckMask;
use crate::liveness::checker::ea_bitmask_query::EaEdgeCheck;
use crate::liveness::test_helpers::{empty_successors, make_checker};
use crate::liveness::LiveExpr;
use crate::Value;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_build_counterexample_missing_cycle_node_errors() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    assert!(
        !init_nodes.is_empty(),
        "checker should have at least one initial node"
    );

    let missing = BehaviorGraphNode::new(
        crate::state::Fingerprint(0xCAFEBABE_u64),
        init_nodes[0].tableau_idx,
    );
    let err = checker
        .build_counterexample(&[init_nodes[0], missing])
        .expect_err("counterexample with a missing cycle node must fail");
    assert!(
        matches!(err, EvalError::Internal { .. }),
        "expected internal invariant error, got {err:?}"
    );
    assert!(err
        .to_string()
        .contains("counterexample cycle references missing node"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_build_counterexample_fingerprints_missing_cycle_node_errors() {
    let mut checker = make_checker(LiveExpr::always(LiveExpr::Bool(true)));
    let mut get_successors = empty_successors;
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .unwrap();
    assert!(
        !init_nodes.is_empty(),
        "checker should have at least one initial node"
    );

    let missing = BehaviorGraphNode::new(
        crate::state::Fingerprint(0xCAFEBABE_u64),
        init_nodes[0].tableau_idx,
    );
    let err = checker
        .build_counterexample_fingerprints(&[init_nodes[0], missing])
        .expect_err("fingerprint-only counterexample with a missing cycle node must fail");
    assert!(
        matches!(err, EvalError::Internal { .. }),
        "expected internal invariant error, got {err:?}"
    );
    assert!(err
        .to_string()
        .contains("counterexample cycle references missing node"));
}

// =============================================================================
// =============================================================================
// Algorithm audit: per-node precomputed bitmask tests (#2572)
// =============================================================================

/// Test `EaEdgeCheck` with a simple 2-state graph (#2704).
/// Verifies that inline bitmask-based filtering produces correct results.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ea_edge_check_basic() {
    use crate::liveness::behavior_graph::BehaviorGraph;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s1, 0).unwrap();
    let n1 = BehaviorGraphNode::from_state(&s1, 0);
    graph.add_successor(n1, &s0, 0).unwrap();

    // State mask: check 0 passes on n0 (x=0), fails on n1 (x=1)
    graph.get_node_info_mut(&n0).unwrap().state_check_mask = CheckMask::from_u64(1u64); // bit 0 set
    graph.get_node_info_mut(&n1).unwrap().state_check_mask = CheckMask::from_u64(0u64); // bit 0 not set

    // Action masks: both edges pass check 0
    graph.get_node_info_mut(&n0).unwrap().action_check_masks = vec![CheckMask::from_u64(1u64)]; // n0->n1
    graph.get_node_info_mut(&n1).unwrap().action_check_masks = vec![CheckMask::from_u64(1u64)]; // n1->n0

    // PEM requires EA state check 0 — only edges where BOTH endpoints have bit 0 pass
    let ec = EaEdgeCheck::new(&[], &[0]).expect("should return Some when indices are non-empty");
    // n0->n1: from=n0(pass), to=n1(fail) → excluded
    assert!(
        !ec.allows_edge_pair(&graph, &n0, &n1),
        "n0->n1 should fail EA state check: n1 does not have bit 0"
    );
    // n1->n0: from=n1(fail) → excluded
    assert!(
        !ec.allows_edge_pair(&graph, &n1, &n0),
        "n1->n0 should fail EA state check: n1 does not have bit 0"
    );
}

/// Test `EaEdgeCheck::new` with empty indices returns None.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ea_edge_check_empty_returns_none() {
    let result = EaEdgeCheck::new(&[], &[]);
    assert!(
        result.is_none(),
        "empty indices should return None (no filtering)"
    );
}

/// Test `EaEdgeCheck` with action-only filtering (#2704).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ea_edge_check_action_only() {
    use crate::liveness::behavior_graph::BehaviorGraph;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s1, 0).unwrap();
    let n1 = BehaviorGraphNode::from_state(&s1, 0);
    graph.add_successor(n1, &s0, 0).unwrap();

    // Action check 0 passes on n0->n1, fails on n1->n0
    graph.get_node_info_mut(&n0).unwrap().action_check_masks = vec![CheckMask::from_u64(1u64)]; // bit 0 set
    graph.get_node_info_mut(&n1).unwrap().action_check_masks = vec![CheckMask::from_u64(0u64)]; // bit 0 not set

    let ec = EaEdgeCheck::new(&[0], &[]).expect("should return Some");
    assert!(
        ec.allows_edge_pair(&graph, &n0, &n1),
        "n0->n1 should pass action check 0"
    );
    assert!(
        !ec.allows_edge_pair(&graph, &n1, &n0),
        "n1->n0 should fail action check 0"
    );
}

/// Test `EaEdgeCheck` with multiple check indices (#2704).
/// Verifies that all required checks must pass (AND semantics).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ea_edge_check_multiple_checks_and_semantics() {
    use crate::liveness::behavior_graph::BehaviorGraph;

    let s0 = State::from_pairs([("x", Value::int(0))]);

    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    // Self-loop: n0 -> n0
    graph.add_successor(n0, &s0, 0).unwrap();

    // Action: check 0 passes, check 1 fails (only bit 0 set on self-loop edge)
    graph.get_node_info_mut(&n0).unwrap().action_check_masks = vec![CheckMask::from_u64(0b01u64)];

    // Require both action checks 0 and 1
    let ec = EaEdgeCheck::new(&[0, 1], &[]).expect("should return Some");
    assert!(
        !ec.allows_edge_pair(&graph, &n0, &n0),
        "edge should be excluded when not ALL required action checks pass (AND semantics)"
    );

    // Now both pass
    graph.get_node_info_mut(&n0).unwrap().action_check_masks = vec![CheckMask::from_u64(0b11u64)];
    let ec = EaEdgeCheck::new(&[0, 1], &[]).expect("should return Some");
    assert!(
        ec.allows_edge_pair(&graph, &n0, &n0),
        "edge should pass when all required checks pass"
    );
}

/// Test `EaEdgeCheck` with EA indices at boundaries (0, 62, 63) (#2704).
///
/// Verifies that the `required_action` and `required_state` bitmasks
/// correctly handle the maximum valid index without shift overflow.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ea_edge_check_boundary_indices() {
    use crate::liveness::behavior_graph::BehaviorGraph;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s1, 0).unwrap();
    let n1 = BehaviorGraphNode::from_state(&s1, 0);

    // Set state mask: bits 0, 62, 63 on both nodes
    let state_mask = CheckMask::from_indices(&[0, 62, 63]);
    graph.get_node_info_mut(&n0).unwrap().state_check_mask = state_mask.clone();
    graph.get_node_info_mut(&n1).unwrap().state_check_mask = state_mask.clone();

    // Set action mask on n0's edge to n1: bits 0 and 63
    let action_mask = CheckMask::from_indices(&[0, 63]);
    graph.get_node_info_mut(&n0).unwrap().action_check_masks = vec![action_mask.clone()];

    // EA with state indices [0, 62, 63] and action indices [0, 63]
    let ec = EaEdgeCheck::new(&[0, 63], &[0, 62, 63]).expect("should produce EaEdgeCheck");
    // The edge n0→n1 should be allowed (both state masks pass, action mask passes)
    assert!(
        ec.allows_edge_pair(&graph, &n0, &n1),
        "n0→n1 should pass EA check with boundary indices"
    );
}
