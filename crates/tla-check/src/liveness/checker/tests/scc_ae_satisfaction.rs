// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SCC AE state/action satisfaction tests
//!
//! Split from liveness/checker/tests.rs — Part of #2779

use super::helpers::state_pred_x_eq;
use super::*;
use crate::liveness::test_helpers::{empty_successors, make_checker};
use crate::liveness::LiveExpr;
use crate::Value;

/// Test `scc_ae_state_satisfied` with a single SCC node that satisfies the check.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_ae_state_satisfied_single_node_passes() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::scc::Scc;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    // Set bit 0 and bit 2 on n0's state mask
    graph.get_node_info_mut(&n0).unwrap().state_check_mask = CheckMask::from_u64(0b101u64);

    let scc = Scc::new(vec![n0]);

    // Check index 0 — bit 0 is set → satisfied
    assert!(LivenessChecker::scc_ae_state_satisfied(&scc, &[0], &graph));
    // Check index 2 — bit 2 is set → satisfied
    assert!(LivenessChecker::scc_ae_state_satisfied(&scc, &[2], &graph));
    // Check both 0 and 2 — both set on same node → satisfied
    assert!(LivenessChecker::scc_ae_state_satisfied(
        &scc,
        &[0, 2],
        &graph
    ));
    // Check index 1 — bit 1 is NOT set → unsatisfied
    assert!(!LivenessChecker::scc_ae_state_satisfied(&scc, &[1], &graph));
}

/// Test `scc_ae_state_satisfied` with empty indices — should return true trivially.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_ae_state_satisfied_empty_indices() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::scc::Scc;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);

    let scc = Scc::new(vec![n0]);
    assert!(LivenessChecker::scc_ae_state_satisfied(&scc, &[], &graph));
}

/// Test `scc_ae_state_satisfied` where different nodes in the SCC satisfy different checks.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_ae_state_satisfied_distributed_across_nodes() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::scc::Scc;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s1, 0).unwrap();
    let n1 = BehaviorGraphNode::from_state(&s1, 0);

    // n0 has bit 0, n1 has bit 1 — each satisfies a different AE constraint
    graph.get_node_info_mut(&n0).unwrap().state_check_mask = CheckMask::from_u64(0b01u64);
    graph.get_node_info_mut(&n1).unwrap().state_check_mask = CheckMask::from_u64(0b10u64);

    let scc = Scc::new(vec![n0, n1]);

    // Both checks satisfied (distributed across different nodes)
    assert!(LivenessChecker::scc_ae_state_satisfied(
        &scc,
        &[0, 1],
        &graph
    ));
    // Check 2 is satisfied by neither node
    assert!(!LivenessChecker::scc_ae_state_satisfied(
        &scc,
        &[0, 1, 2],
        &graph
    ));
}

/// Test `scc_ae_action_satisfied` with a self-loop edge that satisfies the check.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_ae_action_satisfied_self_loop() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::scc::Scc;
    use rustc_hash::FxHashSet;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s0, 0).unwrap();

    // Action check 0 passes on the self-loop edge
    graph.get_node_info_mut(&n0).unwrap().action_check_masks = vec![CheckMask::from_u64(0b01u64)];

    let scc = Scc::new(vec![n0]);
    let scc_set: FxHashSet<_> = scc.nodes().iter().copied().collect();

    // Check 0 — bit 0 set on self-loop → satisfied
    assert!(LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[0],
        None,
        &graph,
        &scc_set
    ));
    // Check 1 — bit 1 NOT set → unsatisfied
    assert!(!LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[1],
        None,
        &graph,
        &scc_set
    ));
}

/// Test `scc_ae_action_satisfied` with empty indices — should return true trivially.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_ae_action_satisfied_empty_indices() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::scc::Scc;
    use rustc_hash::FxHashSet;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);

    let scc = Scc::new(vec![n0]);
    let scc_set: FxHashSet<_> = scc.nodes().iter().copied().collect();

    assert!(LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[],
        None,
        &graph,
        &scc_set
    ));
}

/// Test `scc_ae_action_satisfied` with EA edge filtering via EaEdgeCheck (#2704).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_ae_action_satisfied_ea_edge_filter() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::checker::ea_bitmask_query::EaEdgeCheck;
    use crate::liveness::scc::Scc;
    use rustc_hash::FxHashSet;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s1, 0).unwrap();
    let n1 = BehaviorGraphNode::from_state(&s1, 0);
    graph.add_successor(n1, &s0, 0).unwrap();

    // AE check 0 passes on both edges.
    // EA check 1 passes only on n0→n1 (bit 1 set on n0's edge, not n1's).
    // EA check 2 passes on neither edge (simulates empty allowed set).
    graph.get_node_info_mut(&n0).unwrap().action_check_masks = vec![CheckMask::from_u64(0b011u64)]; // bits 0,1 set
    graph.get_node_info_mut(&n1).unwrap().action_check_masks = vec![CheckMask::from_u64(0b001u64)]; // bit 0 only

    let scc = Scc::new(vec![n0, n1]);
    let scc_set: FxHashSet<_> = scc.nodes().iter().copied().collect();

    // Without EA filter — AE check 0 satisfied (both edges have bit 0)
    assert!(LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[0],
        None,
        &graph,
        &scc_set
    ));

    // EA filter on action check 1: only n0→n1 passes → AE check 0 still satisfied
    let ea_partial = EaEdgeCheck::new(&[1], &[]);
    assert!(LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[0],
        ea_partial.as_ref(),
        &graph,
        &scc_set
    ));

    // EA filter on action check 2: neither edge has bit 2 → all filtered → unsatisfied
    let ea_empty = EaEdgeCheck::new(&[2], &[]);
    assert!(!LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[0],
        ea_empty.as_ref(),
        &graph,
        &scc_set
    ));
}

/// Test `scc_ae_action_satisfied` filters out edges to nodes outside the SCC.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_ae_action_satisfied_ignores_non_scc_successors() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::scc::Scc;
    use rustc_hash::FxHashSet;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s1, 0).unwrap();
    let _n1 = BehaviorGraphNode::from_state(&s1, 0);

    // n0->n1: check 0 passes (but n1 is NOT in the SCC)
    graph.get_node_info_mut(&n0).unwrap().action_check_masks = vec![CheckMask::from_u64(0b01u64)];

    // SCC contains only n0 (n1 is outside — n1 exists in graph but not in SCC set)
    let scc = Scc::new(vec![n0]);
    let scc_set: FxHashSet<_> = scc.nodes().iter().copied().collect();

    // Check 0 — edge to n1 is filtered (n1 not in SCC) → unsatisfied
    assert!(!LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[0],
        None,
        &graph,
        &scc_set
    ));
}

// =============================================================================
// Boundary tests for u64 word boundaries in multi-word CheckMask
// =============================================================================

/// Test `scc_ae_state_satisfied` at bit index 63 (the last bit in the first u64 word).
///
/// Verifies the boundary within a single word. Multi-word indices starting at
/// 64 are covered by the regression below.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_ae_state_satisfied_boundary_index_63() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::scc::Scc;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);

    // Set ONLY bit 63 (the final bit in the first u64 word)
    graph.get_node_info_mut(&n0).unwrap().state_check_mask = CheckMask::from_u64(1u64 << 63);

    let scc = Scc::new(vec![n0]);

    // Check index 63 — bit 63 is set → satisfied
    assert!(LivenessChecker::scc_ae_state_satisfied(&scc, &[63], &graph));
    // Check index 0 — bit 0 is NOT set → unsatisfied
    assert!(!LivenessChecker::scc_ae_state_satisfied(&scc, &[0], &graph));
    // Check both 0 and 63 — 0 is missing → unsatisfied
    assert!(!LivenessChecker::scc_ae_state_satisfied(
        &scc,
        &[0, 63],
        &graph
    ));
}

/// Test `scc_ae_action_satisfied` at bit index 63 (self-loop at the first-word boundary).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_ae_action_satisfied_boundary_index_63() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::scc::Scc;
    use rustc_hash::FxHashSet;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s0, 0).unwrap();

    // Self-loop: action check 63 passes (final bit in the first u64 word)
    graph.get_node_info_mut(&n0).unwrap().action_check_masks =
        vec![CheckMask::from_u64(1u64 << 63)];

    let scc = Scc::new(vec![n0]);
    let scc_set: FxHashSet<_> = scc.nodes().iter().copied().collect();

    // Check index 63 — bit 63 set on self-loop → satisfied
    assert!(LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[63],
        None,
        &graph,
        &scc_set
    ));
    // Check index 0 — bit 0 NOT set → unsatisfied
    assert!(!LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[0],
        None,
        &graph,
        &scc_set
    ));
}

/// Test `scc_ae_state_satisfied` across the 63/64 and 127/128 word boundaries.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_ae_state_satisfied_multiword_boundaries() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::scc::Scc;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);

    let mut mask = CheckMask::new();
    mask.set(64);
    mask.set(127);
    graph.get_node_info_mut(&n0).unwrap().state_check_mask = mask;

    let scc = Scc::new(vec![n0]);

    assert!(LivenessChecker::scc_ae_state_satisfied(&scc, &[64], &graph));
    assert!(LivenessChecker::scc_ae_state_satisfied(
        &scc,
        &[127],
        &graph
    ));
    assert!(LivenessChecker::scc_ae_state_satisfied(
        &scc,
        &[64, 127],
        &graph
    ));
    assert!(!LivenessChecker::scc_ae_state_satisfied(
        &scc,
        &[63],
        &graph
    ));
    assert!(!LivenessChecker::scc_ae_state_satisfied(
        &scc,
        &[128],
        &graph
    ));
    assert!(!LivenessChecker::scc_ae_state_satisfied(
        &scc,
        &[63, 64],
        &graph
    ));
}

/// Test `scc_ae_action_satisfied` across the 63/64 and 127/128 word boundaries.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_ae_action_satisfied_multiword_boundaries() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::scc::Scc;
    use rustc_hash::FxHashSet;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s0, 0).unwrap();

    let mut mask = CheckMask::new();
    mask.set(64);
    mask.set(127);
    graph.get_node_info_mut(&n0).unwrap().action_check_masks = vec![mask];

    let scc = Scc::new(vec![n0]);
    let scc_set: FxHashSet<_> = scc.nodes().iter().copied().collect();

    assert!(LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[64],
        None,
        &graph,
        &scc_set
    ));
    assert!(LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[127],
        None,
        &graph,
        &scc_set
    ));
    assert!(LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[64, 127],
        None,
        &graph,
        &scc_set
    ));
    assert!(!LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[63],
        None,
        &graph,
        &scc_set
    ));
    assert!(!LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[128],
        None,
        &graph,
        &scc_set
    ));
    assert!(!LivenessChecker::scc_ae_action_satisfied(
        &scc,
        &[63, 64],
        None,
        &graph,
        &scc_set
    ));
}

/// Regression test for #1953: build_witness_cycle_in_scc must return an error
/// when promise checking touches a missing tableau node.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_build_witness_cycle_missing_tableau_node_returns_error() {
    let mut checker = make_checker(LiveExpr::eventually(state_pred_x_eq(1, 1002)));
    let mut get_successors = empty_successors;

    // Add one real node with x=0, which does not fulfill the promise x=1.
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let init_nodes = checker
        .add_initial_state(&s0, &mut get_successors, None)
        .expect("add_initial_state must succeed for test setup");
    assert!(!init_nodes.is_empty());

    // Add a fabricated SCC node with an out-of-range tableau index.
    let missing = BehaviorGraphNode::new(crate::state::Fingerprint(0xABCD_0123_u64), usize::MAX);
    let scc = crate::liveness::tarjan::Scc::new(vec![init_nodes[0], missing]);

    let result = checker.build_witness_cycle_in_scc(&scc, None, &[], &[]);
    let err = result.expect_err("build_witness_cycle_in_scc must error on missing tableau node");
    assert!(
        matches!(err, EvalError::Internal { .. }),
        "expected internal invariant error, got {err:?}"
    );
    assert!(
        err.to_string().contains("tableau invariant violated"),
        "error message should mention tableau invariant violation, got: {}",
        err
    );
}

// =============================================================================
// SCC aggregate mask optimization tests
// =============================================================================

/// Test that `try_build_scc_aggregates` correctly unions state masks.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_aggregate_state_mask_unions_nodes() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::scc::Scc;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s1, 0).unwrap();
    let n1 = BehaviorGraphNode::from_state(&s1, 0);
    graph.add_successor(n1, &s0, 0).unwrap();

    // n0 has bit 0, n1 has bit 1
    graph.get_node_info_mut(&n0).unwrap().state_check_mask = CheckMask::from_u64(0b01);
    graph.get_node_info_mut(&n1).unwrap().state_check_mask = CheckMask::from_u64(0b10);

    let scc = Scc::new(vec![n0, n1]);
    let scc_set = scc.build_node_set();
    let sccs: Vec<&Scc> = vec![&scc];
    let scc_sets = vec![scc_set];

    let aggregates =
        LivenessChecker::try_build_scc_aggregates(&sccs, &scc_sets, None, &graph).unwrap();
    assert_eq!(aggregates.len(), 1);

    // Aggregate should have both bits 0 and 1 set
    let agg = &aggregates[0];
    assert!(
        agg.state_mask.get(0),
        "aggregate should include bit 0 from n0"
    );
    assert!(
        agg.state_mask.get(1),
        "aggregate should include bit 1 from n1"
    );
    assert!(
        !agg.state_mask.get(2),
        "aggregate should NOT include bit 2 (neither node has it)"
    );

    // Verify that contains_all agrees with per-node check
    let required_01 = CheckMask::from_indices(&[0, 1]);
    assert!(
        agg.state_mask.contains_all(&required_01),
        "aggregate contains both bits 0 and 1"
    );
    let required_012 = CheckMask::from_indices(&[0, 1, 2]);
    assert!(
        !agg.state_mask.contains_all(&required_012),
        "aggregate lacks bit 2"
    );
}

/// Test that `try_build_scc_aggregates` correctly unions action masks for intra-SCC edges.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_aggregate_action_mask_intra_scc_only() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::scc::Scc;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s2 = State::from_pairs([("x", Value::int(2))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s1, 0).unwrap();
    let n1 = BehaviorGraphNode::from_state(&s1, 0);
    graph.add_successor(n1, &s0, 0).unwrap();
    // n0 also has an edge to s2 which is NOT in the SCC
    graph.add_successor(n0, &s2, 0).unwrap();

    // n0->n1 (succ_idx 0): bit 0 set
    // n0->s2 (succ_idx 1): bit 1 set (but s2 is outside SCC, should be excluded)
    // n1->n0 (succ_idx 0): bit 2 set
    graph.get_node_info_mut(&n0).unwrap().action_check_masks =
        vec![CheckMask::from_u64(0b01), CheckMask::from_u64(0b10)];
    graph.get_node_info_mut(&n1).unwrap().action_check_masks = vec![CheckMask::from_u64(0b100)];

    let scc = Scc::new(vec![n0, n1]);
    let scc_set = scc.build_node_set();
    let sccs: Vec<&Scc> = vec![&scc];
    let scc_sets = vec![scc_set];

    let aggregates =
        LivenessChecker::try_build_scc_aggregates(&sccs, &scc_sets, None, &graph).unwrap();
    let agg = &aggregates[0];

    // Only intra-SCC edges: n0->n1 (bit 0) and n1->n0 (bit 2)
    assert!(
        agg.action_mask.get(0),
        "aggregate should include bit 0 from n0->n1 edge"
    );
    assert!(
        !agg.action_mask.get(1),
        "aggregate should NOT include bit 1 (n0->s2 is outside SCC)"
    );
    assert!(
        agg.action_mask.get(2),
        "aggregate should include bit 2 from n1->n0 edge"
    );
}

/// Test that aggregate masks produce identical results to per-node checks
/// for the AE satisfaction predicate.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_aggregate_matches_per_node_ae_check() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::scc::Scc;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s2 = State::from_pairs([("x", Value::int(2))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s1, 0).unwrap();
    let n1 = BehaviorGraphNode::from_state(&s1, 0);
    graph.add_successor(n1, &s2, 0).unwrap();
    let n2 = BehaviorGraphNode::from_state(&s2, 0);
    graph.add_successor(n2, &s0, 0).unwrap();

    // Distribute bits across nodes:
    // n0: state bit 0, n1: state bit 1, n2: state bit 2
    graph.get_node_info_mut(&n0).unwrap().state_check_mask = CheckMask::from_u64(0b001);
    graph.get_node_info_mut(&n1).unwrap().state_check_mask = CheckMask::from_u64(0b010);
    graph.get_node_info_mut(&n2).unwrap().state_check_mask = CheckMask::from_u64(0b100);

    // Action bits on edges:
    // n0->n1: bit 0, n1->n2: bit 1, n2->n0: bit 2
    graph.get_node_info_mut(&n0).unwrap().action_check_masks = vec![CheckMask::from_u64(0b001)];
    graph.get_node_info_mut(&n1).unwrap().action_check_masks = vec![CheckMask::from_u64(0b010)];
    graph.get_node_info_mut(&n2).unwrap().action_check_masks = vec![CheckMask::from_u64(0b100)];

    let scc = Scc::new(vec![n0, n1, n2]);
    let scc_set = scc.build_node_set();
    let sccs: Vec<&Scc> = vec![&scc];
    let scc_sets = vec![scc_set.clone()];

    let aggregates =
        LivenessChecker::try_build_scc_aggregates(&sccs, &scc_sets, None, &graph).unwrap();
    let agg = &aggregates[0];

    // Test various AE state index combinations against both methods
    let test_cases: Vec<Vec<usize>> = vec![
        vec![0],
        vec![1],
        vec![2],
        vec![0, 1],
        vec![0, 1, 2],
        vec![3], // not satisfied
        vec![0, 3],
    ];

    for ae_state_idx in &test_cases {
        let per_node = LivenessChecker::scc_ae_state_satisfied(&scc, ae_state_idx, &graph);
        let required = CheckMask::from_indices(ae_state_idx);
        let aggregate = agg.state_mask.contains_all(&required);
        assert_eq!(
            per_node, aggregate,
            "AE state mismatch for indices {:?}: per_node={}, aggregate={}",
            ae_state_idx, per_node, aggregate
        );
    }

    // Test AE action index combinations
    for ae_action_idx in &test_cases {
        let per_node =
            LivenessChecker::scc_ae_action_satisfied(&scc, ae_action_idx, None, &graph, &scc_set);
        let required = CheckMask::from_indices(ae_action_idx);
        let aggregate = agg.action_mask.contains_all(&required);
        assert_eq!(
            per_node, aggregate,
            "AE action mismatch for indices {:?}: per_node={}, aggregate={}",
            ae_action_idx, per_node, aggregate
        );
    }
}

/// Test that aggregate masks with EA edge filtering exclude filtered edges.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_scc_aggregate_with_ea_filter() {
    use crate::liveness::behavior_graph::BehaviorGraph;
    use crate::liveness::checker::ea_bitmask_query::EaEdgeCheck;
    use crate::liveness::scc::Scc;

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let mut graph = BehaviorGraph::new();
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s1, 0).unwrap();
    let n1 = BehaviorGraphNode::from_state(&s1, 0);
    graph.add_successor(n1, &s0, 0).unwrap();

    // n0->n1: action bits 0 and 1, state bits: n0 has bit 5
    // n1->n0: action bit 0
    graph.get_node_info_mut(&n0).unwrap().action_check_masks = vec![CheckMask::from_u64(0b011)];
    graph.get_node_info_mut(&n0).unwrap().state_check_mask = CheckMask::from_u64(1 << 5);
    graph.get_node_info_mut(&n1).unwrap().action_check_masks = vec![CheckMask::from_u64(0b001)];
    graph.get_node_info_mut(&n1).unwrap().state_check_mask = CheckMask::new();

    let scc = Scc::new(vec![n0, n1]);
    let scc_set = scc.build_node_set();
    let sccs: Vec<&Scc> = vec![&scc];
    let scc_sets = vec![scc_set];

    // EA filter requires action bit 1 on edges. Only n0->n1 passes.
    let ea_check = EaEdgeCheck::new(&[1], &[]);

    // Without EA filter: aggregate action includes bits 0 and 1
    let agg_no_ea =
        LivenessChecker::try_build_scc_aggregates(&sccs, &scc_sets, None, &graph).unwrap();
    assert!(agg_no_ea[0].action_mask.get(0));
    assert!(agg_no_ea[0].action_mask.get(1));

    // With EA filter: n1->n0 is excluded (no bit 1), only n0->n1 survives
    let agg_with_ea =
        LivenessChecker::try_build_scc_aggregates(&sccs, &scc_sets, ea_check.as_ref(), &graph)
            .unwrap();
    assert!(
        agg_with_ea[0].action_mask.get(0),
        "n0->n1 passes EA and has bit 0"
    );
    assert!(
        agg_with_ea[0].action_mask.get(1),
        "n0->n1 passes EA and has bit 1"
    );
    // After EA filtering, only n0->n1 survived, which only has bits 0 and 1
    assert!(
        !agg_with_ea[0].action_mask.get(2),
        "bit 2 never set on any edge"
    );
}
