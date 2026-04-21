// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for behavior graph construction and trace reconstruction.

use super::*;
use crate::error::EvalError;
use crate::Value;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_behavior_graph_node_equality() {
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s2 = State::from_pairs([("x", Value::int(1))]);
    let s3 = State::from_pairs([("x", Value::int(2))]);

    // Same state, same tableau index -> equal
    let n1 = BehaviorGraphNode::from_state(&s1, 0);
    let n2 = BehaviorGraphNode::from_state(&s2, 0);
    assert_eq!(n1, n2);

    // Same state, different tableau index -> not equal
    let n3 = BehaviorGraphNode::from_state(&s1, 1);
    assert_ne!(n1, n3);

    // Different state, same tableau index -> not equal
    let n4 = BehaviorGraphNode::from_state(&s3, 0);
    assert_ne!(n1, n4);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_behavior_graph_add_init() {
    let mut graph = BehaviorGraph::new();
    let s1 = State::from_pairs([("x", Value::int(0))]);

    // First add should succeed
    assert!(graph.add_init_node(&s1, 0));
    assert_eq!(graph.len(), 1);
    assert_eq!(graph.init_nodes().len(), 1);

    // Duplicate add should not increase size
    assert!(!graph.add_init_node(&s1, 0));
    assert_eq!(graph.len(), 1);

    // Same state, different tableau index should be added
    assert!(graph.add_init_node(&s1, 1));
    assert_eq!(graph.len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_behavior_graph_add_successor() {
    let mut graph = BehaviorGraph::new();
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    graph.add_init_node(&s0, 0);
    let init_node = BehaviorGraphNode::from_state(&s0, 0);

    // Add successor
    assert!(graph.add_successor(init_node, &s1, 0).unwrap());
    assert_eq!(graph.len(), 2);

    // Check parent pointer
    let succ_node = BehaviorGraphNode::from_state(&s1, 0);
    let info = graph.get_node_info(&succ_node).unwrap();
    assert_eq!(info.parent, Some(init_node));
    assert_eq!(info.depth, 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_behavior_graph_trace_reconstruction() {
    let mut graph = BehaviorGraph::new();
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s2 = State::from_pairs([("x", Value::int(2))]);

    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);

    graph.add_successor(n0, &s1, 0).unwrap();
    let n1 = BehaviorGraphNode::from_state(&s1, 0);

    graph.add_successor(n1, &s2, 1).unwrap();
    let n2 = BehaviorGraphNode::from_state(&s2, 1);

    let trace = graph.reconstruct_trace(n2).unwrap();
    assert_eq!(trace.len(), 3);
    assert_eq!(trace[0].0, s0);
    assert_eq!(trace[0].1, 0);
    assert_eq!(trace[1].0, s1);
    assert_eq!(trace[1].1, 0);
    assert_eq!(trace[2].0, s2);
    assert_eq!(trace[2].1, 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_behavior_graph_fingerprint_trace_reconstruction() {
    let mut graph = BehaviorGraph::new();
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let s2 = State::from_pairs([("x", Value::int(2))]);

    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);

    graph.add_successor(n0, &s1, 0).unwrap();
    let n1 = BehaviorGraphNode::from_state(&s1, 0);

    graph.add_successor(n1, &s2, 1).unwrap();
    let n2 = BehaviorGraphNode::from_state(&s2, 1);

    let trace = graph.reconstruct_fingerprint_trace(n2).unwrap();
    assert_eq!(
        trace,
        vec![
            (s0.fingerprint(), 0),
            (s1.fingerprint(), 0),
            (s2.fingerprint(), 1),
        ]
    );
}

/// Part of #3746: resolve_fingerprint_trace now tolerates partial missing
/// states by skipping them (filter_map). When some states are missing, the
/// result is a shorter trace. When ALL states are missing, it returns an error.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_behavior_graph_resolve_fingerprint_trace_skips_missing_states() {
    let mut graph = BehaviorGraph::new();
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s1, 0).unwrap();
    let n1 = BehaviorGraphNode::from_state(&s1, 0);

    let trace = graph.reconstruct_fingerprint_trace(n1).unwrap();
    assert_eq!(trace.len(), 2, "trace should have s0 and s1");

    // Remove s1 from state_cache — partial missing is tolerated (#3746).
    graph.state_cache.remove(&n1.state_fp);
    let resolved = graph
        .resolve_fingerprint_trace(&trace)
        .expect("partial missing states should be tolerated");
    assert_eq!(
        resolved.len(),
        1,
        "resolved trace should contain only s0 (s1 was skipped)"
    );
    assert_eq!(resolved[0].0.get("x"), Some(&Value::int(0)));

    // Remove s0 as well — ALL states missing produces an error.
    graph.state_cache.remove(&n0.state_fp);
    let err = graph
        .resolve_fingerprint_trace(&trace)
        .expect_err("all states missing must produce an error");
    assert!(
        matches!(err, EvalError::Internal { .. }),
        "expected internal invariant error, got {err:?}"
    );
    assert!(err.to_string().contains("all"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_behavior_graph_add_successor_missing_source_errors() {
    let mut graph = BehaviorGraph::new();
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);
    let missing_from = BehaviorGraphNode::from_state(&s0, 0);

    let err = graph
        .add_successor(missing_from, &s1, 0)
        .expect_err("missing source node must be reported as invariant failure");
    assert!(
        matches!(err, EvalError::Internal { .. }),
        "expected internal invariant error, got {err:?}"
    );
    assert!(err.to_string().contains("source node is missing"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_behavior_graph_trace_reconstruction_missing_node_errors() {
    let mut graph = BehaviorGraph::new();
    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph.add_successor(n0, &s1, 0).unwrap();
    let n1 = BehaviorGraphNode::from_state(&s1, 0);

    let bogus_parent = BehaviorGraphNode::new(Fingerprint(0xDEADBEEF), 0);
    graph.get_node_info_mut(&n1).unwrap().parent = Some(bogus_parent);

    let err = graph
        .reconstruct_trace(n1)
        .expect_err("missing parent node must not produce a truncated trace");
    assert!(
        matches!(err, EvalError::Internal { .. }),
        "expected internal invariant error, got {err:?}"
    );
    assert!(err.to_string().contains("missing node"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_behavior_graph_contains() {
    let mut graph = BehaviorGraph::new();
    let s1 = State::from_pairs([("x", Value::int(1))]);

    let node = BehaviorGraphNode::from_state(&s1, 0);
    assert!(!graph.contains(&node));

    graph.add_init_node(&s1, 0);
    assert!(graph.contains(&node));

    // Different tableau index should not be found
    let node2 = BehaviorGraphNode::from_state(&s1, 1);
    assert!(!graph.contains(&node2));
}

/// Approach I (#2364): states are deduplicated in state_cache by fingerprint.
/// Multiple behavior graph nodes with the same state but different tableau
/// indices share a single State entry in the cache.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_behavior_graph_state_deduplication_across_tableau_indices() {
    let mut graph = BehaviorGraph::new();
    let s0 = State::from_pairs([("x", Value::int(42))]);

    // Add the same state with two different tableau indices
    assert!(graph.add_init_node(&s0, 0));
    assert!(graph.add_init_node(&s0, 1));
    assert_eq!(graph.len(), 2, "two distinct BG nodes");

    // state_cache should have exactly one entry (deduplicated)
    assert_eq!(
        graph.state_cache.len(),
        1,
        "state_cache must deduplicate by fingerprint"
    );

    // Both nodes should return the same state
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    let n1 = BehaviorGraphNode::from_state(&s0, 1);
    let state0 = graph.get_state(&n0).expect("state for tableau 0");
    let state1 = graph.get_state(&n1).expect("state for tableau 1");
    assert_eq!(state0, state1);

    // add_successor with same state, different tableau idx should also dedup
    let s1 = State::from_pairs([("x", Value::int(99))]);
    graph.add_successor(n0, &s1, 0).unwrap();
    graph.add_successor(n1, &s1, 1).unwrap();
    assert_eq!(
        graph.state_cache.len(),
        2,
        "two unique states in cache after successor adds"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disk_backed_behavior_graph_add_successor_and_trace() {
    let mut graph = BehaviorGraph::new_disk_backed(64).unwrap();
    assert!(graph.is_disk_backed());

    let s0 = State::from_pairs([("x", Value::int(0))]);
    let s1 = State::from_pairs([("x", Value::int(1))]);

    assert!(graph.try_add_init_node(&s0, 0).unwrap());
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    assert!(graph.add_successor(n0, &s1, 0).unwrap());
    let n1 = BehaviorGraphNode::from_state(&s1, 0);

    let info = graph.try_get_node_info(&n1).unwrap().unwrap();
    assert_eq!(info.parent, Some(n0));
    assert_eq!(info.depth, 1);

    graph
        .update_node_info(&n0, |info| {
            info.state_check_mask = crate::liveness::checker::CheckMask::from_u64(1);
        })
        .unwrap();

    let n0_info = graph.try_get_node_info(&n0).unwrap().unwrap();
    assert!(n0_info.state_check_mask.get(0));

    let trace = graph.reconstruct_fingerprint_trace(n1).unwrap();
    assert_eq!(trace, vec![(s0.fingerprint(), 0), (s1.fingerprint(), 0)]);
}
