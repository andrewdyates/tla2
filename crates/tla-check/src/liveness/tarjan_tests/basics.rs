// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_empty_graph() {
    let graph = BehaviorGraph::new();
    let result = find_sccs(&graph);

    assert_eq!(result.sccs.len(), 0);
    assert_eq!(result.stats.nodes_processed, 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_single_node_no_self_loop() {
    let mut graph = BehaviorGraph::new();
    let s0 = make_state(0);
    graph.add_init_node(&s0, 0);

    // Trivial SCCs (single-node, no self-loop) are filtered inline by extract_scc.
    let result = find_sccs(&graph);
    assert_eq!(result.sccs.len(), 0, "trivial SCC should be filtered out");
    assert_eq!(result.stats.nodes_processed, 1);

    let cycles = find_cycles(&graph);
    assert!(
        cycles.errors.is_empty(),
        "Tarjan errors: {:?}",
        cycles.errors
    );
    assert_eq!(cycles.sccs.len(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_single_node_with_self_loop() {
    let mut graph = BehaviorGraph::new();
    let s0 = make_state(0);
    graph.add_init_node(&s0, 0);

    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph
        .add_successor(n0, &s0, 0)
        .expect("self-loop should attach to an existing source node");

    let result = find_sccs(&graph);

    assert_eq!(result.sccs.len(), 1);
    assert_eq!(result.sccs[0].len(), 1);
    assert!(!is_trivial_scc_in_graph(&result.sccs[0], &graph)
        .expect("self-loop SCC should exist in the graph"));

    let cycles = find_cycles(&graph);
    assert!(cycles.errors.is_empty());
    assert_eq!(cycles.sccs.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_two_node_cycle() {
    let mut graph = BehaviorGraph::new();
    let s0 = make_state(0);
    let s1 = make_state(1);

    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);

    graph
        .add_successor(n0, &s1, 0)
        .expect("forward edge should attach to an existing source node");
    let n1 = BehaviorGraphNode::from_state(&s1, 0);
    graph
        .add_successor(n1, &s0, 0)
        .expect("back edge should attach to an existing source node");

    let result = find_sccs(&graph);

    assert_eq!(result.sccs.len(), 1);
    assert_eq!(result.sccs[0].len(), 2);
    assert!(!is_trivial_scc_in_graph(&result.sccs[0], &graph)
        .expect("two-node SCC should exist in the graph"));

    let cycles = find_cycles(&graph);
    assert!(cycles.errors.is_empty());
    assert_eq!(cycles.sccs.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_linear_chain_no_cycle() {
    let mut graph = BehaviorGraph::new();
    let s0 = make_state(0);
    let s1 = make_state(1);
    let s2 = make_state(2);

    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);

    graph
        .add_successor(n0, &s1, 0)
        .expect("chain edge should attach to an existing source node");
    let n1 = BehaviorGraphNode::from_state(&s1, 0);
    graph
        .add_successor(n1, &s2, 0)
        .expect("chain edge should attach to an existing source node");

    // All 3 nodes form trivial SCCs (no self-loops), filtered inline.
    let result = find_sccs(&graph);
    assert_eq!(result.sccs.len(), 0, "trivial SCCs should be filtered out");
    assert_eq!(result.stats.nodes_processed, 3);

    let cycles = find_cycles(&graph);
    assert!(cycles.errors.is_empty());
    assert_eq!(cycles.sccs.len(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_two_separate_cycles() {
    let mut graph = BehaviorGraph::new();

    let s0 = make_state(0);
    let s1 = make_state(1);
    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph
        .add_successor(n0, &s1, 0)
        .expect("cycle edge should attach to an existing source node");
    let n1 = BehaviorGraphNode::from_state(&s1, 0);
    graph
        .add_successor(n1, &s0, 0)
        .expect("cycle edge should attach to an existing source node");

    let s2 = make_state(2);
    let s3 = make_state(3);
    graph.add_init_node(&s2, 1);
    let n2 = BehaviorGraphNode::from_state(&s2, 1);
    graph
        .add_successor(n2, &s3, 1)
        .expect("cycle edge should attach to an existing source node");
    let n3 = BehaviorGraphNode::from_state(&s3, 1);
    graph
        .add_successor(n3, &s2, 1)
        .expect("cycle edge should attach to an existing source node");

    let result = find_sccs(&graph);
    let cycles = find_cycles(&graph);
    assert!(cycles.errors.is_empty());
    assert_eq!(cycles.sccs.len(), 2);
    assert_eq!(result.stats.nontrivial_sccs, 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tableau_differentiation() {
    let mut graph = BehaviorGraph::new();
    let s0 = make_state(0);

    graph.add_init_node(&s0, 0);
    graph.add_init_node(&s0, 1);

    let n0_t0 = BehaviorGraphNode::from_state(&s0, 0);
    let n0_t1 = BehaviorGraphNode::from_state(&s0, 1);

    assert_ne!(n0_t0, n0_t1);

    graph
        .add_successor(n0_t0, &s0, 1)
        .expect("tableau edge should attach to an existing source node");
    graph
        .add_successor(n0_t1, &s0, 0)
        .expect("tableau edge should attach to an existing source node");

    let cycles = find_cycles(&graph);
    assert!(cycles.errors.is_empty());
    assert_eq!(cycles.sccs.len(), 1);
    assert_eq!(cycles.sccs[0].len(), 2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_edge_filter_excludes_back_edge_from_scc() {
    let mut graph = BehaviorGraph::new();
    let s0 = make_state(0);
    let s1 = make_state(1);

    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);
    graph
        .add_successor(n0, &s1, 0)
        .expect("filtered edge should attach to an existing source node");
    let n1 = BehaviorGraphNode::from_state(&s1, 0);
    graph
        .add_successor(n1, &s0, 0)
        .expect("filtered edge should attach to an existing source node");

    let result = find_sccs_with_edge_filter(&graph, &|_from_info, _succ_idx, to| {
        // Exclude the back-edge n1->n0 (the only edge targeting n0)
        *to != n0
    });

    // After excluding the back-edge, both nodes form trivial SCCs
    // (single-node, no self-loop), which are filtered inline.
    assert_eq!(
        result.sccs.len(),
        0,
        "trivial SCCs after edge filter should be filtered out"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_accepting_scc_detection() {
    let mut graph = BehaviorGraph::new();
    let s0 = make_state(0);
    let s1 = make_state(1);

    graph.add_init_node(&s0, 0);
    let n0 = BehaviorGraphNode::from_state(&s0, 0);

    graph
        .add_successor(n0, &s1, 0)
        .expect("accepting-cycle edge should attach to an existing source node");
    let n1 = BehaviorGraphNode::from_state(&s1, 0);
    graph
        .add_successor(n1, &s0, 0)
        .expect("accepting-cycle edge should attach to an existing source node");

    let accepting_sccs = find_accepting_sccs(&graph, |_| true);
    assert!(accepting_sccs.errors.is_empty());
    assert_eq!(accepting_sccs.sccs.len(), 1);

    let accepting_sccs = find_accepting_sccs(&graph, |_| false);
    assert!(accepting_sccs.errors.is_empty());
    assert_eq!(accepting_sccs.sccs.len(), 0);

    let accepting_sccs = find_accepting_sccs(&graph, |n| n.tableau_idx == 0);
    assert!(accepting_sccs.errors.is_empty());
    assert_eq!(accepting_sccs.sccs.len(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_complex_graph() {
    let mut graph = BehaviorGraph::new();
    let states: Vec<State> = (0..6).map(make_state).collect();

    graph.add_init_node(&states[0], 0);
    let n0 = BehaviorGraphNode::from_state(&states[0], 0);

    graph
        .add_successor(n0, &states[1], 0)
        .expect("complex-graph edge should attach to an existing source node");
    let n1 = BehaviorGraphNode::from_state(&states[1], 0);
    graph
        .add_successor(n1, &states[2], 0)
        .expect("complex-graph edge should attach to an existing source node");
    let n2 = BehaviorGraphNode::from_state(&states[2], 0);
    graph
        .add_successor(n2, &states[0], 0)
        .expect("complex-graph edge should attach to an existing source node");

    graph
        .add_successor(n0, &states[3], 0)
        .expect("complex-graph edge should attach to an existing source node");
    graph
        .add_successor(n1, &states[4], 0)
        .expect("complex-graph edge should attach to an existing source node");
    graph
        .add_successor(n2, &states[5], 0)
        .expect("complex-graph edge should attach to an existing source node");

    let n3 = BehaviorGraphNode::from_state(&states[3], 0);
    graph
        .add_successor(n3, &states[4], 0)
        .expect("complex-graph edge should attach to an existing source node");
    let n5 = BehaviorGraphNode::from_state(&states[5], 0);
    graph
        .add_successor(n5, &states[4], 0)
        .expect("complex-graph edge should attach to an existing source node");
    graph
        .add_successor(n5, &states[3], 0)
        .expect("complex-graph edge should attach to an existing source node");
    graph
        .add_successor(n3, &states[5], 0)
        .expect("complex-graph edge should attach to an existing source node");

    let result = find_sccs(&graph);
    let cycles = find_cycles(&graph);
    assert!(cycles.errors.is_empty());
    assert!(
        cycles.sccs.len() >= 2,
        "Expected at least 2 cycles from two distinct cycle structures, got {}",
        cycles.sccs.len()
    );
    assert_eq!(result.stats.nodes_processed, 6);
}
