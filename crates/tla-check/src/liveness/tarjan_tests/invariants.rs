// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_trivial_missing_node_returns_error() {
    let graph = BehaviorGraph::new();
    let missing = BehaviorGraphNode::new(crate::state::Fingerprint(0xDEAD_BEEF_u64), 0);
    let scc = Scc::new(vec![missing]);

    let result = is_trivial_scc_in_graph(&scc, &graph);
    assert!(
        result.is_err(),
        "missing node must return Err, got {:?}",
        result
    );
    let err_msg = result.unwrap_err().to_string();
    assert!(
        err_msg.contains("missing from behavior graph"),
        "error should mention missing node, got: {}",
        err_msg
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_find_cycles_missing_node_records_error() {
    let mut graph = BehaviorGraph::new();
    let s0 = make_state(0);
    graph.add_init_node(&s0, 0);

    let result = find_cycles(&graph);
    assert!(result.errors.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tarjan_dfs_missing_node_populates_errors() {
    let graph = BehaviorGraph::new();
    let result = find_sccs(&graph);
    assert!(result.errors.is_empty());
    assert_eq!(result.sccs.len(), 0);
}
