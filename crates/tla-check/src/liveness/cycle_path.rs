// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! BFS-based cycle path extraction within an SCC.
//!
//! Given an SCC (from Tarjan's algorithm), finds a concrete cycle path
//! for counterexample construction. This is a separate algorithm (BFS)
//! from SCC detection (DFS Tarjan).

#[cfg(test)]
use super::behavior_graph::{BehaviorGraph, BehaviorGraphNode};
#[cfg(test)]
use super::scc::Scc;
#[cfg(test)]
use rustc_hash::{FxHashMap, FxHashSet};
#[cfg(test)]
use tla_value::error::{EvalError, EvalResult};

/// Find a cycle within an SCC for counterexample construction.
///
/// Returns `Ok(Some(path))` if a cycle is found, `Ok(None)` if no cycle
/// exists (e.g., empty SCC), or `Err` if a node in the SCC is missing
/// from the graph (invariant violation).
#[cfg(test)]
pub(crate) fn find_cycle_in_scc(
    graph: &BehaviorGraph,
    scc: &Scc,
) -> EvalResult<Option<Vec<BehaviorGraphNode>>> {
    if scc.len() < 2 {
        // Check for self-loop on single node
        if scc.len() == 1 {
            let node = scc.nodes()[0];
            let info = graph
                .get_node_info(&node)
                .ok_or_else(|| EvalError::Internal {
                    message: format!(
                        "find_cycle_in_scc: SCC node {:?} missing from behavior graph",
                        node
                    ),
                    span: None,
                })?;
            if info.successors.contains(&node) {
                return Ok(Some(vec![node, node]));
            }
        }
        return Ok(None);
    }

    // Build set of SCC nodes for fast lookup
    let scc_set = scc.build_node_set();

    // Use BFS to find a cycle within the SCC
    // Start from first node, find path back to it
    let start = scc.nodes()[0];

    // BFS to find path back to start
    let mut visited: FxHashSet<BehaviorGraphNode> = FxHashSet::default();
    let mut parent: FxHashMap<BehaviorGraphNode, BehaviorGraphNode> = FxHashMap::default();
    let mut queue = std::collections::VecDeque::new();

    // Start from successors of start node
    let start_info = graph
        .get_node_info(&start)
        .ok_or_else(|| EvalError::Internal {
            message: format!(
                "find_cycle_in_scc: start node {:?} missing from behavior graph",
                start
            ),
            span: None,
        })?;
    for succ in &start_info.successors {
        if scc_set.contains(succ) {
            visited.insert(*succ);
            parent.insert(*succ, start);
            queue.push_back(*succ);
        }
    }

    while let Some(current) = queue.pop_front() {
        if current == start {
            // Found cycle! Reconstruct path by following parents back from current
            let mut path = Vec::new();
            let mut node = current;

            // Walk back through parents until we reach start
            while let Some(&p) = parent.get(&node) {
                path.push(node);
                node = p;
                if node == start {
                    break;
                }
            }
            path.push(start);

            // Reverse to get forward direction: start -> ... -> start
            path.reverse();
            return Ok(Some(path));
        }

        if let Some(info) = graph.get_node_info(&current) {
            for succ in &info.successors {
                if scc_set.contains(succ) && !visited.contains(succ) {
                    visited.insert(*succ);
                    parent.insert(*succ, current);
                    queue.push_back(*succ);
                }
            }
        }
        // Note: missing intermediate nodes during BFS are non-fatal — we
        // simply don't expand them. Only the start node is required.
    }

    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::liveness::tarjan::find_cycles;
    use crate::liveness::test_helpers::make_state;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_find_cycle_in_scc() {
        let mut graph = BehaviorGraph::new();
        let s0 = make_state(0);
        let s1 = make_state(1);
        let s2 = make_state(2);

        graph.add_init_node(&s0, 0);
        let n0 = BehaviorGraphNode::from_state(&s0, 0);

        graph.add_successor(n0, &s1, 0).unwrap();
        let n1 = BehaviorGraphNode::from_state(&s1, 0);

        graph.add_successor(n1, &s2, 0).unwrap();
        let n2 = BehaviorGraphNode::from_state(&s2, 0);

        graph.add_successor(n2, &s0, 0).unwrap();

        let cycles = find_cycles(&graph);
        assert!(cycles.errors.is_empty());
        assert_eq!(cycles.sccs.len(), 1);

        let cycle_path = find_cycle_in_scc(&graph, &cycles.sccs[0]).unwrap();
        assert!(cycle_path.is_some());

        let path = cycle_path.unwrap();
        // Cycle should start and end at same node
        assert_eq!(path.first(), path.last());
        // Path should have at least 2 elements (start and back to start)
        assert!(path.len() >= 2);
    }

    /// Regression test for #1965: find_cycle_in_scc returns Err when the
    /// start node is missing from the graph, distinguishing "no cycle" from
    /// "graph invariant violated".
    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_find_cycle_in_scc_missing_node_returns_error() {
        let graph = BehaviorGraph::new();
        let missing_a = BehaviorGraphNode::new(crate::state::Fingerprint(0xBAAD_F00D_u64), 0);
        let missing_b = BehaviorGraphNode::new(crate::state::Fingerprint(0xFEED_FACE_u64), 0);
        let scc = Scc::new(vec![missing_a, missing_b]);

        let result = find_cycle_in_scc(&graph, &scc);
        assert!(
            result.is_err(),
            "missing start node must return Err, got {:?}",
            result
        );
        let err_msg = result.unwrap_err().to_string();
        assert!(
            err_msg.contains("missing from behavior graph"),
            "error should mention missing node, got: {}",
            err_msg
        );
    }
}
