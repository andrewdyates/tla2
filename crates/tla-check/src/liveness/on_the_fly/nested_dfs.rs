// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(dead_code)]

//! Nested DFS (NDFS) for accepting cycle detection in Buchi automata.
//!
//! Implements the classic Courcoubetis-Vardi-Wolper-Yannakakis algorithm
//! for detecting accepting cycles in the product automaton on-the-fly.
//!
//! # Algorithm
//!
//! The algorithm uses two interleaved DFS passes:
//!
//! 1. **Outer DFS (blue):** Explores the product graph depth-first. When
//!    backtracking from an **accepting** state `s`, launches the inner DFS.
//!
//! 2. **Inner DFS (red):** Searches for a path from `s` back to `s`
//!    through the product graph. If such a path is found, an accepting
//!    cycle exists (the blue path from root to `s` is the prefix; the red
//!    path from `s` back to `s` is the cycle).
//!
//! The key insight is that if a state is accepting and reachable from
//! itself, then there is an accepting cycle through it.
//!
//! # Complexity
//!
//! - Time: O(|V| + |E|) where V = product nodes, E = product edges
//! - Space: O(|V|) for the two color sets (blue_visited, red_visited)
//!
//! This is optimal for single-threaded cycle detection. For parallel
//! variants, see CNDFS (Evangelista et al., 2012) or SWARM verification.
//!
//! # References
//!
//! - Courcoubetis, C., Vardi, M. Y., Wolper, P. & Yannakakis, M. (1992).
//!   "Memory-efficient algorithms for the verification of temporal properties."
//!   Formal Methods in System Design, 1(2-3), 275-288.
//! - Holzmann, G. J., Peled, D. & Yannakakis, M. (1996).
//!   "On nested depth first search." The Spin Verification System.

use super::product::{CycleDetectionResult, ProductGraph, ProductNode};
use rustc_hash::FxHashSet;

/// Run the nested DFS algorithm on the product graph.
///
/// `initial_nodes` are the starting points for the outer DFS.
/// `is_accepting` is a predicate that returns `true` for accepting
/// product nodes (those whose Buchi component is an accepting state).
///
/// Returns the first accepting cycle found, or `NoCycle` if the
/// product graph has no accepting cycles reachable from initial nodes.
pub(crate) fn nested_dfs<F>(
    graph: &ProductGraph,
    initial_nodes: &[ProductNode],
    is_accepting: F,
) -> CycleDetectionResult
where
    F: Fn(&ProductNode) -> bool,
{
    let mut blue_visited: FxHashSet<ProductNode> = FxHashSet::default();
    let mut red_visited: FxHashSet<ProductNode> = FxHashSet::default();

    for &init in initial_nodes {
        if blue_visited.contains(&init) {
            continue;
        }

        if let Some(cycle) = outer_dfs(
            graph,
            init,
            &is_accepting,
            &mut blue_visited,
            &mut red_visited,
        ) {
            return CycleDetectionResult::AcceptingCycle { cycle };
        }
    }

    CycleDetectionResult::NoCycle
}

/// Outer DFS (blue pass): explore the product graph depth-first.
///
/// Uses an explicit stack to avoid recursion depth issues on large
/// product graphs. When backtracking from an accepting state, launches
/// the inner DFS to search for a cycle back to that state.
///
/// Returns `Some(cycle)` if an accepting cycle is found.
fn outer_dfs<F>(
    graph: &ProductGraph,
    start: ProductNode,
    is_accepting: &F,
    blue_visited: &mut FxHashSet<ProductNode>,
    red_visited: &mut FxHashSet<ProductNode>,
) -> Option<Vec<ProductNode>>
where
    F: Fn(&ProductNode) -> bool,
{
    // Explicit stack: (node, successor_index, is_postorder_visit).
    // When is_postorder_visit is true, we're backtracking from this node.
    let mut stack: Vec<(ProductNode, usize)> = Vec::new();
    let mut path: Vec<ProductNode> = Vec::new();

    blue_visited.insert(start);
    stack.push((start, 0));
    path.push(start);

    while let Some((node, succ_idx)) = stack.last_mut() {
        let node = *node;
        let successors = graph.get_successors(&node);

        if *succ_idx < successors.len() {
            let succ = successors[*succ_idx];
            *succ_idx += 1;

            if !blue_visited.contains(&succ) {
                blue_visited.insert(succ);
                stack.push((succ, 0));
                path.push(succ);
            }
        } else {
            // Backtracking from this node.
            // If this is an accepting state, run the inner DFS.
            if is_accepting(&node) {
                if let Some(cycle) = inner_dfs(graph, node, &path, red_visited) {
                    return Some(cycle);
                }
            }

            stack.pop();
            path.pop();
        }
    }

    None
}

/// Inner DFS (red pass): search for a path from `seed` back to `seed`.
///
/// The `seed` is an accepting state found during the outer DFS. If we
/// can reach `seed` again from itself, then there exists an accepting
/// cycle (any infinite path through this cycle visits `seed` infinitely
/// often, satisfying the Buchi acceptance condition).
///
/// `blue_path` is the current outer DFS path, used for constructing
/// the full counterexample trace (prefix + cycle).
///
/// Returns `Some(cycle_nodes)` if a cycle through `seed` is found.
fn inner_dfs(
    graph: &ProductGraph,
    seed: ProductNode,
    blue_path: &[ProductNode],
    red_visited: &mut FxHashSet<ProductNode>,
) -> Option<Vec<ProductNode>> {
    let mut stack: Vec<(ProductNode, usize)> = Vec::new();
    let mut red_path: Vec<ProductNode> = Vec::new();

    red_visited.insert(seed);
    stack.push((seed, 0));
    red_path.push(seed);

    while let Some((node, succ_idx)) = stack.last_mut() {
        let node = *node;
        let successors = graph.get_successors(&node);

        if *succ_idx < successors.len() {
            let succ = successors[*succ_idx];
            *succ_idx += 1;

            if succ == seed {
                // Found a cycle back to the seed!
                // Construct the full counterexample:
                // - prefix: blue path from initial state to seed
                // - cycle: red path from seed back to seed
                red_path.push(succ);
                return Some(build_counterexample(blue_path, seed, &red_path));
            }

            if !red_visited.contains(&succ) {
                red_visited.insert(succ);
                stack.push((succ, 0));
                red_path.push(succ);
            }
        } else {
            stack.pop();
            red_path.pop();
        }
    }

    None
}

/// Build a counterexample trace from the blue (prefix) and red (cycle) paths.
///
/// The counterexample consists of:
/// 1. **Prefix:** The portion of the blue path from the initial state to the
///    seed (accepting state where the cycle was found).
/// 2. **Cycle:** The red path from the seed back to itself.
///
/// The returned vector contains the full cycle (seed ... -> seed).
fn build_counterexample(
    blue_path: &[ProductNode],
    seed: ProductNode,
    red_path: &[ProductNode],
) -> Vec<ProductNode> {
    // Find the seed in the blue path to extract the prefix.
    let seed_pos = blue_path.iter().position(|n| *n == seed);

    let mut trace = Vec::new();

    // Add the prefix (blue path up to and including the seed).
    if let Some(pos) = seed_pos {
        trace.extend_from_slice(&blue_path[..=pos]);
    } else {
        // Seed not found in blue path (shouldn't happen in correct NDFS),
        // but handle gracefully by just using the cycle.
        trace.push(seed);
    }

    // Add the cycle (red path, skipping the first element which is the seed
    // already at the end of the prefix).
    if red_path.len() > 1 {
        trace.extend_from_slice(&red_path[1..]);
    }

    trace
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::liveness::on_the_fly::product::{product_node, BuchiState};
    use crate::state::Fingerprint;

    #[test]
    fn test_ndfs_empty_graph() {
        let graph = ProductGraph::new();
        let result = nested_dfs(&graph, &[], |_| true);
        assert!(matches!(result, CycleDetectionResult::NoCycle));
    }

    #[test]
    fn test_ndfs_single_accepting_self_loop() {
        let mut graph = ProductGraph::new();
        let a = product_node(Fingerprint(1), BuchiState(0));
        graph.add_edge(a, a);

        let result = nested_dfs(&graph, &[a], |n| n.tableau_idx == 0);

        match result {
            CycleDetectionResult::AcceptingCycle { cycle } => {
                assert!(
                    cycle.len() >= 2,
                    "cycle should contain at least seed + back-edge: got {:?}",
                    cycle
                );
            }
            CycleDetectionResult::NoCycle => {
                panic!("self-loop on accepting state should be detected")
            }
        }
    }

    #[test]
    fn test_ndfs_two_node_accepting_cycle() {
        let mut graph = ProductGraph::new();
        let a = product_node(Fingerprint(1), BuchiState(0));
        let b = product_node(Fingerprint(2), BuchiState(0));

        graph.add_edge(a, b);
        graph.add_edge(b, a);

        // Both nodes accepting: cycle should be found
        let result = nested_dfs(&graph, &[a], |_| true);
        match result {
            CycleDetectionResult::AcceptingCycle { cycle } => {
                assert!(cycle.len() >= 2);
            }
            CycleDetectionResult::NoCycle => {
                panic!("two-node cycle with accepting states should be detected")
            }
        }
    }

    #[test]
    fn test_ndfs_cycle_with_non_accepting_only() {
        let mut graph = ProductGraph::new();
        let a = product_node(Fingerprint(1), BuchiState(0));
        let b = product_node(Fingerprint(2), BuchiState(1));

        graph.add_edge(a, b);
        graph.add_edge(b, a);

        // Only state 1 is "accepting" in Buchi sense, but b has buchi=1
        // so if we only accept buchi=2, no accepting cycle
        let result = nested_dfs(&graph, &[a], |n| n.tableau_idx == 2);
        assert!(matches!(result, CycleDetectionResult::NoCycle));
    }

    #[test]
    fn test_ndfs_chain_no_cycle() {
        let mut graph = ProductGraph::new();
        let a = product_node(Fingerprint(1), BuchiState(0));
        let b = product_node(Fingerprint(2), BuchiState(0));
        let c = product_node(Fingerprint(3), BuchiState(0));

        graph.add_edge(a, b);
        graph.add_edge(b, c);

        let result = nested_dfs(&graph, &[a], |_| true);
        assert!(matches!(result, CycleDetectionResult::NoCycle));
    }

    #[test]
    fn test_ndfs_accepting_state_not_in_cycle() {
        // a -> b -> c -> b (cycle), a is accepting but not in the cycle
        let mut graph = ProductGraph::new();
        let a = product_node(Fingerprint(1), BuchiState(0));
        let b = product_node(Fingerprint(2), BuchiState(1));
        let c = product_node(Fingerprint(3), BuchiState(1));

        graph.add_edge(a, b);
        graph.add_edge(b, c);
        graph.add_edge(c, b);

        // Only buchi=0 is accepting (only a), but a is not in the cycle b<->c
        let result = nested_dfs(&graph, &[a], |n| n.tableau_idx == 0);
        assert!(matches!(result, CycleDetectionResult::NoCycle));
    }

    #[test]
    fn test_ndfs_multiple_sccs_finds_accepting() {
        // Two SCCs: {a,b} and {c,d}. Only c is accepting.
        let mut graph = ProductGraph::new();
        let a = product_node(Fingerprint(1), BuchiState(0));
        let b = product_node(Fingerprint(2), BuchiState(0));
        let c = product_node(Fingerprint(3), BuchiState(1));
        let d = product_node(Fingerprint(4), BuchiState(0));

        // SCC 1: a <-> b
        graph.add_edge(a, b);
        graph.add_edge(b, a);
        // Bridge: b -> c
        graph.add_edge(b, c);
        // SCC 2: c <-> d
        graph.add_edge(c, d);
        graph.add_edge(d, c);

        // Only buchi=1 (c) is accepting
        let result = nested_dfs(&graph, &[a], |n| n.tableau_idx == 1);
        match result {
            CycleDetectionResult::AcceptingCycle { cycle } => {
                // The cycle should involve c
                assert!(
                    cycle.iter().any(|n| *n == c),
                    "cycle should contain the accepting node c"
                );
            }
            CycleDetectionResult::NoCycle => {
                panic!("should find accepting cycle through c<->d")
            }
        }
    }

    #[test]
    fn test_ndfs_counterexample_includes_prefix() {
        // Linear prefix a -> b -> c, then cycle c -> d -> c
        // c is accepting
        let mut graph = ProductGraph::new();
        let a = product_node(Fingerprint(1), BuchiState(0));
        let b = product_node(Fingerprint(2), BuchiState(0));
        let c = product_node(Fingerprint(3), BuchiState(1));
        let d = product_node(Fingerprint(4), BuchiState(0));

        graph.add_edge(a, b);
        graph.add_edge(b, c);
        graph.add_edge(c, d);
        graph.add_edge(d, c);

        let result = nested_dfs(&graph, &[a], |n| n.tableau_idx == 1);
        match result {
            CycleDetectionResult::AcceptingCycle { cycle } => {
                // The trace should start from initial and include the cycle
                assert!(
                    cycle.first() == Some(&a),
                    "counterexample should start from initial state a"
                );
                assert!(
                    cycle.contains(&c),
                    "counterexample should include the accepting node c"
                );
            }
            CycleDetectionResult::NoCycle => {
                panic!("should find accepting cycle through c<->d")
            }
        }
    }
}
