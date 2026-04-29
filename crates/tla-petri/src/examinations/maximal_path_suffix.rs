// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Maximal-path suffix analysis for shallow CTL `AF/EG` routing.
//!
//! Answers the question: does there exist a maximal path from the initial
//! state that stays entirely within a predicate region?
//!
//! Under MCC maximal-path semantics:
//! - `EG(atom)` = `exists_maximal_path_within(graph, sat)`
//! - `AF(atom)` = `!exists_maximal_path_within(graph, not_sat)`

use std::collections::VecDeque;

use crate::explorer::ReachabilityGraph;
use crate::scc::tarjan_scc_generic;

/// Returns true iff there exists a maximal path from the initial state (0)
/// that stays entirely within `allowed`.
///
/// A maximal path either reaches a full-graph deadlock or loops forever.
/// Induced-subgraph sinks (states with no `allowed` successor but with
/// full-graph successors) are NOT deadlocks and do NOT witness `EG`.
pub(crate) fn exists_maximal_path_within(graph: &ReachabilityGraph, allowed: &[bool]) -> bool {
    if graph.num_states == 0 || !allowed[0] {
        return false;
    }

    // Forward BFS from state 0 following only edges to allowed successors.
    let n = graph.num_states as usize;
    let mut visited = vec![false; n];
    visited[0] = true;
    let mut queue = VecDeque::new();
    queue.push_back(0u32);

    // Induced subgraph adjacency (only allowed→allowed edges).
    let mut induced_adj: Vec<Vec<u32>> = vec![Vec::new(); n];

    while let Some(v) = queue.pop_front() {
        let vi = v as usize;
        // A full-graph deadlock is a state with no outgoing edges at all.
        if graph.adj[vi].is_empty() {
            return true;
        }

        for &(w, _) in &graph.adj[vi] {
            let wi = w as usize;
            if wi < allowed.len() && allowed[wi] {
                induced_adj[vi].push(w);
                if !visited[wi] {
                    visited[wi] = true;
                    queue.push_back(w);
                }
            }
        }
    }

    // No deadlock found in the allowed-reachable region.
    // Check for cycles in the induced subgraph among visited states.
    // Build a compact adjacency for only the visited states.
    let visited_states: Vec<u32> = (0..n as u32).filter(|&s| visited[s as usize]).collect();
    if visited_states.is_empty() {
        return false;
    }

    // Map original state IDs to compact IDs for Tarjan.
    let mut compact_id = vec![u32::MAX; n];
    for (i, &s) in visited_states.iter().enumerate() {
        compact_id[s as usize] = i as u32;
    }

    let compact_adj: Vec<Vec<u32>> = visited_states
        .iter()
        .map(|&s| {
            induced_adj[s as usize]
                .iter()
                .filter_map(|&w| {
                    let cid = compact_id[w as usize];
                    if cid != u32::MAX {
                        Some(cid)
                    } else {
                        None
                    }
                })
                .collect()
        })
        .collect();

    let sccs = tarjan_scc_generic(&compact_adj, |&w| w);

    // A cyclic SCC witnesses an infinite path within `allowed`.
    for scc in &sccs {
        if scc.len() > 1 {
            return true;
        }
        if scc.len() == 1 {
            let v = scc[0];
            // Self-loop check.
            if compact_adj[v as usize].contains(&v) {
                return true;
            }
        }
    }

    // No deadlock and no cycle — induced-subgraph sinks have full-graph
    // exits, so the path must leave `allowed`. No witness exists.
    false
}

/// Shallow CTL `EG(atom)`: TRUE iff some maximal path from state 0 stays
/// within `sat` forever.
pub(crate) fn eg_holds_from_mask(graph: &ReachabilityGraph, sat: &[bool]) -> bool {
    exists_maximal_path_within(graph, sat)
}

/// Shallow CTL `AF(atom)`: TRUE iff every maximal path from state 0
/// eventually reaches a state satisfying `sat`.
///
/// Equivalently: no maximal path can stay within `!sat` forever.
pub(crate) fn af_holds_from_mask(graph: &ReachabilityGraph, sat: &[bool]) -> bool {
    let not_sat: Vec<bool> = sat.iter().map(|&b| !b).collect();
    !exists_maximal_path_within(graph, &not_sat)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_graph(num_states: u32, edges: &[(u32, u32)]) -> ReachabilityGraph {
        let mut adj = vec![Vec::new(); num_states as usize];
        for &(from, to) in edges {
            // Transition ID doesn't matter for suffix analysis, use 0.
            adj[from as usize].push((to, 0));
        }
        ReachabilityGraph {
            adj,
            num_states,
            completed: true,
        }
    }

    #[test]
    fn test_eg_single_deadlock_state_true() {
        // Single state, atom=true, no outgoing edges → deadlock witness.
        let graph = make_graph(1, &[]);
        let sat = vec![true];
        assert!(eg_holds_from_mask(&graph, &sat));
    }

    #[test]
    fn test_eg_single_state_not_sat_false() {
        let graph = make_graph(1, &[]);
        let sat = vec![false];
        assert!(!eg_holds_from_mask(&graph, &sat));
    }

    #[test]
    fn test_eg_induced_sink_not_deadlock() {
        // 0(atom) -> 1(atom) -> 2(!atom)
        // State 1 has no atom-successor but is NOT a deadlock (has exit to 2).
        // EG(atom) must be FALSE.
        let graph = make_graph(3, &[(0, 1), (1, 2)]);
        let sat = vec![true, true, false];
        assert!(!eg_holds_from_mask(&graph, &sat));
    }

    #[test]
    fn test_eg_non_bottom_cycle_witnesses() {
        // 0(atom) -> 1(atom), 1(atom) -> 1(atom) self-loop, 1 -> 2(!atom)
        // The existential path can stay on the self-loop forever.
        // EG(atom) must be TRUE.
        let graph = make_graph(3, &[(0, 1), (1, 1), (1, 2)]);
        let sat = vec![true, true, false];
        assert!(eg_holds_from_mask(&graph, &sat));
    }

    #[test]
    fn test_af_false_on_not_atom_cycle() {
        // 0(!atom) -> 0(!atom) self-loop, 0 -> 1(atom)
        // There is a maximal path (looping at 0) that never reaches atom.
        // AF(atom) must be FALSE.
        let graph = make_graph(2, &[(0, 0), (0, 1)]);
        let sat = vec![false, true];
        assert!(!af_holds_from_mask(&graph, &sat));
    }

    #[test]
    fn test_af_true_when_all_paths_reach_atom() {
        // 0(!atom) -> 1(atom), no cycles in !atom region.
        // Every maximal path from 0 must pass through 1.
        // AF(atom) = TRUE.
        let graph = make_graph(2, &[(0, 1)]);
        let sat = vec![false, true];
        assert!(af_holds_from_mask(&graph, &sat));
    }

    #[test]
    fn test_eg_multi_state_cycle() {
        // 0(atom) -> 1(atom) -> 2(atom) -> 0(atom), cycle of length 3.
        let graph = make_graph(3, &[(0, 1), (1, 2), (2, 0)]);
        let sat = vec![true, true, true];
        assert!(eg_holds_from_mask(&graph, &sat));
    }

    #[test]
    fn test_eg_initial_not_allowed_false() {
        // Initial state doesn't satisfy atom → immediate FALSE.
        let graph = make_graph(2, &[(0, 1)]);
        let sat = vec![false, true];
        assert!(!eg_holds_from_mask(&graph, &sat));
    }

    #[test]
    fn test_af_true_on_deadlock_satisfying_atom() {
        // 0(atom) deadlock. AF(atom) = TRUE because the only maximal path
        // is [0] and it already satisfies atom.
        let graph = make_graph(1, &[]);
        let sat = vec![true];
        assert!(af_holds_from_mask(&graph, &sat));
    }

    #[test]
    fn test_af_false_on_deadlock_not_satisfying_atom() {
        // 0(!atom) deadlock. AF(atom) = FALSE because the maximal path [0]
        // never reaches atom.
        let graph = make_graph(1, &[]);
        let sat = vec![false];
        assert!(!af_holds_from_mask(&graph, &sat));
    }

    #[test]
    fn test_eg_unreachable_cycle_not_counted() {
        // 0(atom) -> 1(!atom), 2(atom) -> 2(atom) self-loop.
        // State 2 is unreachable from 0 within atom — should not count.
        let graph = make_graph(3, &[(0, 1), (2, 2)]);
        let sat = vec![true, false, true];
        assert!(!eg_holds_from_mask(&graph, &sat));
    }
}
