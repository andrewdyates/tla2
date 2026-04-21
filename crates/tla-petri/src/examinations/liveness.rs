// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MCC Liveness examination via SCC analysis.
//!
//! A transition `t` is L4-live iff from every reachable marking there
//! exists a firing sequence that eventually fires `t`. This is equivalent
//! to: every bottom SCC of the reachability graph contains an internal
//! edge labeled `t`.
//!
//! Reference: Murata, "Petri nets: Properties, analysis and applications", 1989.

use rustc_hash::FxHashSet;

use crate::explorer::ReachabilityGraph;

/// Check if all transitions are L4-live.
///
/// Returns `true` iff every bottom SCC can fire every transition
/// (directly within the SCC's internal edges).
#[must_use]
pub(crate) fn check_liveness(
    graph: &ReachabilityGraph,
    sccs: &[Vec<u32>],
    bottom_indices: &[usize],
    num_transitions: usize,
) -> bool {
    if num_transitions == 0 {
        return true;
    }

    for &scc_idx in bottom_indices {
        let scc = &sccs[scc_idx];
        let scc_states: FxHashSet<u32> = scc.iter().copied().collect();
        let mut fireable: FxHashSet<u32> = FxHashSet::default();

        for &state in scc {
            for &(succ, trans) in &graph.adj[state as usize] {
                if scc_states.contains(&succ) {
                    fireable.insert(trans);
                }
            }
        }

        if fireable.len() < num_transitions {
            return false;
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::explorer::ReachabilityGraph;
    use crate::scc::{bottom_sccs, tarjan_scc};

    fn make_graph(adj: Vec<Vec<(u32, u32)>>) -> ReachabilityGraph {
        let n = adj.len() as u32;
        ReachabilityGraph {
            adj,
            num_states: n,
            completed: true,
        }
    }

    #[test]
    fn test_live_circular_net() {
        // Single SCC: 0 -t0-> 1 -t1-> 2 -t2-> 0
        // All 3 transitions fireable within the single bottom SCC → LIVE
        let graph = make_graph(vec![vec![(1, 0)], vec![(2, 1)], vec![(0, 2)]]);
        let sccs = tarjan_scc(&graph);
        let bottoms = bottom_sccs(&graph.adj, &sccs);
        assert!(check_liveness(&graph, &sccs, &bottoms, 3));
    }

    #[test]
    fn test_not_live_deadlock() {
        // 0 -t0-> 1, state 1 is deadlock (bottom SCC = {1}, no fireable transitions)
        let graph = make_graph(vec![vec![(1, 0)], vec![]]);
        let sccs = tarjan_scc(&graph);
        let bottoms = bottom_sccs(&graph.adj, &sccs);
        assert!(!check_liveness(&graph, &sccs, &bottoms, 1));
    }

    #[test]
    fn test_not_live_dead_transition() {
        // 0 -t0-> 1 -t1-> 0 (cycle with t0, t1)
        // plus 0 -t2-> 2 (but t2 only fires once, then stuck in {0,1} cycle)
        // Wait — t2 fires from 0 to 2, but 2 has no outgoing.
        // Bottom SCCs: {2} (deadlock) and {0,1} (cycle).
        // {2} has no fireable transitions → NOT LIVE
        let graph = make_graph(vec![vec![(1, 0), (2, 2)], vec![(0, 1)], vec![]]);
        let sccs = tarjan_scc(&graph);
        let bottoms = bottom_sccs(&graph.adj, &sccs);
        assert!(!check_liveness(&graph, &sccs, &bottoms, 3));
    }

    #[test]
    fn test_live_single_state_self_loop() {
        // State 0 with self-loops on t0 and t1 — single bottom SCC with all transitions
        let graph = make_graph(vec![vec![(0, 0), (0, 1)]]);
        let sccs = tarjan_scc(&graph);
        let bottoms = bottom_sccs(&graph.adj, &sccs);
        assert!(check_liveness(&graph, &sccs, &bottoms, 2));
    }

    #[test]
    fn test_not_live_missing_transition_in_bottom() {
        // Bottom SCC {1,2} with edges using only t0.
        // Transition t1 exists but is only used in the transient part.
        // Bottom SCC can't fire t1 → NOT LIVE
        let graph = make_graph(vec![
            vec![(1, 1)], // 0 -t1-> 1
            vec![(2, 0)], // 1 -t0-> 2
            vec![(1, 0)], // 2 -t0-> 1
        ]);
        let sccs = tarjan_scc(&graph);
        let bottoms = bottom_sccs(&graph.adj, &sccs);
        assert!(!check_liveness(&graph, &sccs, &bottoms, 2));
    }
}
