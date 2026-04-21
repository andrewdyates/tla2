// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tarjan's SCC algorithm for graph analysis.
//!
//! Provides a generic implementation parameterized by edge type, used by both
//! the reachability graph (liveness examination) and the Buchi product graph
//! (LTL model checking).

use crate::explorer::ReachabilityGraph;

/// Compute all strongly connected components using Tarjan's algorithm.
///
/// Generic over edge type `E`. The `successor` closure extracts the destination
/// node ID from an edge. Returns SCCs in reverse topological order (bottom SCCs
/// appear first). Each SCC is a vector of state IDs.
#[must_use]
pub(crate) fn tarjan_scc_generic<E>(
    adj: &[Vec<E>],
    successor: impl Fn(&E) -> u32,
) -> Vec<Vec<u32>> {
    let n = adj.len();
    let mut ctx = TarjanCtx {
        index_counter: 0,
        stack: Vec::new(),
        on_stack: vec![false; n],
        index: vec![u32::MAX; n],
        lowlink: vec![0; n],
        sccs: Vec::new(),
    };

    for v in 0..n {
        if ctx.index[v] == u32::MAX {
            strongconnect(&mut ctx, adj, &successor, v as u32);
        }
    }

    ctx.sccs
}

/// Convenience wrapper for reachability graphs with `(successor, transition_id)` edges.
#[must_use]
pub(crate) fn tarjan_scc(graph: &ReachabilityGraph) -> Vec<Vec<u32>> {
    tarjan_scc_generic(&graph.adj, |&(w, _)| w)
}

struct TarjanCtx {
    index_counter: u32,
    stack: Vec<u32>,
    on_stack: Vec<bool>,
    index: Vec<u32>,
    lowlink: Vec<u32>,
    sccs: Vec<Vec<u32>>,
}

fn strongconnect<E>(ctx: &mut TarjanCtx, adj: &[Vec<E>], successor: &impl Fn(&E) -> u32, v: u32) {
    // Iterative Tarjan's to avoid stack overflow on large graphs.
    let mut call_stack: Vec<(u32, usize)> = Vec::new();

    // Initialize v
    let vi = v as usize;
    ctx.index[vi] = ctx.index_counter;
    ctx.lowlink[vi] = ctx.index_counter;
    ctx.index_counter += 1;
    ctx.stack.push(v);
    ctx.on_stack[vi] = true;

    call_stack.push((v, 0));

    while let Some(&mut (node, ref mut edge_idx)) = call_stack.last_mut() {
        let ni = node as usize;
        if *edge_idx < adj[ni].len() {
            let w = successor(&adj[ni][*edge_idx]);
            *edge_idx += 1;
            let wi = w as usize;

            if ctx.index[wi] == u32::MAX {
                // Not yet visited — recurse
                ctx.index[wi] = ctx.index_counter;
                ctx.lowlink[wi] = ctx.index_counter;
                ctx.index_counter += 1;
                ctx.stack.push(w);
                ctx.on_stack[wi] = true;
                call_stack.push((w, 0));
            } else if ctx.on_stack[wi] {
                ctx.lowlink[ni] = ctx.lowlink[ni].min(ctx.index[wi]);
            }
        } else {
            // All edges processed — check if root of SCC
            if ctx.lowlink[ni] == ctx.index[ni] {
                let mut scc = Vec::new();
                loop {
                    let w = ctx.stack.pop().expect("SCC stack underflow");
                    ctx.on_stack[w as usize] = false;
                    scc.push(w);
                    if w == node {
                        break;
                    }
                }
                ctx.sccs.push(scc);
            }

            let (finished_node, _) = call_stack
                .pop()
                .expect("invariant: call_stack non-empty in DFS pop");

            // Propagate lowlink to parent
            if let Some(&mut (parent, _)) = call_stack.last_mut() {
                let pi = parent as usize;
                let fi = finished_node as usize;
                ctx.lowlink[pi] = ctx.lowlink[pi].min(ctx.lowlink[fi]);
            }
        }
    }
}

/// Identify which SCCs are bottom SCCs (no outgoing edges to other SCCs).
///
/// Returns indices into the `sccs` slice for the bottom components.
#[must_use]
pub(crate) fn bottom_sccs(adj: &[Vec<(u32, u32)>], sccs: &[Vec<u32>]) -> Vec<usize> {
    let max_state = adj.len();
    let mut scc_of = vec![0usize; max_state];
    for (scc_idx, scc) in sccs.iter().enumerate() {
        for &state in scc {
            scc_of[state as usize] = scc_idx;
        }
    }

    let mut result = Vec::new();
    for (scc_idx, scc) in sccs.iter().enumerate() {
        let is_bottom = scc.iter().all(|&state| {
            adj[state as usize]
                .iter()
                .all(|&(succ, _)| scc_of[succ as usize] == scc_idx)
        });
        if is_bottom {
            result.push(scc_idx);
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_graph(adj: Vec<Vec<(u32, u32)>>) -> ReachabilityGraph {
        let n = adj.len() as u32;
        ReachabilityGraph {
            adj,
            num_states: n,
            completed: true,
        }
    }

    #[test]
    fn test_single_node_no_edges() {
        let graph = make_graph(vec![vec![]]);
        let sccs = tarjan_scc(&graph);
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0], vec![0]);

        let bottoms = bottom_sccs(&graph.adj, &sccs);
        assert_eq!(bottoms.len(), 1);
    }

    #[test]
    fn test_simple_cycle() {
        // 0 → 1 → 2 → 0 (single SCC)
        let graph = make_graph(vec![vec![(1, 0)], vec![(2, 0)], vec![(0, 0)]]);
        let sccs = tarjan_scc(&graph);
        assert_eq!(sccs.len(), 1);
        assert_eq!(sccs[0].len(), 3);

        let bottoms = bottom_sccs(&graph.adj, &sccs);
        assert_eq!(bottoms.len(), 1);
    }

    #[test]
    fn test_chain_to_cycle() {
        // 0 → 1 → 2 → 3 → 2
        let graph = make_graph(vec![vec![(1, 0)], vec![(2, 0)], vec![(3, 0)], vec![(2, 0)]]);
        let sccs = tarjan_scc(&graph);
        assert_eq!(sccs.len(), 3);

        let bottoms = bottom_sccs(&graph.adj, &sccs);
        assert_eq!(bottoms.len(), 1);
        let bottom_scc = &sccs[bottoms[0]];
        assert_eq!(bottom_scc.len(), 2);
        assert!(bottom_scc.contains(&2));
        assert!(bottom_scc.contains(&3));
    }

    #[test]
    fn test_two_bottom_sccs() {
        // 0 → 1, 0 → 2 (three singleton SCCs, two bottoms: {1}, {2})
        let graph = make_graph(vec![vec![(1, 0), (2, 0)], vec![], vec![]]);
        let sccs = tarjan_scc(&graph);
        assert_eq!(sccs.len(), 3);

        let bottoms = bottom_sccs(&graph.adj, &sccs);
        assert_eq!(bottoms.len(), 2);
    }

    #[test]
    fn test_deadlock_is_bottom_scc() {
        // 0 → 1, 1 has no outgoing edges (deadlock sink)
        let graph = make_graph(vec![vec![(1, 0)], vec![]]);
        let sccs = tarjan_scc(&graph);
        assert_eq!(sccs.len(), 2);

        let bottoms = bottom_sccs(&graph.adj, &sccs);
        assert_eq!(bottoms.len(), 1);
        let bottom_scc = &sccs[bottoms[0]];
        assert_eq!(bottom_scc, &[1]);
    }
}
