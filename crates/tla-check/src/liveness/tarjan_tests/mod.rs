// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Tarjan SCC detection.
//!
//! Split from `liveness/tarjan.rs` as part of #2853.

use super::*;
use crate::liveness::test_helpers::make_state;
use crate::state::State;

mod arena_warn_threshold;
mod basics;
mod invariants;
mod properties;

fn build_graph_from_adj(
    n: usize,
    adj: &[bool],
) -> (BehaviorGraph, Vec<State>, Vec<BehaviorGraphNode>) {
    assert_eq!(adj.len(), n * n);

    let mut graph = BehaviorGraph::new();
    let states: Vec<State> = (0..n).map(|i| make_state(i as i64)).collect();

    for state in &states {
        graph.add_init_node(state, 0);
    }

    let nodes: Vec<BehaviorGraphNode> = states
        .iter()
        .map(|state| BehaviorGraphNode::from_state(state, 0))
        .collect();

    for from_idx in 0..n {
        for to_idx in 0..n {
            if adj[from_idx * n + to_idx] {
                graph
                    .add_successor(nodes[from_idx], &states[to_idx], 0)
                    .expect("adjacency builder should add successor from an existing source node");
            }
        }
    }

    (graph, states, nodes)
}

fn canonicalize_sccs(sccs: Vec<Scc>, nodes: &[BehaviorGraphNode]) -> Vec<Vec<usize>> {
    let mut sets: Vec<Vec<usize>> = sccs
        .into_iter()
        .map(|scc| {
            let mut idxs: Vec<usize> = scc
                .nodes()
                .iter()
                .map(|node| {
                    nodes
                        .iter()
                        .position(|n| n == node)
                        .expect("SCC contains node not in graph")
                })
                .collect();
            idxs.sort_unstable();
            idxs
        })
        .collect();
    sets.sort();
    sets
}

fn compute_reachability(n: usize, adj: &[bool]) -> Vec<Vec<bool>> {
    assert_eq!(adj.len(), n * n);

    let mut reach = vec![vec![false; n]; n];
    for start in 0..n {
        let mut queue = std::collections::VecDeque::new();
        let mut visited = vec![false; n];
        visited[start] = true;
        queue.push_back(start);

        while let Some(cur) = queue.pop_front() {
            reach[start][cur] = true;
            for succ in 0..n {
                if adj[cur * n + succ] && !visited[succ] {
                    visited[succ] = true;
                    queue.push_back(succ);
                }
            }
        }
    }
    reach
}

fn reference_sccs(n: usize, adj: &[bool]) -> Vec<Vec<usize>> {
    let reach = compute_reachability(n, adj);

    let mut parent: Vec<usize> = (0..n).collect();
    fn find(parent: &mut [usize], x: usize) -> usize {
        if parent[x] != x {
            let root = find(parent, parent[x]);
            parent[x] = root;
        }
        parent[x]
    }
    fn union(parent: &mut [usize], a: usize, b: usize) {
        let ra = find(parent, a);
        let rb = find(parent, b);
        if ra != rb {
            parent[rb] = ra;
        }
    }

    #[allow(clippy::needless_range_loop)]
    for i in 0..n {
        for j in (i + 1)..n {
            if reach[i][j] && reach[j][i] {
                union(&mut parent, i, j);
            }
        }
    }

    let mut groups: std::collections::BTreeMap<usize, Vec<usize>> =
        std::collections::BTreeMap::new();
    for i in 0..n {
        let root = find(&mut parent, i);
        groups.entry(root).or_default().push(i);
    }

    let mut sets: Vec<Vec<usize>> = groups.into_values().collect();
    for set in &mut sets {
        set.sort_unstable();
    }

    // Filter trivial SCCs: single-node without self-loop.
    // Matches the inline filtering in TarjanFinder::extract_scc.
    sets.retain(|set| {
        if set.len() == 1 {
            let node = set[0];
            adj[node * n + node] // keep only if self-loop exists
        } else {
            true
        }
    });

    sets.sort();
    sets
}
