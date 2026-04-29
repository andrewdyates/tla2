// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use rustc_hash::FxHashMap;
use std::hash::Hash;
use std::sync::Arc;

/// A strongly connected component.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scc<N> {
    nodes: Vec<N>,
}

impl<N> Scc<N> {
    fn new(nodes: Vec<N>) -> Self {
        Self { nodes }
    }

    /// The nodes in this SCC.
    pub fn nodes(&self) -> &[N] {
        &self.nodes
    }

    /// The number of nodes in this SCC.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the SCC is empty.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

/// Result of Tarjan SCC analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TarjanResult<N> {
    /// SCCs in reverse topological order.
    pub sccs: Vec<Scc<N>>,
}

#[derive(Debug, Clone)]
struct NodeState {
    index: usize,
    low_link: usize,
    on_stack: bool,
}

#[derive(Debug)]
enum DfsFrame<N> {
    Visit(N),
    ProcessSuccessor {
        node: N,
        successors: Arc<Vec<N>>,
        succ_idx: usize,
    },
    PostProcess {
        node: N,
        successors: Arc<Vec<N>>,
    },
}

/// Compute strongly connected components using iterative Tarjan DFS.
pub fn tarjan_scc<N, I, F, S>(nodes: I, successors: F) -> TarjanResult<N>
where
    N: Clone + Eq + Hash,
    I: IntoIterator<Item = N>,
    F: Fn(&N) -> S,
    S: IntoIterator<Item = N>,
{
    let mut finder = TarjanFinder::new(successors);
    for node in nodes {
        if !finder.node_states.contains_key(&node) {
            finder.tarjan_iterative(node);
        }
    }
    TarjanResult { sccs: finder.sccs }
}

/// Identify SCCs with no outgoing edges to a different SCC.
pub fn bottom_sccs<N, F, S>(sccs: &[Scc<N>], successors: F) -> Vec<usize>
where
    N: Clone + Eq + Hash,
    F: Fn(&N) -> S,
    S: IntoIterator<Item = N>,
{
    let mut scc_of = FxHashMap::default();
    for (scc_idx, scc) in sccs.iter().enumerate() {
        for node in scc.nodes() {
            scc_of.insert(node.clone(), scc_idx);
        }
    }

    let mut bottoms = Vec::new();
    for (scc_idx, scc) in sccs.iter().enumerate() {
        let is_bottom = scc.nodes().iter().all(|node| {
            successors(node)
                .into_iter()
                .all(|succ| scc_of.get(&succ).copied() == Some(scc_idx))
        });
        if is_bottom {
            bottoms.push(scc_idx);
        }
    }
    bottoms
}

struct TarjanFinder<N, F> {
    successors: F,
    node_states: FxHashMap<N, NodeState>,
    index: usize,
    stack: Vec<N>,
    sccs: Vec<Scc<N>>,
}

impl<N, F, S> TarjanFinder<N, F>
where
    N: Clone + Eq + Hash,
    F: Fn(&N) -> S,
    S: IntoIterator<Item = N>,
{
    fn new(successors: F) -> Self {
        Self {
            successors,
            node_states: FxHashMap::default(),
            index: 0,
            stack: Vec::new(),
            sccs: Vec::new(),
        }
    }

    fn tarjan_iterative(&mut self, start: N) {
        let mut dfs_stack = vec![DfsFrame::Visit(start)];

        while let Some(frame) = dfs_stack.pop() {
            match frame {
                DfsFrame::Visit(node) => self.handle_visit(node, &mut dfs_stack),
                DfsFrame::ProcessSuccessor {
                    node,
                    successors,
                    succ_idx,
                } => self.handle_process_successor(node, successors, succ_idx, &mut dfs_stack),
                DfsFrame::PostProcess { node, successors } => {
                    self.handle_post_process(node, &successors);
                }
            }
        }
    }

    fn handle_visit(&mut self, node: N, dfs_stack: &mut Vec<DfsFrame<N>>) {
        if self.node_states.contains_key(&node) {
            return;
        }

        let node_index = self.index;
        self.index += 1;
        self.node_states.insert(
            node.clone(),
            NodeState {
                index: node_index,
                low_link: node_index,
                on_stack: true,
            },
        );
        self.stack.push(node.clone());

        let successors = Arc::new((self.successors)(&node).into_iter().collect::<Vec<_>>());
        dfs_stack.push(DfsFrame::PostProcess {
            node: node.clone(),
            successors: Arc::clone(&successors),
        });

        if !successors.is_empty() {
            dfs_stack.push(DfsFrame::ProcessSuccessor {
                node,
                successors,
                succ_idx: 0,
            });
        }
    }

    fn handle_process_successor(
        &mut self,
        node: N,
        successors: Arc<Vec<N>>,
        succ_idx: usize,
        dfs_stack: &mut Vec<DfsFrame<N>>,
    ) {
        if succ_idx >= successors.len() {
            return;
        }

        let succ = successors[succ_idx].clone();
        if succ_idx + 1 < successors.len() {
            dfs_stack.push(DfsFrame::ProcessSuccessor {
                node: node.clone(),
                successors: Arc::clone(&successors),
                succ_idx: succ_idx + 1,
            });
        }

        if let Some(succ_state) = self.node_states.get(&succ) {
            if succ_state.on_stack {
                let succ_index = succ_state.index;
                if let Some(node_state) = self.node_states.get_mut(&node) {
                    node_state.low_link = node_state.low_link.min(succ_index);
                }
            }
        } else {
            dfs_stack.push(DfsFrame::Visit(succ));
        }
    }

    fn handle_post_process(&mut self, node: N, successors: &[N]) {
        let mut min_low_link = self
            .node_states
            .get(&node)
            .map_or(usize::MAX, |state| state.low_link);

        for succ in successors {
            if let Some(succ_state) = self.node_states.get(succ) {
                if succ_state.on_stack {
                    min_low_link = min_low_link.min(succ_state.low_link);
                }
            }
        }

        if let Some(node_state) = self.node_states.get_mut(&node) {
            node_state.low_link = min_low_link;
        }

        let Some(state) = self.node_states.get(&node) else {
            return;
        };
        if state.low_link == state.index {
            self.extract_scc(node);
        }
    }

    fn extract_scc(&mut self, root: N) {
        let mut nodes = Vec::new();
        while let Some(node) = self.stack.pop() {
            if let Some(state) = self.node_states.get_mut(&node) {
                state.on_stack = false;
            }
            nodes.push(node.clone());
            if node == root {
                break;
            }
        }
        self.sccs.push(Scc::new(nodes));
    }
}

#[cfg(test)]
mod tests {
    use super::{bottom_sccs, tarjan_scc};

    fn successors(node: &u8) -> Vec<u8> {
        match *node {
            0 => vec![1],
            1 => vec![2],
            2 => vec![3],
            3 => vec![2],
            4 => vec![5, 6],
            5 => Vec::new(),
            6 => Vec::new(),
            7 => vec![7],
            _ => Vec::new(),
        }
    }

    #[test]
    fn tarjan_finds_bottom_cycle() {
        let result = tarjan_scc([0_u8, 1, 2, 3], successors);

        assert_eq!(result.sccs.len(), 3);
        let bottoms = bottom_sccs(&result.sccs, successors);
        assert_eq!(bottoms.len(), 1);

        let bottom = result.sccs[bottoms[0]].nodes();
        assert_eq!(bottom.len(), 2);
        assert!(bottom.contains(&2));
        assert!(bottom.contains(&3));
    }

    #[test]
    fn tarjan_finds_two_bottom_singletons() {
        let result = tarjan_scc([4_u8, 5, 6], successors);

        assert_eq!(result.sccs.len(), 3);
        let bottoms = bottom_sccs(&result.sccs, successors);
        assert_eq!(bottoms.len(), 2);

        let bottom_sets: Vec<&[u8]> = bottoms
            .iter()
            .map(|index| result.sccs[*index].nodes())
            .collect();
        assert!(bottom_sets.iter().any(|nodes| *nodes == [5]));
        assert!(bottom_sets.iter().any(|nodes| *nodes == [6]));
    }

    #[test]
    fn tarjan_treats_self_loop_as_bottom_scc() {
        let result = tarjan_scc([7_u8], successors);

        assert_eq!(result.sccs.len(), 1);
        let bottoms = bottom_sccs(&result.sccs, successors);
        assert_eq!(bottoms, vec![0]);
        assert_eq!(result.sccs[0].nodes(), [7]);
    }
}
