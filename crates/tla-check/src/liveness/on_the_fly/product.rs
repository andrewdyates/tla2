// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(dead_code)]

//! Product state types for on-the-fly LTL model checking.
//!
//! The product automaton is the synchronous product of the TLA+ system
//! state space and the Buchi automaton (NBA) for the negated property.
//! A product state is a pair `(system_state_fingerprint, buchi_state)`.
//!
//! An accepting run in the product automaton corresponds to a system
//! behavior that violates the LTL property.

use crate::liveness::behavior_graph::BehaviorGraphNode;
use crate::state::Fingerprint;
use rustc_hash::{FxHashMap, FxHashSet};

/// Index of a state in the Buchi automaton (NBA).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct BuchiState(pub(crate) usize);

/// A node in the product automaton: (system state fingerprint, Buchi state).
///
/// Structurally compatible with [`BehaviorGraphNode`] for reuse of
/// existing graph infrastructure, but semantically distinct: product
/// nodes are built incrementally during BFS exploration.
pub(crate) type ProductNode = BehaviorGraphNode;

/// Create a product node from a system fingerprint and Buchi state.
pub(crate) fn product_node(fp: Fingerprint, buchi: BuchiState) -> ProductNode {
    ProductNode::new(fp, buchi.0)
}

/// Extract the Buchi state from a product node.
pub(crate) fn buchi_state_of(node: &ProductNode) -> BuchiState {
    BuchiState(node.tableau_idx)
}

/// Edge in the product graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ProductEdge {
    pub(crate) from: ProductNode,
    pub(crate) to: ProductNode,
}

/// Statistics for the on-the-fly LTL checker.
#[derive(Debug, Clone, Default)]
pub(crate) struct OnTheFlyStats {
    /// Number of product nodes created.
    pub(crate) product_nodes: usize,
    /// Number of product edges created.
    pub(crate) product_edges: usize,
    /// Number of consistency checks performed.
    pub(crate) consistency_checks: usize,
    /// Number of cycle detection runs triggered.
    pub(crate) cycle_checks: usize,
    /// Whether an accepting cycle was detected.
    pub(crate) violation_found: bool,
}

/// Result of on-the-fly cycle detection.
#[derive(Debug, Clone)]
pub(crate) enum CycleDetectionResult {
    /// No accepting cycle found yet.
    NoCycle,
    /// An accepting cycle was detected.
    AcceptingCycle {
        /// Nodes forming the accepting cycle in the product graph.
        cycle: Vec<ProductNode>,
    },
}

/// Default node limit for the on-the-fly product graph.
///
/// At ~100 bytes per node (node entry + successor list + predecessor list),
/// 2M nodes consumes ~200 MB. Beyond this, the product graph is likely too
/// large for efficient on-the-fly analysis. Override with
/// `TLA2_ON_THE_FLY_PRODUCT_NODE_LIMIT`.
///
/// Part of #4080: prevents unbounded memory growth in the on-the-fly LTL
/// checker's product graph.
const DEFAULT_PRODUCT_NODE_LIMIT: usize = 2_000_000;

/// Read the product graph node limit from environment or return default.
fn product_node_limit() -> Option<usize> {
    use std::sync::OnceLock;
    static LIMIT: OnceLock<Option<usize>> = OnceLock::new();
    *LIMIT.get_or_init(|| {
        let from_env = std::env::var("TLA2_ON_THE_FLY_PRODUCT_NODE_LIMIT")
            .ok()
            .and_then(|value| value.trim().parse::<usize>().ok());
        match from_env {
            Some(0) => None, // Explicit 0 disables the limit
            Some(n) => Some(n),
            None => Some(DEFAULT_PRODUCT_NODE_LIMIT),
        }
    })
}

/// Adjacency-list product graph maintained incrementally during BFS.
///
/// Stores both forward and reverse edges for efficient cycle detection
/// and trace reconstruction. Has a configurable node limit to prevent
/// unbounded memory growth (Part of #4080).
#[derive(Debug, Clone)]
pub(crate) struct ProductGraph {
    /// All product nodes discovered so far.
    pub(crate) nodes: FxHashSet<ProductNode>,
    /// Forward adjacency: node -> list of successors.
    pub(crate) successors: FxHashMap<ProductNode, Vec<ProductNode>>,
    /// Reverse adjacency: node -> list of predecessors.
    pub(crate) predecessors: FxHashMap<ProductNode, Vec<ProductNode>>,
    /// Optional node limit. When reached, `add_node` returns `false` for
    /// new nodes and a warning is logged once.
    node_limit: Option<usize>,
    /// Whether the limit-reached warning has been emitted.
    limit_warned: bool,
}

impl ProductGraph {
    /// Create an empty product graph with the default node limit.
    pub(crate) fn new() -> Self {
        Self {
            nodes: FxHashSet::default(),
            successors: FxHashMap::default(),
            predecessors: FxHashMap::default(),
            node_limit: product_node_limit(),
            limit_warned: false,
        }
    }

    /// Add a product node. Returns `true` if newly added.
    ///
    /// Returns `false` without inserting if the node limit has been reached.
    pub(crate) fn add_node(&mut self, node: ProductNode) -> bool {
        if self.nodes.contains(&node) {
            return false;
        }
        if let Some(limit) = self.node_limit {
            if self.nodes.len() >= limit {
                if !self.limit_warned {
                    self.limit_warned = true;
                    eprintln!(
                        "Warning: on-the-fly product graph reached node limit ({limit}); \
                         further nodes will be dropped. Override with \
                         TLA2_ON_THE_FLY_PRODUCT_NODE_LIMIT=0 to disable."
                    );
                }
                return false;
            }
        }
        self.nodes.insert(node)
    }

    /// Add a directed edge. Returns `true` if this is a new edge.
    ///
    /// If either endpoint would exceed the node limit, the edge is not added.
    pub(crate) fn add_edge(&mut self, from: ProductNode, to: ProductNode) -> bool {
        self.add_node(from);
        self.add_node(to);

        // Don't add edges for nodes that were dropped due to the limit.
        if !self.nodes.contains(&from) || !self.nodes.contains(&to) {
            return false;
        }

        let succs = self.successors.entry(from).or_default();
        if succs.contains(&to) {
            return false;
        }
        succs.push(to);
        self.predecessors.entry(to).or_default().push(from);
        true
    }

    /// Check if a node has a self-loop.
    pub(crate) fn has_self_loop(&self, node: &ProductNode) -> bool {
        self.successors
            .get(node)
            .is_some_and(|succs| succs.contains(node))
    }

    /// Get the successors of a node.
    pub(crate) fn get_successors(&self, node: &ProductNode) -> &[ProductNode] {
        self.successors
            .get(node)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Find all SCCs using iterative Tarjan's algorithm.
    ///
    /// Returns SCCs as vectors of product nodes. Each SCC contains all
    /// nodes that are mutually reachable.
    pub(crate) fn find_sccs(&self) -> Vec<Vec<ProductNode>> {
        let mut index_counter: usize = 0;
        let mut stack: Vec<ProductNode> = Vec::new();
        let mut on_stack: FxHashSet<ProductNode> = FxHashSet::default();
        let mut indices: FxHashMap<ProductNode, usize> = FxHashMap::default();
        let mut lowlinks: FxHashMap<ProductNode, usize> = FxHashMap::default();
        let mut result: Vec<Vec<ProductNode>> = Vec::new();

        for &start_node in &self.nodes {
            if indices.contains_key(&start_node) {
                continue;
            }

            let mut work_stack: Vec<(ProductNode, usize)> = vec![(start_node, 0)];
            while let Some((node, succ_pos)) = work_stack.last_mut() {
                let node = *node;

                if *succ_pos == 0 && !indices.contains_key(&node) {
                    indices.insert(node, index_counter);
                    lowlinks.insert(node, index_counter);
                    index_counter += 1;
                    stack.push(node);
                    on_stack.insert(node);
                }

                let succs = self.successors.get(&node);
                let succ_count = succs.map_or(0, |s| s.len());

                if *succ_pos < succ_count {
                    let succ = succs.expect("succ_count > 0 implies succs is Some")[*succ_pos];
                    *succ_pos += 1;

                    if !indices.contains_key(&succ) {
                        work_stack.push((succ, 0));
                    } else if on_stack.contains(&succ) {
                        let succ_index = indices[&succ];
                        let node_lowlink = lowlinks.get_mut(&node).expect("node has lowlink");
                        if succ_index < *node_lowlink {
                            *node_lowlink = succ_index;
                        }
                    }
                } else {
                    let node_index = indices[&node];
                    let node_lowlink = lowlinks[&node];

                    if node_lowlink == node_index {
                        let mut scc = Vec::new();
                        loop {
                            let w = stack.pop().expect("stack should not be empty");
                            on_stack.remove(&w);
                            scc.push(w);
                            if w == node {
                                break;
                            }
                        }
                        result.push(scc);
                    }

                    work_stack.pop();
                    if let Some((parent, _)) = work_stack.last() {
                        let parent = *parent;
                        let parent_lowlink = lowlinks.get_mut(&parent).expect("parent has lowlink");
                        if node_lowlink < *parent_lowlink {
                            *parent_lowlink = node_lowlink;
                        }
                    }
                }
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_product_graph_empty() {
        let graph = ProductGraph::new();
        assert!(graph.nodes.is_empty());
        let sccs = graph.find_sccs();
        assert!(sccs.is_empty());
    }

    #[test]
    fn test_product_graph_add_node() {
        let mut graph = ProductGraph::new();
        let n = product_node(Fingerprint(1), BuchiState(0));
        assert!(graph.add_node(n));
        assert!(!graph.add_node(n)); // duplicate
        assert_eq!(graph.nodes.len(), 1);
    }

    #[test]
    fn test_product_graph_add_edge() {
        let mut graph = ProductGraph::new();
        let a = product_node(Fingerprint(1), BuchiState(0));
        let b = product_node(Fingerprint(2), BuchiState(0));

        assert!(graph.add_edge(a, b));
        assert!(!graph.add_edge(a, b)); // duplicate edge
        assert_eq!(graph.nodes.len(), 2);
        assert_eq!(graph.get_successors(&a).len(), 1);
    }

    #[test]
    fn test_product_graph_self_loop() {
        let mut graph = ProductGraph::new();
        let a = product_node(Fingerprint(1), BuchiState(0));

        assert!(!graph.has_self_loop(&a));
        graph.add_edge(a, a);
        assert!(graph.has_self_loop(&a));
    }

    #[test]
    fn test_product_graph_scc_two_node_cycle() {
        let mut graph = ProductGraph::new();
        let a = product_node(Fingerprint(1), BuchiState(0));
        let b = product_node(Fingerprint(2), BuchiState(0));

        graph.add_edge(a, b);
        graph.add_edge(b, a);

        let sccs = graph.find_sccs();
        // Should find one SCC containing both nodes
        let big_sccs: Vec<_> = sccs.iter().filter(|scc| scc.len() >= 2).collect();
        assert_eq!(big_sccs.len(), 1);
        assert_eq!(big_sccs[0].len(), 2);
    }

    #[test]
    fn test_product_graph_scc_chain_no_cycle() {
        let mut graph = ProductGraph::new();
        let a = product_node(Fingerprint(1), BuchiState(0));
        let b = product_node(Fingerprint(2), BuchiState(0));
        let c = product_node(Fingerprint(3), BuchiState(0));

        graph.add_edge(a, b);
        graph.add_edge(b, c);

        let sccs = graph.find_sccs();
        // All singleton SCCs (no back-edge)
        assert!(sccs.iter().all(|scc| scc.len() == 1));
    }

    #[test]
    fn test_buchi_state_roundtrip() {
        let fp = Fingerprint(42);
        let bs = BuchiState(3);
        let node = product_node(fp, bs);
        assert_eq!(node.state_fp, fp);
        assert_eq!(buchi_state_of(&node), bs);
    }

    #[test]
    fn test_product_graph_node_limit_drops_excess() {
        // Create a graph with a small limit by directly setting the field.
        let mut graph = ProductGraph {
            nodes: FxHashSet::default(),
            successors: FxHashMap::default(),
            predecessors: FxHashMap::default(),
            node_limit: Some(3),
            limit_warned: false,
        };

        let a = product_node(Fingerprint(1), BuchiState(0));
        let b = product_node(Fingerprint(2), BuchiState(0));
        let c = product_node(Fingerprint(3), BuchiState(0));
        let d = product_node(Fingerprint(4), BuchiState(0));

        assert!(graph.add_node(a));
        assert!(graph.add_node(b));
        assert!(graph.add_node(c));
        // 4th node should be dropped
        assert!(!graph.add_node(d));
        assert_eq!(graph.nodes.len(), 3);
        assert!(!graph.nodes.contains(&d));
    }

    #[test]
    fn test_product_graph_edge_dropped_when_node_over_limit() {
        let mut graph = ProductGraph {
            nodes: FxHashSet::default(),
            successors: FxHashMap::default(),
            predecessors: FxHashMap::default(),
            node_limit: Some(2),
            limit_warned: false,
        };

        let a = product_node(Fingerprint(1), BuchiState(0));
        let b = product_node(Fingerprint(2), BuchiState(0));
        let c = product_node(Fingerprint(3), BuchiState(0));

        graph.add_node(a);
        graph.add_node(b);
        // Edge from b->c: c would be new and over limit, so edge not added
        assert!(!graph.add_edge(b, c));
        assert_eq!(graph.nodes.len(), 2);
        assert!(graph.get_successors(&b).is_empty());
    }

    #[test]
    fn test_product_graph_no_limit_when_none() {
        let mut graph = ProductGraph {
            nodes: FxHashSet::default(),
            successors: FxHashMap::default(),
            predecessors: FxHashMap::default(),
            node_limit: None,
            limit_warned: false,
        };

        // Should accept many nodes with no limit
        for i in 0..100 {
            assert!(graph.add_node(product_node(Fingerprint(i), BuchiState(0))));
        }
        assert_eq!(graph.nodes.len(), 100);
    }
}
