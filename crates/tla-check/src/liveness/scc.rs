// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SCC data types for liveness checking.
//!
//! Pure data structures representing strongly connected components and
//! Tarjan algorithm results. Separated from the algorithm implementation
//! in `tarjan.rs` so consumers can import types without pulling in the
//! algorithm.

#[cfg(test)]
use super::behavior_graph::BehaviorGraph;
use super::behavior_graph::BehaviorGraphNode;
use rustc_hash::FxHashSet;
#[cfg(test)]
use tla_value::error::{EvalError, EvalResult};

/// A strongly connected component in the behavior graph
///
/// An SCC is a maximal set of nodes where every node can reach every other node.
/// In the context of liveness checking, an SCC represents a potential cycle in
/// the product graph (state × tableau).
#[derive(Debug, Clone)]
pub(super) struct Scc {
    /// The nodes in this SCC
    nodes: Vec<BehaviorGraphNode>,
}

impl Scc {
    /// Create a new SCC from a list of nodes
    pub(super) fn new(nodes: Vec<BehaviorGraphNode>) -> Self {
        Self { nodes }
    }

    /// Get the nodes in this SCC
    pub(super) fn nodes(&self) -> &[BehaviorGraphNode] {
        &self.nodes
    }

    /// Get the number of nodes in this SCC
    pub(super) fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Check if this SCC is empty
    pub(super) fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Build a HashSet of this SCC's nodes for O(1) membership testing.
    /// Callers should build once per SCC and reuse across operations.
    pub(super) fn build_node_set(&self) -> FxHashSet<BehaviorGraphNode> {
        self.nodes.iter().copied().collect()
    }
}

/// Check whether an SCC is trivial (single node without self-loop), returning
/// an error when graph invariants are violated.
#[cfg(test)]
pub(super) fn is_trivial_scc_in_graph(scc: &Scc, graph: &BehaviorGraph) -> EvalResult<bool> {
    if scc.nodes.len() != 1 {
        return Ok(false);
    }

    let node = &scc.nodes[0];
    let info = graph
        .get_node_info(node)
        .ok_or_else(|| EvalError::Internal {
            message: format!(
                "SCC node {:?} missing from behavior graph — graph construction invariant violated",
                node
            ),
            span: None,
        })?;
    Ok(!info.successors.contains(node))
}

/// Statistics for SCC detection (test-only: not read in production)
#[cfg(test)]
#[derive(Debug, Clone, Default)]
pub(super) struct TarjanStats {
    /// Number of SCCs found
    pub(super) scc_count: usize,
    /// Number of non-trivial SCCs (actual cycles)
    pub(super) nontrivial_sccs: usize,
    /// Largest SCC size
    pub(super) max_scc_size: usize,
    /// Total nodes processed
    pub(super) nodes_processed: usize,
}

/// Result of Tarjan's algorithm
#[derive(Debug, Clone)]
pub(crate) struct TarjanResult {
    /// All SCCs found, in reverse topological order
    pub(super) sccs: Vec<Scc>,
    /// Statistics about the computation (test-only)
    #[cfg(test)]
    pub(super) stats: TarjanStats,
    /// Algorithm invariant violations detected during computation.
    /// Should be empty under normal operation; non-empty indicates a bug
    /// in graph construction or the Tarjan implementation itself.
    pub(super) errors: Vec<String>,
}
