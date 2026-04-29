// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Behavior graph for liveness checking
//!
//! The behavior graph is the product of the state graph and the tableau automaton.
//! Each node is a `(state, tableau_node)` pair, and transitions follow both:
//! - The state graph (via the Next relation)
//! - The tableau automaton (via tableau node successors)
//!
//! A liveness violation exists iff there is a reachable accepting cycle in this
//! product graph.
//!
//! # TLC Reference
//!
//! This follows TLC's implementation in:
//! - `tlc2/tool/liveness/GraphNode.java` - Node representation
//! - `tlc2/tool/liveness/TableauNodePtrTable.java` - (fp, tidx) tracking
//! - `tlc2/tool/liveness/LiveCheck.java` - Product graph construction

use crate::error::EvalResult;
use crate::liveness::checker::CheckMask;
use crate::liveness::debug::{liveness_disk_graph_ptr_capacity, use_disk_graph};
use crate::liveness::graph_store::{invariant_error, NodeInfoView, RuntimeGraphStore};
use crate::state::{Fingerprint, State};
use rustc_hash::FxHashMap;
use std::fmt;
use std::sync::Arc;

/// A node in the behavior graph: (state fingerprint, tableau node index) pair
///
/// This is the fundamental unit for liveness checking. Two behavior graph nodes
/// are equal iff they have the same state fingerprint AND the same tableau index.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct BehaviorGraphNode {
    /// Fingerprint of the TLA+ state
    pub(crate) state_fp: Fingerprint,
    /// Index of the tableau node
    pub(crate) tableau_idx: usize,
}

impl BehaviorGraphNode {
    /// Create a new behavior graph node
    pub(crate) fn new(state_fp: Fingerprint, tableau_idx: usize) -> Self {
        Self {
            state_fp,
            tableau_idx,
        }
    }

    /// Create from a state and tableau index
    pub(crate) fn from_state(state: &State, tableau_idx: usize) -> Self {
        Self::new(state.fingerprint(), tableau_idx)
    }
}

impl fmt::Display for BehaviorGraphNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, t{})", self.state_fp, self.tableau_idx)
    }
}

/// The behavior graph: product of state graph × tableau
///
/// This structure tracks:
/// - All visited (state, tableau) pairs
/// - Transitions between pairs (for SCC detection)
/// - Parent pointers (for counterexample trace reconstruction)
///
/// States are stored separately from graph topology, deduplicated by fingerprint.
/// Multiple behavior graph nodes with the same state fingerprint (different tableau
/// indices) share a single State entry. This matches TLC's `GraphNode.java` which
/// stores only fingerprints + BitVectors in the graph, not full states.
/// (Approach I from `designs/2026-02-26-2364-liveness-architecture-alternative.md`)
#[derive(Debug)]
pub(crate) struct BehaviorGraph {
    /// Graph topology storage: nodes, edges, parent pointers, check masks.
    /// Part of #2732: runtime-selectable between the historical in-memory map
    /// and the new disk-backed node-record store.
    pub(crate) store: RuntimeGraphStore,
    /// Deduplicated state storage, keyed by fingerprint.
    /// One entry per unique state (shared across tableau indices).
    state_cache: FxHashMap<Fingerprint, State>,
    /// Part of #3065: Optional shared state cache from the model checker.
    /// When set, `get_state()` checks this first, avoiding State clones
    /// during graph construction for the fingerprint-based direct path.
    shared_state_cache: Option<Arc<FxHashMap<Fingerprint, State>>>,
}

/// Information stored for each behavior graph node
///
/// Does NOT store the full State — states are deduplicated in
/// `BehaviorGraph::state_cache` by fingerprint. Use `BehaviorGraph::get_state()`
/// to retrieve the state for a node.
#[derive(Debug, Clone)]
pub(crate) struct NodeInfo {
    /// Successor nodes (Vec for cache-friendly iteration; typical out-degree 2-20)
    pub(crate) successors: Vec<BehaviorGraphNode>,
    /// Parent node (for trace reconstruction)
    pub(crate) parent: Option<BehaviorGraphNode>,
    /// BFS depth
    pub(crate) depth: usize,
    /// Precomputed state check bitmask (#2572, #2890).
    /// Bit i set means `check_state[i]` is true for this node's state.
    /// Populated by `populate_node_check_masks()` after BFS construction.
    /// Uses multi-word `CheckMask` to support >64 check indices.
    pub(crate) state_check_mask: CheckMask,
    /// Precomputed action check bitmasks (#2572, #2890), aligned with `successors`.
    /// `action_check_masks[j]` has bit i set if `check_action[i]` is true for
    /// the transition `(this_node -> successors[j])`.
    /// Populated by `populate_node_check_masks()` after BFS construction.
    /// Uses multi-word `CheckMask` to support >64 check indices.
    pub(crate) action_check_masks: Vec<CheckMask>,
}

impl BehaviorGraph {
    fn with_store(store: RuntimeGraphStore) -> Self {
        Self {
            store,
            state_cache: FxHashMap::default(),
            shared_state_cache: None,
        }
    }

    /// Create a new empty in-memory behavior graph.
    pub(crate) fn new() -> Self {
        Self::with_store(RuntimeGraphStore::new_in_memory())
    }

    /// Create a disk-backed behavior graph with a specific pointer-table capacity.
    pub(crate) fn new_disk_backed(ptr_table_capacity: usize) -> EvalResult<Self> {
        Ok(Self::with_store(RuntimeGraphStore::new_disk_backed(
            ptr_table_capacity,
        )?))
    }

    /// Create a behavior graph using the current runtime liveness storage gate.
    pub(crate) fn new_from_env() -> EvalResult<Self> {
        if use_disk_graph() {
            Self::new_disk_backed(liveness_disk_graph_ptr_capacity())
        } else {
            Ok(Self::new())
        }
    }

    /// Create a behavior graph using the runtime liveness storage gate, with an
    /// optional size hint for auto-detecting when disk-backed storage is needed.
    ///
    /// When `estimated_nodes` exceeds `TLA2_LIVENESS_AUTO_DISK_THRESHOLD`
    /// (default 2M), the graph automatically uses disk-backed storage to prevent
    /// OOM on multi-property liveness specs (e.g., CoffeeCan3000Beans with 4.5M
    /// states and 5 grouped plans).
    pub(crate) fn new_from_env_with_hint(estimated_nodes: Option<usize>) -> EvalResult<Self> {
        // If explicitly requested via env var, use that unconditionally.
        if use_disk_graph() {
            return Self::new_disk_backed(liveness_disk_graph_ptr_capacity());
        }

        // Auto-detect: if estimated nodes exceed the threshold, use disk-backed.
        use super::debug::{liveness_auto_disk_threshold, liveness_profile};
        if let Some(est) = estimated_nodes {
            let threshold = liveness_auto_disk_threshold();
            if est > threshold {
                let capacity = est.next_power_of_two().max(1 << 20);
                if liveness_profile() {
                    eprintln!(
                        "[liveness] auto-disk: estimated {est} nodes > threshold {threshold}, \
                         using disk-backed graph (capacity {capacity})"
                    );
                }
                return Self::new_disk_backed(capacity);
            }
        }

        Ok(Self::new())
    }

    #[cfg(test)]
    pub(crate) fn is_disk_backed(&self) -> bool {
        self.store.is_disk_backed()
    }

    /// Part of #3065: Set a shared state cache from the model checker.
    /// When set, `get_state()` checks this cache first, and fingerprint-based
    /// methods can add nodes without cloning State objects.
    pub(crate) fn set_shared_state_cache(&mut self, cache: Arc<FxHashMap<Fingerprint, State>>) {
        self.shared_state_cache = Some(cache);
    }

    /// Part of #3065: Add an initial node by fingerprint only (no State clone).
    /// Requires shared_state_cache to be set. Returns true if newly added.
    pub(crate) fn try_add_init_node_by_fp(
        &mut self,
        fp: Fingerprint,
        tableau_idx: usize,
    ) -> EvalResult<bool> {
        let node = BehaviorGraphNode::new(fp, tableau_idx);
        self.store.add_init_node(node)
    }

    /// Part of #3065: Add a successor node by fingerprint only (no State clone).
    /// Requires shared_state_cache to be set. Returns true if successor is new.
    pub(crate) fn add_successor_by_fp(
        &mut self,
        from: BehaviorGraphNode,
        to_fp: Fingerprint,
        to_tableau_idx: usize,
    ) -> EvalResult<bool> {
        let to_node = BehaviorGraphNode::new(to_fp, to_tableau_idx);
        self.store.add_successor(from, to_node)
    }

    /// Add an initial node to the behavior graph
    ///
    /// Returns true if the node was newly added, false if it already existed.
    #[cfg(test)]
    pub fn add_init_node(&mut self, state: &State, tableau_idx: usize) -> bool {
        self.try_add_init_node(state, tableau_idx)
            .expect("in-memory behavior graph add_init_node should not fail")
    }

    pub(crate) fn try_add_init_node(
        &mut self,
        state: &State,
        tableau_idx: usize,
    ) -> EvalResult<bool> {
        self.try_add_init_node_with_fp(state, state.fingerprint(), tableau_idx)
    }

    /// Add an initial node using an explicit behavior-graph fingerprint.
    pub(crate) fn try_add_init_node_with_fp(
        &mut self,
        state: &State,
        state_fp: Fingerprint,
        tableau_idx: usize,
    ) -> EvalResult<bool> {
        let node = BehaviorGraphNode::new(state_fp, tableau_idx);
        if !self.store.add_init_node(node)? {
            return Ok(false);
        }
        self.state_cache
            .entry(node.state_fp)
            .or_insert_with(|| state.clone());
        Ok(true)
    }

    /// Add a successor node to the behavior graph
    ///
    /// Returns true if the successor was newly added, false if it already existed.
    pub(crate) fn add_successor(
        &mut self,
        from: BehaviorGraphNode,
        to_state: &State,
        to_tableau_idx: usize,
    ) -> EvalResult<bool> {
        self.add_successor_with_fp(from, to_state, to_state.fingerprint(), to_tableau_idx)
    }

    /// Add a successor node using an explicit behavior-graph fingerprint.
    pub(crate) fn add_successor_with_fp(
        &mut self,
        from: BehaviorGraphNode,
        to_state: &State,
        to_fp: Fingerprint,
        to_tableau_idx: usize,
    ) -> EvalResult<bool> {
        let to_node = BehaviorGraphNode::new(to_fp, to_tableau_idx);
        let is_new = self.store.add_successor(from, to_node)?;
        if is_new {
            self.state_cache
                .entry(to_node.state_fp)
                .or_insert_with(|| to_state.clone());
        }
        Ok(is_new)
    }

    /// Check if a behavior graph node has been visited.
    #[cfg(test)]
    pub(crate) fn contains(&self, node: &BehaviorGraphNode) -> bool {
        self.store.contains(*node)
    }

    /// Get information about a node for in-memory callers and tests.
    // Test-only convenience; production liveness uses try_get_node_info for error propagation.
    #[cfg(test)]
    pub fn get_node_info(&self, node: &BehaviorGraphNode) -> Option<NodeInfoView<'_>> {
        self.try_get_node_info(node)
            .expect("in-memory behavior graph get_node_info should not fail")
    }

    /// Get information about a node, propagating disk-backed storage errors.
    pub(crate) fn try_get_node_info(
        &self,
        node: &BehaviorGraphNode,
    ) -> EvalResult<Option<NodeInfoView<'_>>> {
        self.store.get_node_info(node)
    }

    /// Update a node's topology record in place.
    pub(crate) fn update_node_info<R>(
        &mut self,
        node: &BehaviorGraphNode,
        update: impl FnOnce(&mut NodeInfo) -> R,
    ) -> EvalResult<Option<R>> {
        self.store.update_node_info(node, update)
    }

    #[cfg(test)]
    pub fn get_node_info_mut(&mut self, node: &BehaviorGraphNode) -> Option<&mut NodeInfo> {
        self.store.get_node_info_mut(node)
    }

    /// Get the state for a behavior graph node (from deduplicated state cache).
    ///
    /// Looks up the state by fingerprint only — does NOT verify that the specific
    /// `(state_fp, tableau_idx)` pair exists in the graph topology. All callers
    /// should ensure the node is in the graph before calling this (e.g., from BFS
    /// queue, SCC iteration, or after a `get_node_info()` check).
    pub(crate) fn get_state(&self, node: &BehaviorGraphNode) -> Option<&State> {
        if let Some(ref shared) = self.shared_state_cache {
            if let Some(state) = shared.get(&node.state_fp) {
                return Some(state);
            }
        }
        self.state_cache.get(&node.state_fp)
    }

    /// Get a state directly by fingerprint.
    ///
    /// Used by the fingerprint-only liveness path to evaluate ENABLED without
    /// reconstructing `Vec<State>` successor caches after graph exploration.
    pub(crate) fn get_state_by_fp(&self, fp: Fingerprint) -> Option<&State> {
        if let Some(ref shared) = self.shared_state_cache {
            if let Some(state) = shared.get(&fp) {
                return Some(state);
            }
        }
        self.state_cache.get(&fp)
    }

    /// Get initial nodes in insertion order.
    #[cfg(test)]
    pub(crate) fn init_nodes(&self) -> Vec<BehaviorGraphNode> {
        self.store.init_nodes()
    }

    /// Get the number of nodes in the behavior graph.
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.store.node_count()
    }

    /// Get all node keys.
    pub(crate) fn node_keys(&self) -> Vec<BehaviorGraphNode> {
        self.store.node_keys()
    }

    /// Resolve a fingerprint-only path to concrete states via the state cache.
    ///
    /// Part of #3746: Tolerates missing states from the non-atomic seen_fps/seen
    /// insert race in parallel mode. Missing states are skipped instead of
    /// producing a hard error, yielding a potentially shorter but valid trace.
    pub(crate) fn resolve_fingerprint_trace(
        &self,
        trace: &[(Fingerprint, usize)],
    ) -> EvalResult<Vec<(State, usize)>> {
        let resolved: Vec<(State, usize)> = trace
            .iter()
            .filter_map(|(state_fp, tableau_idx)| {
                let node = BehaviorGraphNode::new(*state_fp, *tableau_idx);
                let state = self.get_state(&node)?;
                Some((state.clone(), *tableau_idx))
            })
            .collect();
        if resolved.is_empty() && !trace.is_empty() {
            return Err(invariant_error(format!(
                "trace reconstruction: all {} state(s) missing from cache — \
                 cannot produce any counterexample trace",
                trace.len(),
            )));
        }
        Ok(resolved)
    }

    /// Reconstruct a trace from an initial state to the given node
    // Currently test-only convenience; production liveness uses fingerprint traces.
    // Retained for future counterexample trace reconstruction.
    #[cfg(test)]
    pub fn reconstruct_trace(&self, end: BehaviorGraphNode) -> EvalResult<Vec<(State, usize)>> {
        let trace = self.reconstruct_fingerprint_trace(end)?;
        self.resolve_fingerprint_trace(&trace)
    }

    /// Reconstruct a fingerprint-only trace from an initial node to `end`.
    pub(crate) fn reconstruct_fingerprint_trace(
        &self,
        end: BehaviorGraphNode,
    ) -> EvalResult<Vec<(Fingerprint, usize)>> {
        self.store.reconstruct_fingerprint_trace(end)
    }
}

impl Default for BehaviorGraph {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
#[path = "behavior_graph_tests.rs"]
mod tests;
