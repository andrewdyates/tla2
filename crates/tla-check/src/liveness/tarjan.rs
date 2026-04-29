// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Arena-based iterative Tarjan's algorithm for SCC detection
//!
//! This module implements an arena-indexed iterative Tarjan's algorithm to find
//! strongly connected components (SCCs) in the behavior graph. SCCs are cycles
//! in the product graph that may indicate liveness violations.
//!
//! # Algorithm Overview
//!
//! Tarjan's algorithm uses depth-first search to find SCCs in O(V + E) time.
//! This implementation is iterative (rather than recursive) to handle large
//! graphs without stack overflow.
//!
//! The key insight is that an SCC is identified when we find a node that is
//! its own "low link" - meaning it can reach itself through a cycle.
//!
//! # Performance — Arena-Based Indexing
//!
//! For large graphs (e.g., CoffeeCan3000Beans with 9M+ nodes), hash-map-based
//! node state lookups dominate runtime. This implementation uses a two-phase
//! approach:
//!
//! **Phase 1 — Indexing:** All `BehaviorGraphNode` keys are mapped to contiguous
//! `u32` indices. This is a one-time O(V) cost using `FxHashMap`.
//!
//! **Phase 2 — Arena DFS:** All node states, successor lists, and stacks use
//! `u32` indices into flat `Vec<T>` arrays. This replaces hash-map lookups with
//! O(1) array indexing during the DFS, which is cache-friendly and avoids the
//! ~7ns/lookup overhead of `FxHashMap` at 9M entries.
//!
//! Successor lists are stored in a contiguous arena (`succ_arena: Vec<u32>`)
//! where each node's successors are a contiguous slice referenced by
//! `(start, count)`. This eliminates per-node `Vec` allocation and enables
//! sequential memory access patterns during DFS.
//!
//! Trivial SCC filtering (single-node SCCs without self-loops) is done inline
//! during extraction via `has_self_loop` on `ArenaNodeState`, avoiding a
//! post-hoc graph lookup pass.
//!
//! # TLC Reference
//!
//! This follows TLC's implementation in:
//! - `tlc2/tool/liveness/LiveWorker.java` - checkSccs method
//!
//! # References
//!
//! - Tarjan, R. E. (1972). "Depth-first search and linear graph algorithms"
//! - <https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm>

use super::behavior_graph::{BehaviorGraph, BehaviorGraphNode, NodeInfo};
#[cfg(test)]
use super::scc::is_trivial_scc_in_graph;
#[cfg(test)]
use super::scc::TarjanStats;
use rustc_hash::FxHashMap;

// Re-export SCC types for backward compatibility with existing references
// to `tarjan::Scc`, `tarjan::TarjanResult`, etc. in checker modules.
pub(super) use super::scc::{Scc, TarjanResult};

/// Optional edge filter predicate for Tarjan's algorithm (#2704).
///
/// Receives `(from_info, succ_idx, to)` so the filter can read precomputed
/// bitmasks directly from `NodeInfo` without a redundant graph lookup.
/// The `to` node is provided so the filter can look up `to_info` from the
/// graph if needed (e.g., for EA state checks on the destination).
type EdgeFilter<'a> = Option<&'a dyn Fn(&NodeInfo, usize, &BehaviorGraphNode) -> bool>;

/// Sentinel value indicating an arena node has not been visited yet.
const NOT_VISITED: u32 = u32::MAX;

/// Default node-count threshold above which Tarjan arena allocation emits an
/// OOM-advisory note to stderr.
///
/// At ~92 bytes/node + 4 bytes/edge, 1M nodes ≈ ~100 MB arena. Operators on
/// small-memory hosts may want a lower threshold; large hosts may want higher.
///
/// Override via `TLA2_TARJAN_ARENA_WARN_NODES`. `0` disables the warning.
///
/// Part of #4080: OOM safety — tarjan SCC arena visibility.
const DEFAULT_TARJAN_ARENA_WARN_THRESHOLD: usize = 1_000_000;

/// Read the Tarjan arena warn threshold from the environment, falling back to
/// [`DEFAULT_TARJAN_ARENA_WARN_THRESHOLD`].
///
/// Cached on first call so repeated SCC runs pay no env-parsing cost.
fn tarjan_arena_warn_threshold() -> usize {
    static CACHED: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *CACHED.get_or_init(|| {
        std::env::var("TLA2_TARJAN_ARENA_WARN_NODES")
            .ok()
            .and_then(|v| v.trim().parse::<usize>().ok())
            .unwrap_or(DEFAULT_TARJAN_ARENA_WARN_THRESHOLD)
    })
}

/// Per-node state in the arena, indexed by `u32` node id.
///
/// Packed into 16 bytes for cache efficiency (vs 24+ bytes with a hash-map
/// entry including key and bucket metadata).
#[derive(Debug, Clone, Copy)]
struct ArenaNodeState {
    /// Discovery index (NOT_VISITED if unvisited)
    index: u32,
    /// Lowest reachable index
    low_link: u32,
    /// Whether node is currently on the Tarjan stack
    on_stack: bool,
    /// Whether this node has a self-loop (edge to itself).
    has_self_loop: bool,
}

impl ArenaNodeState {
    /// Unvisited sentinel state.
    const UNVISITED: Self = Self {
        index: NOT_VISITED,
        low_link: NOT_VISITED,
        on_stack: false,
        has_self_loop: false,
    };
}

/// Per-node successor information, pre-collected during the indexing phase.
#[derive(Debug, Clone, Copy)]
struct ArenaSuccInfo {
    /// Start index in the shared successor arena.
    start: u32,
    /// Number of successors.
    count: u32,
}

/// Frame for iterative DFS traversal using arena indices.
///
/// Uses `u32` indices instead of `BehaviorGraphNode` (16 bytes) for compactness.
#[derive(Debug, Clone, Copy)]
enum DfsFrame {
    /// First visit to a node - discover and push to stack.
    Visit { node_id: u32 },
    /// After processing all successors - check for SCC root.
    PostProcess { node_id: u32 },
    /// Process next successor.
    ProcessSuccessor {
        node_id: u32,
        /// Current successor index (0-based within the node's successor slice).
        succ_idx: u32,
    },
}

/// Find all strongly connected components using arena-based iterative Tarjan's algorithm.
///
/// This is the main entry point for SCC detection. It returns all non-trivial
/// SCCs in the graph in reverse topological order (i.e., if SCC A can reach
/// SCC B, then B comes before A in the output).
///
/// Trivial SCCs (single-node without self-loop) are filtered inline during
/// extraction and are NOT included in the result.
///
/// # Arguments
///
/// * `graph` - The behavior graph to analyze
///
/// # Returns
///
/// A `TarjanResult` containing all non-trivial SCCs and statistics
pub(super) fn find_sccs(graph: &BehaviorGraph) -> TarjanResult {
    ArenaTarjan::run(graph, None)
}

/// Find SCCs using Tarjan's algorithm, restricting edges with a predicate (#2704).
///
/// The edge filter receives `(from_info, succ_idx, to)` where `from_info` is the
/// source node's `NodeInfo` (with precomputed bitmasks) and `succ_idx` is the
/// index in `from_info.successors`. This allows O(1) bitmask checks without
/// redundant graph lookups, matching TLC's inline `getCheckAction()` pattern.
///
/// Trivial SCCs (single-node without self-loop) are filtered inline during
/// extraction and are NOT included in the result.
pub(super) fn find_sccs_with_edge_filter(
    graph: &BehaviorGraph,
    edge_filter: &dyn Fn(&NodeInfo, usize, &BehaviorGraphNode) -> bool,
) -> TarjanResult {
    ArenaTarjan::run(graph, Some(edge_filter))
}

/// Find non-trivial SCCs (actual cycles) in the behavior graph.
///
/// This is a convenience function that filters out trivial SCCs
/// (single nodes without self-loops). Returns a full `TarjanResult`
/// so callers can check for algorithm errors. Part of #1817.
///
/// Note: `find_sccs` already filters trivial SCCs inline. This function
/// provides a secondary validation via `is_trivial_scc_in_graph` for tests.
///
/// If `is_trivial_scc_in_graph` detects a missing graph node (invariant violation),
/// the error is recorded in `result.errors` and the SCC is retained
/// (not silently dropped).
#[cfg(test)]
pub(super) fn find_cycles(graph: &BehaviorGraph) -> TarjanResult {
    let mut result = find_sccs(graph);
    let mut trivial_errors = Vec::new();
    result
        .sccs
        .retain(|scc| match is_trivial_scc_in_graph(scc, graph) {
            Ok(true) => false, // trivial -> filter out
            Ok(false) => true, // non-trivial -> keep
            Err(e) => {
                // Missing node invariant violation -> keep SCC and record error
                trivial_errors.push(format!(
                    "is_trivial failed for SCC ({} nodes): {}",
                    scc.len(),
                    e
                ));
                true
            }
        });
    result.errors.extend(trivial_errors);
    result
}

/// Arena-based Tarjan's algorithm.
///
/// Two-phase approach for cache-friendly SCC detection on large graphs:
///
/// 1. **Index phase:** Map all `BehaviorGraphNode` to contiguous `u32` ids.
///    Pre-collect all (filtered) successors into a flat `Vec<u32>` arena.
///    This touches the `BehaviorGraph` once.
///
/// 2. **DFS phase:** Run iterative Tarjan using only flat `Vec<T>` arrays
///    indexed by `u32`. No hash-map lookups during the DFS itself.
struct ArenaTarjan {
    /// Number of nodes in the arena.
    node_count: u32,
    /// Map from arena id back to `BehaviorGraphNode` (for SCC output).
    id_to_node: Vec<BehaviorGraphNode>,
    /// Per-node successor info (start, count) into `succ_arena`.
    succ_info: Vec<ArenaSuccInfo>,
    /// Contiguous arena of successor ids.
    succ_arena: Vec<u32>,
    /// Per-node Tarjan state.
    states: Vec<ArenaNodeState>,
    /// Discovery index counter.
    index: u32,
    /// Tarjan stack (arena ids).
    stack: Vec<u32>,
    /// Found SCCs.
    sccs: Vec<Scc>,
    /// Algorithm invariant violations.
    errors: Vec<String>,
    /// Statistics (test-only: not read in production).
    #[cfg(test)]
    stats: TarjanStats,
}

impl ArenaTarjan {
    /// Run the full two-phase arena Tarjan algorithm.
    fn run(graph: &BehaviorGraph, edge_filter: EdgeFilter<'_>) -> TarjanResult {
        let mut arena = Self::build_arena(graph, edge_filter);
        arena.find_all_sccs();

        TarjanResult {
            sccs: arena.sccs,
            #[cfg(test)]
            stats: arena.stats,
            errors: arena.errors,
        }
    }

    /// Phase 1: Build the arena by indexing all nodes and collecting successors.
    ///
    /// Part of #4080: logs arena memory estimate for large graphs so operators
    /// can anticipate OOM risk. The arena is structurally bounded by the
    /// behavior graph size (which has its own 5M node limit), but arena + graph
    /// together can use 2x the memory of the graph alone.
    fn build_arena(graph: &BehaviorGraph, edge_filter: EdgeFilter<'_>) -> Self {
        let all_nodes = graph.node_keys();
        let n = all_nodes.len();

        // Part of #4080: warn when arena allocation will be large.
        // Arena memory estimate: node_to_id (32 bytes/entry) + id_to_node (16 bytes)
        // + succ_info (8 bytes) + states (4 bytes) + succ_arena (~4*n * 4 bytes).
        // Total: ~76 bytes/node + 16 bytes/edge.
        //
        // The warning threshold is env-configurable (`TLA2_TARJAN_ARENA_WARN_NODES`,
        // default 1M) so small-memory agents can lower it and larger hosts can raise
        // it to suppress noise.
        if n > tarjan_arena_warn_threshold() {
            let estimated_mb = (n * 76 + n * 4 * 4) / (1024 * 1024);
            eprintln!(
                "Note: Tarjan SCC arena allocating for {n} nodes (~{estimated_mb} MB). \
                 Consider disk-backed liveness graph for large state spaces."
            );
        }

        // Build bidirectional index.
        let mut node_to_id: FxHashMap<BehaviorGraphNode, u32> =
            FxHashMap::with_capacity_and_hasher(n, Default::default());
        let mut id_to_node: Vec<BehaviorGraphNode> = Vec::with_capacity(n);

        for (i, node) in all_nodes.iter().enumerate() {
            node_to_id.insert(*node, i as u32);
            id_to_node.push(*node);
        }

        // Pre-collect successors into the arena.
        // Estimate: average out-degree ~4, so pre-allocate 4*n.
        let mut succ_arena: Vec<u32> = Vec::with_capacity(n.saturating_mul(4));
        let mut succ_info: Vec<ArenaSuccInfo> = Vec::with_capacity(n);
        let mut states: Vec<ArenaNodeState> = vec![ArenaNodeState::UNVISITED; n];
        let mut errors: Vec<String> = Vec::new();

        for (arena_id, node) in all_nodes.iter().enumerate() {
            let start = succ_arena.len() as u32;
            let mut has_self_loop = false;

            match graph.try_get_node_info(node) {
                Ok(Some(info)) => {
                    if let Some(ef) = edge_filter {
                        for (succ_idx, succ) in info.successors.iter().enumerate() {
                            if ef(&info, succ_idx, succ) {
                                if let Some(&succ_id) = node_to_id.get(succ) {
                                    if succ_id == arena_id as u32 {
                                        has_self_loop = true;
                                    }
                                    succ_arena.push(succ_id);
                                }
                                // Successors not in node_to_id are outside the graph
                                // (shouldn't happen but defensive).
                            }
                        }
                    } else {
                        for succ in &info.successors {
                            if let Some(&succ_id) = node_to_id.get(succ) {
                                if succ_id == arena_id as u32 {
                                    has_self_loop = true;
                                }
                                succ_arena.push(succ_id);
                            }
                        }
                    }
                }
                Ok(None) => {
                    errors.push(format!(
                        "Tarjan DFS visited node {:?} (arena_id={}) \
                         but it is missing from behavior graph \u{2014} \
                         graph construction invariant violated",
                        node, arena_id
                    ));
                }
                Err(error) => {
                    errors.push(format!(
                        "Tarjan DFS failed to read node {:?} (arena_id={}): {}",
                        node, arena_id, error
                    ));
                }
            }

            let count = succ_arena.len() as u32 - start;
            succ_info.push(ArenaSuccInfo { start, count });

            // Pre-set self-loop flag so the DFS phase doesn't need to recompute it.
            states[arena_id].has_self_loop = has_self_loop;
        }

        Self {
            node_count: n as u32,
            id_to_node,
            succ_info,
            succ_arena,
            states,
            index: 0,
            stack: Vec::with_capacity(n.min(1 << 20)),
            sccs: Vec::new(),
            errors,
            #[cfg(test)]
            stats: TarjanStats::default(),
        }
    }

    /// Phase 2: Run iterative Tarjan on all unvisited nodes.
    fn find_all_sccs(&mut self) {
        for node_id in 0..self.node_count {
            if self.states[node_id as usize].index == NOT_VISITED {
                self.tarjan_iterative(node_id);
            }
        }

        #[cfg(test)]
        {
            self.stats.scc_count = self.sccs.len();
        }
    }

    /// Iterative Tarjan's algorithm starting from a given arena node.
    ///
    /// All lookups are O(1) array indexing -- no hash maps touched.
    fn tarjan_iterative(&mut self, start: u32) {
        let mut dfs_stack: Vec<DfsFrame> = vec![DfsFrame::Visit { node_id: start }];

        while let Some(frame) = dfs_stack.pop() {
            match frame {
                DfsFrame::Visit { node_id } => {
                    self.handle_visit(node_id, &mut dfs_stack);
                }
                DfsFrame::ProcessSuccessor { node_id, succ_idx } => {
                    self.handle_process_successor(node_id, succ_idx, &mut dfs_stack);
                }
                DfsFrame::PostProcess { node_id } => {
                    self.handle_post_process(node_id);
                }
            }
        }
    }

    /// DFS Visit: discover a node, assign index/low_link, push to Tarjan stack.
    #[inline]
    fn handle_visit(&mut self, node_id: u32, dfs_stack: &mut Vec<DfsFrame>) {
        let idx = node_id as usize;

        // Already visited? (can happen when multiple DFS roots queue the same node)
        if self.states[idx].index != NOT_VISITED {
            return;
        }

        let discovery = self.index;
        self.index += 1;

        self.states[idx].index = discovery;
        self.states[idx].low_link = discovery;
        self.states[idx].on_stack = true;
        self.stack.push(node_id);

        #[cfg(test)]
        {
            self.stats.nodes_processed += 1;
        }

        // Push PostProcess first (it will execute after all successors are done).
        dfs_stack.push(DfsFrame::PostProcess { node_id });

        // Push first successor processing frame if this node has successors.
        let si = self.succ_info[idx];
        if si.count > 0 {
            dfs_stack.push(DfsFrame::ProcessSuccessor {
                node_id,
                succ_idx: 0,
            });
        }
    }

    /// DFS ProcessSuccessor: handle one successor, push Visit or update low_link.
    #[inline]
    fn handle_process_successor(
        &mut self,
        node_id: u32,
        succ_idx: u32,
        dfs_stack: &mut Vec<DfsFrame>,
    ) {
        let si = self.succ_info[node_id as usize];
        if succ_idx >= si.count {
            return;
        }

        let succ_id = self.succ_arena[(si.start + succ_idx) as usize];

        // Enqueue next successor before recursing into this one.
        let next_succ_idx = succ_idx + 1;
        if next_succ_idx < si.count {
            dfs_stack.push(DfsFrame::ProcessSuccessor {
                node_id,
                succ_idx: next_succ_idx,
            });
        }

        let succ_state = self.states[succ_id as usize];
        if succ_state.index != NOT_VISITED {
            // Successor already visited.
            if succ_state.on_stack {
                let node_state = &mut self.states[node_id as usize];
                node_state.low_link = node_state.low_link.min(succ_state.index);
            }
        } else {
            // Successor not visited -- Visit it; low_link update handled in PostProcess.
            dfs_stack.push(DfsFrame::Visit { node_id: succ_id });
        }
    }

    /// DFS PostProcess: update low_link from successors, extract SCC if root.
    #[inline]
    fn handle_post_process(&mut self, node_id: u32) {
        let si = self.succ_info[node_id as usize];

        // Collect min low_link from on-stack successors (Tarjan 1972 S3).
        let mut min_low_link = self.states[node_id as usize].low_link;

        let succ_end = (si.start + si.count) as usize;
        for i in si.start as usize..succ_end {
            let succ_id = self.succ_arena[i];
            let succ_state = self.states[succ_id as usize];
            if succ_state.on_stack {
                min_low_link = min_low_link.min(succ_state.low_link);
            }
        }

        self.states[node_id as usize].low_link = min_low_link;

        // Check if this node is the root of an SCC.
        let state = self.states[node_id as usize];
        if state.low_link == state.index {
            self.extract_scc(node_id);
        }
    }

    /// Pop SCC members from the Tarjan stack and record the SCC.
    ///
    /// Inline trivial SCC filtering: single-node SCCs without self-loops are
    /// skipped (not added to `self.sccs`), avoiding a post-hoc graph lookup.
    fn extract_scc(&mut self, root_id: u32) {
        let mut scc_ids: Vec<u32> = Vec::new();

        loop {
            let top = match self.stack.pop() {
                Some(top) => top,
                None => {
                    self.errors.push(format!(
                        "Tarjan invariant violated: SCC root {:?} \
                         must be on stack (index={}, stack empty, \
                         partial SCC has {} nodes)",
                        self.id_to_node[root_id as usize],
                        self.states[root_id as usize].index,
                        scc_ids.len()
                    ));
                    break;
                }
            };

            self.states[top as usize].on_stack = false;
            scc_ids.push(top);

            if top == root_id {
                break;
            }
        }

        let scc_size = scc_ids.len();

        // Inline trivial SCC filtering: a single-node SCC without a self-loop
        // is trivial (no actual cycle). Skip it to avoid post-hoc graph lookups.
        if scc_size == 1 {
            if !self.states[scc_ids[0] as usize].has_self_loop {
                return;
            }
        }

        #[cfg(test)]
        {
            if scc_size > self.stats.max_scc_size {
                self.stats.max_scc_size = scc_size;
            }
            if scc_size > 1 {
                self.stats.nontrivial_sccs += 1;
            }
        }

        // Convert arena ids back to BehaviorGraphNode for the output SCC.
        let scc_nodes: Vec<BehaviorGraphNode> = scc_ids
            .iter()
            .map(|&id| self.id_to_node[id as usize])
            .collect();
        self.sccs.push(Scc::new(scc_nodes));
    }
}

/// Find SCCs that contain accepting nodes (potential liveness violations)
///
/// This is the main function for liveness checking. It finds all non-trivial
/// SCCs that contain at least one accepting tableau node.
///
/// # Arguments
///
/// * `graph` - The behavior graph
/// * `is_accepting` - Function to check if a node is accepting
///
/// # Returns
///
/// `TarjanResult` with SCCs filtered to non-trivial accepting cycles.
/// Callers should check `result.errors` for algorithm invariant violations.
#[cfg(test)]
pub(crate) fn find_accepting_sccs<F>(graph: &BehaviorGraph, is_accepting: F) -> TarjanResult
where
    F: Fn(&BehaviorGraphNode) -> bool,
{
    let mut result = find_sccs(graph);
    // Trivial SCCs (single-node without self-loop) are already filtered inline
    // by extract_scc. Only retain SCCs that contain at least one accepting node.
    result
        .sccs
        .retain(|scc| scc.nodes().iter().any(&is_accepting));
    result
}

#[cfg(test)]
#[path = "tarjan_tests/mod.rs"]
mod tests;
