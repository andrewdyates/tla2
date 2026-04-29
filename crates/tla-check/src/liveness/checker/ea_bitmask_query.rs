// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bitmask query functions for precomputed EA check results (#2572, #2890).
//!
//! These functions read the per-node `state_check_mask` and `action_check_masks`
//! populated by `ea_precompute::populate_node_check_masks`, providing O(1)
//! bit lookups for SCC checking and edge eligibility.
//!
//! Uses multi-word `CheckMask` to support specs with >64 check indices (#2890).
//!
//! # Architecture (#2704)
//!
//! `EaEdgeCheck` replaces the prior `build_allowed_edges_from_nodes()` approach
//! that materialized a `FxHashSet<(BehaviorGraphNode, BehaviorGraphNode)>`.
//! Edge eligibility is now checked inline via O(1) bitmask operations on
//! precomputed `NodeInfo` masks, matching TLC's `GraphNode.getCheckAction()`
//! pattern (LiveWorker.java:400).

use super::check_mask::CheckMask;
use super::{BehaviorGraphNode, LivenessChecker};
use crate::error::EvalResult;
use crate::liveness::behavior_graph::{BehaviorGraph, NodeInfo};
use rustc_hash::FxHashSet;

/// Inline edge eligibility checker for EA constraints (#2704).
///
/// Replaces the prior `FxHashSet<(BehaviorGraphNode, BehaviorGraphNode)>`
/// approach. Checks bitmasks directly on `NodeInfo` — no allocation,
/// matching TLC's `GraphNode.getCheckAction()` pattern.
pub(crate) struct EaEdgeCheck {
    required_action: CheckMask,
    required_state: CheckMask,
    has_action: bool,
    has_state: bool,
}

impl EaEdgeCheck {
    /// Create an edge check from EA action and state indices.
    /// Returns `None` if both slices are empty (all edges allowed).
    pub(crate) fn new(ea_action_idx: &[usize], ea_state_idx: &[usize]) -> Option<Self> {
        if ea_action_idx.is_empty() && ea_state_idx.is_empty() {
            return None;
        }
        Some(Self {
            required_action: CheckMask::from_indices(ea_action_idx),
            required_state: CheckMask::from_indices(ea_state_idx),
            has_action: !ea_action_idx.is_empty(),
            has_state: !ea_state_idx.is_empty(),
        })
    }

    /// Check if an edge is allowed given pre-resolved node infos and successor index.
    /// This is the hot-path version used by the Tarjan edge filter where from_info
    /// and succ_idx are already available.
    #[inline]
    pub(crate) fn allows_edge(
        &self,
        from_info: &NodeInfo,
        succ_idx: usize,
        to_info: &NodeInfo,
    ) -> bool {
        if self.has_state
            && !from_info
                .state_check_mask
                .contains_all(&self.required_state)
        {
            return false;
        }
        if self.has_action {
            let passes = from_info
                .action_check_masks
                .get(succ_idx)
                .is_some_and(|m| m.contains_all(&self.required_action));
            if !passes {
                return false;
            }
        }
        if self.has_state && !to_info.state_check_mask.contains_all(&self.required_state) {
            return false;
        }
        true
    }

    /// Check if an edge (from, to) is allowed by looking up node infos from graph.
    /// This is the cold-path version used by witness cycle building where we only
    /// have node identifiers. Typical successor degree is 2-20, so the linear
    /// search for succ_idx is acceptable for the rare witness path.
    // Test-only boolean wrapper; production SCC/witness code uses
    // `try_allows_edge_pair` so disk-backed storage faults propagate.
    #[cfg(test)]
    pub(crate) fn allows_edge_pair(
        &self,
        graph: &BehaviorGraph,
        from: &BehaviorGraphNode,
        to: &BehaviorGraphNode,
    ) -> bool {
        self.try_allows_edge_pair(graph, from, to).unwrap_or(false)
    }

    pub(crate) fn try_allows_edge_pair(
        &self,
        graph: &BehaviorGraph,
        from: &BehaviorGraphNode,
        to: &BehaviorGraphNode,
    ) -> EvalResult<bool> {
        let Some(from_info) = graph.try_get_node_info(from)? else {
            return Ok(false);
        };
        let Some(succ_idx) = from_info.successors.iter().position(|s| s == to) else {
            return Ok(false);
        };
        let Some(to_info) = graph.try_get_node_info(to)? else {
            return Ok(false);
        };
        Ok(self.allows_edge(&from_info, succ_idx, &to_info))
    }
}

/// Precomputed aggregate bitmasks for an SCC.
///
/// The aggregate state mask is the bitwise OR of all `state_check_mask` values
/// across all nodes in the SCC. The aggregate action mask is the bitwise OR of
/// all `action_check_masks[j]` for intra-SCC edges only (edges where the
/// successor is also in the SCC and passes the EA edge filter).
///
/// These enable O(1) `contains_all` rejection: if a required AE bit is absent
/// from the aggregate, no node/edge in the SCC can satisfy it, so per-node
/// iteration is unnecessary. Since AE constraints are existential (at least one
/// node/edge must have the bit), the aggregate union is exact -- if the required
/// bit is present in the aggregate, the SCC definitely satisfies that constraint.
pub(super) struct SccAggregateMasks {
    /// Union of all `NodeInfo.state_check_mask` across SCC nodes.
    pub(super) state_mask: CheckMask,
    /// Union of all `NodeInfo.action_check_masks[j]` for intra-SCC, EA-allowed edges.
    pub(super) action_mask: CheckMask,
}

impl LivenessChecker {
    /// Build aggregate bitmasks for each candidate SCC.
    ///
    /// Computes the union of state and action check masks across all nodes in
    /// each SCC. For action masks, only intra-SCC edges that pass the EA edge
    /// filter are included. This is an O(V + E) one-time cost per EA group
    /// that eliminates O(PEM x SCC x scc_size) per-node iteration for AE checks.
    pub(super) fn try_build_scc_aggregates(
        candidate_sccs: &[&crate::liveness::tarjan::Scc],
        scc_node_sets: &[FxHashSet<BehaviorGraphNode>],
        ea_check: Option<&EaEdgeCheck>,
        graph: &BehaviorGraph,
    ) -> EvalResult<Vec<SccAggregateMasks>> {
        let mut result = Vec::with_capacity(candidate_sccs.len());
        for (scc_idx, scc) in candidate_sccs.iter().enumerate() {
            let scc_set = &scc_node_sets[scc_idx];
            let mut state_mask = CheckMask::new();
            let mut action_mask = CheckMask::new();

            for node in scc.nodes() {
                if let Some(info) = graph.try_get_node_info(node)? {
                    state_mask.or_assign(&info.state_check_mask);

                    for (succ_idx, succ) in info.successors.iter().enumerate() {
                        if !scc_set.contains(succ) {
                            continue;
                        }
                        if let Some(ec) = ea_check {
                            if let Some(to_info) = graph.try_get_node_info(succ)? {
                                if !ec.allows_edge(&info, succ_idx, &to_info) {
                                    continue;
                                }
                            } else {
                                continue;
                            }
                        }
                        if let Some(mask) = info.action_check_masks.get(succ_idx) {
                            action_mask.or_assign(mask);
                        }
                    }
                }
            }

            result.push(SccAggregateMasks {
                state_mask,
                action_mask,
            });
        }
        Ok(result)
    }

    /// Check AE state constraints using per-node precomputed bitmasks (#2572).
    ///
    /// For each AE state index, verifies that at least one SCC node has the
    /// corresponding check bit set in `NodeInfo.state_check_mask`. O(1) per
    /// bit lookup instead of expression evaluation.
    // Test-only boolean wrapper; production SCC checking uses the `try_*`
    // variant so disk-backed graph storage errors propagate.
    #[cfg(test)]
    pub(super) fn scc_ae_state_satisfied(
        scc: &crate::liveness::tarjan::Scc,
        ae_state_idx: &[usize],
        graph: &BehaviorGraph,
    ) -> bool {
        Self::try_scc_ae_state_satisfied(scc, ae_state_idx, graph).unwrap_or(false)
    }

    #[cfg(test)]
    pub(super) fn try_scc_ae_state_satisfied(
        scc: &crate::liveness::tarjan::Scc,
        ae_state_idx: &[usize],
        graph: &BehaviorGraph,
    ) -> EvalResult<bool> {
        for &check_idx in ae_state_idx {
            let mut found = false;
            for node in scc.nodes() {
                if graph
                    .try_get_node_info(node)?
                    .is_some_and(|info| info.state_check_mask.get(check_idx))
                {
                    found = true;
                    break;
                }
            }
            if !found {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Check AE action constraints using per-node precomputed bitmasks (#2572, #2704).
    ///
    /// For each AE action index, verifies that at least one intra-SCC edge has
    /// the corresponding check bit set in the from-node's
    /// `NodeInfo.action_check_masks`. Uses inline `EaEdgeCheck` instead of
    /// materialized HashSet. O(1) per bit lookup.
    // Test-only boolean wrapper; production SCC checking uses the `try_*`
    // variant so disk-backed graph storage errors propagate.
    #[cfg(test)]
    pub(super) fn scc_ae_action_satisfied(
        scc: &crate::liveness::tarjan::Scc,
        ae_action_idx: &[usize],
        ea_check: Option<&EaEdgeCheck>,
        graph: &BehaviorGraph,
        scc_set: &FxHashSet<BehaviorGraphNode>,
    ) -> bool {
        Self::try_scc_ae_action_satisfied(scc, ae_action_idx, ea_check, graph, scc_set)
            .unwrap_or(false)
    }

    #[cfg(test)]
    pub(super) fn try_scc_ae_action_satisfied(
        scc: &crate::liveness::tarjan::Scc,
        ae_action_idx: &[usize],
        ea_check: Option<&EaEdgeCheck>,
        graph: &BehaviorGraph,
        scc_set: &FxHashSet<BehaviorGraphNode>,
    ) -> EvalResult<bool> {
        if ae_action_idx.is_empty() {
            return Ok(true);
        }
        for &check_idx in ae_action_idx {
            let mut found = false;
            for node in scc.nodes() {
                if let Some(info) = graph.try_get_node_info(node)? {
                    for (succ_idx, succ) in info.successors.iter().enumerate() {
                        if !scc_set.contains(succ) {
                            continue;
                        }
                        if let Some(ec) = ea_check {
                            if !ec.try_allows_edge_pair(graph, node, succ)? {
                                continue;
                            }
                        }
                        let has_bit = info
                            .action_check_masks
                            .get(succ_idx)
                            .is_some_and(|mask| mask.get(check_idx));
                        if has_bit {
                            found = true;
                            break;
                        }
                    }
                }
                if found {
                    break;
                }
            }
            if !found {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
