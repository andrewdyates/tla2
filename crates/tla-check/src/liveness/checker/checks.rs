// Licensed under the Apache License, Version 2.0

// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Top-level liveness checking entrypoint.

use super::ea_bitmask_query::{EaEdgeCheck, SccAggregateMasks};
use super::types::CounterexampleFingerprintPath;
use super::{
    BehaviorGraphNode, CounterexamplePath, GroupedLivenessPlan, InlineCheckResults,
    LivenessChecker, LivenessResult, TirProgram,
};
use crate::error::EvalResult;
use crate::liveness::debug::liveness_profile;
use rustc_hash::FxHashSet;
use std::cell::RefCell;
use std::time::Instant;

impl LivenessChecker {
    /// Check liveness with multiple PEM disjuncts against a shared graph.
    ///
    /// Uses per-node precomputed check bitmasks (#2572) so each unique check
    /// expression is evaluated once during mask population, stored in
    /// `NodeInfo.state_check_mask` and `NodeInfo.action_check_masks`. Per-PEM
    /// allowed-edge sets are assembled via bitmask operations, and PEMs
    /// sharing the same EA signature share a single Tarjan pass.
    ///
    /// Preserves per-PEM SCC correctness from #2047 (no union over
    /// heterogeneous EA sets). AE constraints are checked per-PEM.
    ///
    /// TLC reference: `LiveWorker.java:1280-1284`.
    /// Part of #3174: Bitmask-only mode — cross-property per-tag caches removed.
    pub fn check_liveness_grouped(
        &mut self,
        plan: &GroupedLivenessPlan,
        max_fairness_tag: u32,
    ) -> LivenessResult {
        self.check_liveness_grouped_with_inline_cache(plan, max_fairness_tag, None, None)
    }

    /// Part of #3174: Bitmask-only mode — cross-property per-tag caches removed.
    pub(crate) fn check_liveness_grouped_with_inline_cache(
        &mut self,
        plan: &GroupedLivenessPlan,
        max_fairness_tag: u32,
        inline_results: Option<InlineCheckResults<'_>>,
        tir: Option<&TirProgram<'_>>,
    ) -> LivenessResult {
        // Determine which check indices are used by ANY PEM for ANY purpose
        // (EA or AE). Evaluating all referenced checks upfront enables O(1)
        // bitmask lookups during SCC constraint checking (#2364 Approach G).
        let mut action_used = vec![false; plan.check_action.len()];
        let mut state_used = vec![false; plan.check_state.len()];
        for pem in &plan.pems {
            for &i in &pem.ea_action_idx {
                if i < action_used.len() {
                    action_used[i] = true;
                }
            }
            for &i in &pem.ea_state_idx {
                if i < state_used.len() {
                    state_used[i] = true;
                }
            }
            for &i in &pem.ae_action_idx {
                if i < action_used.len() {
                    action_used[i] = true;
                }
            }
            for &i in &pem.ae_state_idx {
                if i < state_used.len() {
                    state_used[i] = true;
                }
            }
        }

        // Populate per-node check bitmasks (#2572): evaluate each check once
        // across all graph nodes/edges, store results in NodeInfo fields.
        let populate_start = Instant::now();
        if let Err(e) = self.populate_node_check_masks_with_inline_cache(
            &plan.check_action,
            &plan.check_state,
            &action_used,
            &state_used,
            max_fairness_tag,
            inline_results,
            tir,
        ) {
            return LivenessResult::EvalFailure { error: e };
        }
        let profile = liveness_profile();
        if profile {
            eprintln!(
                "  check_liveness_grouped: populate_node_check_masks: {:.3}s",
                populate_start.elapsed().as_secs_f64()
            );
        }

        // Group PEMs by EA signature for Tarjan deduplication.
        let mut ea_groups: Vec<(Vec<usize>, Vec<usize>, Vec<usize>)> = Vec::new();
        for (pem_idx, pem) in plan.pems.iter().enumerate() {
            let mut found = false;
            for (ga, gs, group_pems) in &mut ea_groups {
                if *ga == pem.ea_action_idx && *gs == pem.ea_state_idx {
                    group_pems.push(pem_idx);
                    found = true;
                    break;
                }
            }
            if !found {
                ea_groups.push((
                    pem.ea_action_idx.clone(),
                    pem.ea_state_idx.clone(),
                    vec![pem_idx],
                ));
            }
        }

        // Per unique-EA-signature: build inline edge check from precomputed
        // bitmasks (#2704), run Tarjan once, check PEM AE constraints against SCCs.
        for (ea_action_idx, ea_state_idx, pem_indices) in &ea_groups {
            // 1. Build inline edge check from EA indices (#2704).
            // Replaces prior FxHashSet<(BGNode, BGNode)> materialization.
            let ea_check = EaEdgeCheck::new(ea_action_idx, ea_state_idx);

            // 2. Run Tarjan once for this EA signature.
            // Edge filter now reads bitmasks inline via EaEdgeCheck (#2704).
            let tarjan_start = Instant::now();
            let graph_ref = &self.graph;
            let edge_filter_error = RefCell::new(None);
            let scc_result = if let Some(ref ec) = ea_check {
                crate::liveness::tarjan::find_sccs_with_edge_filter(
                    &self.graph,
                    &|from_info, succ_idx, to| match graph_ref.try_get_node_info(to) {
                        Ok(Some(to_info)) => ec.allows_edge(from_info, succ_idx, &to_info),
                        Ok(None) => false,
                        Err(error) => {
                            if edge_filter_error.borrow().is_none() {
                                edge_filter_error.replace(Some(error.to_string()));
                            }
                            false
                        }
                    },
                )
            } else {
                self.find_sccs()
            };
            if let Some(error) = edge_filter_error.into_inner() {
                return LivenessResult::RuntimeFailure {
                    reason: format!(
                        "error reading graph nodes during Tarjan edge filtering: {error}"
                    ),
                };
            }
            if profile {
                eprintln!(
                    "  check_liveness_grouped: tarjan: {:.3}s (sccs={})",
                    tarjan_start.elapsed().as_secs_f64(),
                    scc_result.sccs.len()
                );
            }

            if !scc_result.errors.is_empty() {
                return LivenessResult::RuntimeFailure {
                    reason: format!(
                        "Tarjan SCC algorithm invariant violation: {}",
                        scc_result.errors.join("; ")
                    ),
                };
            }

            // 3. Pre-filter SCCs once per EA group (#2456).
            //    Both triviality and promise fulfillment depend only on the
            //    EA group's allowed_edges and the shared tableau/promises,
            //    NOT on the PEM's AE constraints. Pre-filtering converts
            //    O(PEM × total_SCCs × (triviality + promises)) to
            //    O(total_SCCs × (triviality + promises)).
            let prefilter_start = Instant::now();
            let candidate_sccs: Vec<&crate::liveness::tarjan::Scc> = {
                let mut result = Vec::new();
                for scc in &scc_result.sccs {
                    match self.is_trivial_scc_with_ea_check(scc, ea_check.as_ref()) {
                        Ok(true) => continue,
                        Ok(false) => {}
                        Err(e) => {
                            return LivenessResult::RuntimeFailure {
                                reason: format!("error checking SCC triviality: {e}"),
                            }
                        }
                    }
                    // Promise fulfillment is PEM-independent (uses self.promises).
                    match self.scc_fulfills_promises(scc) {
                        Ok(true) => result.push(scc),
                        Ok(false) => {}
                        Err(e) => {
                            return LivenessResult::RuntimeFailure {
                                reason: format!("error checking SCC promises: {e}"),
                            }
                        }
                    }
                }
                result
            };

            if profile {
                eprintln!(
                    "  check_liveness_grouped: prefilter_sccs: {:.3}s (candidates={}/{})",
                    prefilter_start.elapsed().as_secs_f64(),
                    candidate_sccs.len(),
                    scc_result.sccs.len()
                );
            }

            // Skip all PEMs if no candidate SCCs exist.
            if candidate_sccs.is_empty() {
                continue;
            }

            // Precompute SCC node sets once per SCC (#2714).
            // Previously, scc_ae_action_satisfied called scc.build_node_set() on
            // every PEM×SCC call. For P PEMs and S SCCs, that was P×S HashSet
            // allocations instead of S.
            let scc_node_sets: Vec<FxHashSet<BehaviorGraphNode>> = candidate_sccs
                .iter()
                .map(|scc| scc.build_node_set())
                .collect();

            // Precompute per-SCC aggregate bitmasks for O(1) AE constraint checks.
            // The aggregate state mask is the union of all nodes' state_check_mask.
            // The aggregate action mask is the union of all intra-SCC edges'
            // action_check_masks. When a required AE bit is absent from the
            // aggregate, the SCC cannot satisfy that constraint for ANY PEM,
            // allowing early skip without per-node iteration.
            let scc_aggregates: Vec<SccAggregateMasks> = match Self::try_build_scc_aggregates(
                &candidate_sccs,
                &scc_node_sets,
                ea_check.as_ref(),
                &self.graph,
            ) {
                Ok(agg) => agg,
                Err(error) => {
                    return LivenessResult::RuntimeFailure {
                        reason: format!("error building SCC aggregate masks: {error}"),
                    }
                }
            };

            // 4. For each PEM sharing this EA signature, check AE constraints
            //    against only the candidate SCCs using per-node bitmasks (#2572).
            //    No expression evaluation or HashMap lookup in this loop.
            for &pem_idx in pem_indices.iter() {
                let pem = &plan.pems[pem_idx];

                // Pre-build required masks for this PEM's AE constraints.
                // O(1) contains_all checks replace O(scc_size) per-node scans
                // when the aggregate mask proves the constraint is unsatisfiable.
                let required_ae_state = super::CheckMask::from_indices(&pem.ae_state_idx);
                let required_ae_action = super::CheckMask::from_indices(&pem.ae_action_idx);

                for (scc_idx, scc) in candidate_sccs.iter().enumerate() {
                    let agg = &scc_aggregates[scc_idx];

                    // Fast aggregate check: if the SCC's union of all state masks
                    // doesn't cover all required AE state bits, skip immediately.
                    // This avoids O(scc_size) per-node iteration when a fairness
                    // action is disabled in all states of the SCC.
                    if !pem.ae_state_idx.is_empty()
                        && !agg.state_mask.contains_all(&required_ae_state)
                    {
                        continue;
                    }

                    // Fast aggregate check for AE action constraints.
                    if !pem.ae_action_idx.is_empty()
                        && !agg.action_mask.contains_all(&required_ae_action)
                    {
                        continue;
                    }

                    // Aggregate passed — the SCC *might* satisfy the AE constraints.
                    // For AE state, the aggregate is exact (each bit is existential
                    // per check index), so no per-node fallback needed.
                    // For AE action, the aggregate is also exact: each bit in the
                    // aggregate means at least one intra-SCC edge has that bit set.
                    // Both try_scc_ae_state_satisfied and try_scc_ae_action_satisfied
                    // do per-index existential checks, which the aggregate already
                    // answers. Skip straight to witness construction.
                    //
                    // Note: The aggregate check is equivalent to the per-node check
                    // because both are existential (exists node with bit set). The
                    // aggregate union captures exactly this — if bit i is set in the
                    // aggregate, at least one node/edge has it set.

                    // Pass PEM indices for bitmask-based witness finding (#2572).
                    // No constraints installation needed — witness construction
                    // uses precomputed bitmasks instead of expression evaluation.
                    let cycle_nodes: Vec<BehaviorGraphNode> = match self.build_witness_cycle_in_scc(
                        scc,
                        ea_check.as_ref(),
                        &pem.ae_state_idx,
                        &pem.ae_action_idx,
                    ) {
                        Ok(Some(cycle)) => cycle,
                        Ok(None) => continue,
                        Err(e) => {
                            return LivenessResult::RuntimeFailure {
                                reason: format!("error constructing counterexample cycle: {e}"),
                            }
                        }
                    };

                    if self
                        .graph
                        .get_state_by_fp(cycle_nodes[0].state_fp)
                        .is_some()
                    {
                        let (prefix, cycle) = match self.build_counterexample(&cycle_nodes) {
                            Ok(v) => v,
                            Err(e) => {
                                return LivenessResult::RuntimeFailure {
                                    reason: format!("error constructing counterexample trace: {e}"),
                                };
                            }
                        };
                        return LivenessResult::Violated { prefix, cycle };
                    }

                    let (prefix, cycle) = match self.build_counterexample_fingerprints(&cycle_nodes)
                    {
                        Ok(v) => v,
                        Err(e) => {
                            return LivenessResult::RuntimeFailure {
                                reason: format!(
                                    "error constructing fingerprint-only counterexample: {e}"
                                ),
                            };
                        }
                    };
                    return LivenessResult::ViolatedFingerprints { prefix, cycle };
                }
            }
        }

        LivenessResult::Satisfied
    }

    /// Build a counterexample trace from a cycle in the behavior graph
    ///
    /// Returns (prefix, cycle) where:
    /// - prefix: Path from initial state to the start of the cycle
    /// - cycle: The violating cycle itself
    pub(super) fn build_counterexample(
        &self,
        cycle_nodes: &[BehaviorGraphNode],
    ) -> EvalResult<(CounterexamplePath, CounterexamplePath)> {
        let (prefix, cycle) = self.build_counterexample_fingerprints(cycle_nodes)?;
        let prefix = self.graph.resolve_fingerprint_trace(&prefix)?;
        let cycle = self.graph.resolve_fingerprint_trace(&cycle)?;
        Ok((prefix, cycle))
    }

    /// Build a fingerprint-only counterexample from a cycle in the behavior graph.
    pub(super) fn build_counterexample_fingerprints(
        &self,
        cycle_nodes: &[BehaviorGraphNode],
    ) -> EvalResult<(CounterexampleFingerprintPath, CounterexampleFingerprintPath)> {
        if cycle_nodes.is_empty() {
            return Ok((Vec::new(), Vec::new()));
        }

        let cycle_start = cycle_nodes[0];
        let prefix_trace = self.graph.reconstruct_fingerprint_trace(cycle_start)?;
        let mut cycle = Vec::with_capacity(cycle_nodes.len());
        for node in cycle_nodes {
            if self.graph.try_get_node_info(node)?.is_none() {
                return Err(Self::behavior_graph_invariant_error(format!(
                    "counterexample cycle references missing node {node}"
                )));
            }
            cycle.push((node.state_fp, node.tableau_idx));
        }

        let prefix = if prefix_trace.len() > 1 {
            prefix_trace[..prefix_trace.len() - 1].to_vec()
        } else {
            Vec::new()
        };

        Ok((prefix, cycle))
    }
}
