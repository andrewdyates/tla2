// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Grouped liveness plan execution: tableau construction, state-graph
//! exploration, SCC result checking, and state cache materialization.
//!
//! Extracted from `liveness.rs` (Part of #3535): separates execution-heavy
//! tableau/graph exploration from the orchestration facade.

use super::*;

use super::liveness_graph::LivenessGraphData;
use crate::liveness::{LiveExpr, LivenessChecker, LivenessResult, Tableau};
use crate::{EvalCheckError, LivenessCheckError};

impl ParallelChecker {
    /// Run one grouped liveness plan: build Tableau, explore, check SCCs.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn run_plan_group(
        &self,
        ctx: &mut EvalCtx,
        stats: &CheckStats,
        graph: &LivenessGraphData,
        state_cache: &Arc<FxHashMap<Fingerprint, State>>,
        prop_name: &str,
        plan: &crate::liveness::GroupedLivenessPlan,
        max_fairness_tag: u32,
    ) -> Option<CheckResult> {
        let tableau = Tableau::new(plan.tf.clone());
        let mut checker = match LivenessChecker::new_from_env(tableau, ctx.clone()) {
            Ok(checker) => checker,
            Err(e) => {
                return Some(check_error_to_result(
                    LivenessCheckError::RuntimeFailure(format!(
                        "Failed to create liveness checker for '{prop_name}': {e}"
                    ))
                    .into(),
                    stats,
                ));
            }
        };
        // Part of #3011: Pass succ_witnesses for correct ENABLED/action evaluation
        // under symmetry. Without this, the liveness checker uses canonical representatives
        // instead of concrete successor states, causing incorrect action predicate results.
        checker.set_successor_maps(
            Arc::clone(&graph.state_fp_to_canon_fp),
            graph.succ_witnesses.as_ref().map(Arc::clone),
        );

        // Part of #2762: Read stuttering_allowed from the resolved spec formula
        // instead of hardcoding true. `[A]_v` → true, `<<A>>_v` → false.
        // Previously this was hardcoded to `true`, ignoring <<A>>_v specs.
        let add_stuttering = self.stuttering_allowed;
        let cached_successors = &graph.cached_successors;
        let fp_map = &graph.state_fp_to_canon_fp;

        let mut get_successors =
            |state: &State| -> Result<Vec<State>, tla_value::error::EvalError> {
                let fp = state.fingerprint();
                let canon_fp = fp_map.get(&fp).copied().unwrap_or(fp);
                // Part of #2929: Distinguish frontier vs deadlocked vs normal states:
                // - `None` → frontier state (not yet BFS-expanded) → sink (no edges)
                // - `Some(empty)` → deadlocked state (expanded, no successors) → stuttering
                // - `Some(non-empty)` → normal state with successors → successors + stuttering
                //
                // During periodic liveness (mid-BFS), frontier states must be sinks.
                // Adding a stuttering self-loop to a frontier state creates a spurious
                // single-node SCC where ENABLED incorrectly returns FALSE, causing false
                // liveness violations for specs with WF/SF fairness constraints.
                let entry = cached_successors.get(&canon_fp);
                let mut succs: Vec<State> = entry
                    .map(|fps| {
                        fps.iter()
                            .filter_map(|sfp| state_cache.get(sfp).cloned())
                            .collect()
                    })
                    .unwrap_or_default();
                // Only add stuttering if the state has been fully expanded (has an
                // entry in cached_successors). Frontier states (None) become sinks.
                if add_stuttering && entry.is_some() {
                    succs.push(state.clone());
                }
                Ok(succs)
            };

        // When tf == Bool(true) (pure WF/SF fairness — the common case), skip the
        // tableau cross-product and build the behavior graph directly from the state
        // graph. TLC uses LiveChecker (no tableau) vs TableauLiveChecker for this split.
        // Part of #2768. Part of #3065: use fingerprint-based exploration for the
        // direct path to eliminate O(V + E) State clones during graph construction.
        let explore_result = if matches!(&plan.tf, LiveExpr::Bool(true)) {
            // Part of #3065: Share the state cache with the behavior graph so
            // get_state() can look up states without cloning into a separate cache.
            checker.set_behavior_graph_shared_cache(Arc::clone(state_cache));
            // Part of #3801: Filter successor FPs to only include states present
            // in the materialized state cache. In fp-only parallel mode, the
            // post-BFS replay may not reconstruct every state referenced by
            // `cached_successors` (e.g., when replay re-enumeration produces
            // different fingerprints than the original BFS due to evaluation
            // context differences). Without this filter, the behavior graph
            // contains nodes whose concrete state data is absent from
            // `shared_state_cache`, causing `populate_node_check_masks` to crash
            // with "missing state for fp" errors. This matches the `filter_map`
            // guard in the BFS path's `get_successors` closure (line 75).
            let mut get_successor_fps =
                |fp: Fingerprint| -> Result<Vec<Fingerprint>, tla_value::error::EvalError> {
                    let canon_fp = fp_map.get(&fp).copied().unwrap_or(fp);
                    let entry = cached_successors.get(&canon_fp);
                    let mut succs: Vec<Fingerprint> = entry
                        .map(|fps| {
                            fps.iter()
                                .copied()
                                .filter(|sfp| state_cache.contains_key(sfp))
                                .collect()
                        })
                        .unwrap_or_default();
                    // Only add stuttering if the state has been fully expanded.
                    if add_stuttering && entry.is_some() {
                        succs.push(fp);
                    }
                    Ok(succs)
                };
            // Part of #3801: Filter init FPs to only include states present in
            // the materialized state cache, matching the BFS path's filter_map
            // at line 130.
            let filtered_init_fps: Vec<Fingerprint> = graph
                .init_fps
                .iter()
                .copied()
                .filter(|fp| state_cache.contains_key(fp))
                .collect();
            let result =
                checker.explore_state_graph_direct_fp(&filtered_init_fps, &mut get_successor_fps);
            // Part of #3065: Populate state_successors from the graph so
            // ENABLED evaluation in populate_node_check_masks has the
            // successor states it needs. Without this, ENABLED always
            // returns FALSE and WF/SF fairness is trivially satisfied.
            if let Err(e) = checker.populate_state_successor_fps_from_graph() {
                return Some(check_error_to_result(
                    LivenessCheckError::RuntimeFailure(format!(
                        "Failed to derive liveness successor fingerprints for '{prop_name}': {e}"
                    ))
                    .into(),
                    stats,
                ));
            }
            result
        } else {
            // Part of #2661: Resolve init states from the materialized state cache
            // using init_fps, instead of storing a pre-converted Vec<State>. This
            // eliminates to_state() from the hot build_liveness_graph_data path.
            let init_states: Vec<State> = graph
                .init_fps
                .iter()
                .filter_map(|fp| state_cache.get(fp).cloned())
                .collect();
            checker.explore_bfs(&init_states, &mut get_successors, None)
        };
        if let Err(e) = explore_result {
            return Some(check_error_to_result(EvalCheckError::Eval(e).into(), stats));
        }

        // Part of #3065: Cross-property check result caches. Fairness-derived
        // check tags (1..max_fairness_tag) are stable across properties because
        // each property creates a fresh converter and converts fairness first.
        let liveness_result = checker.check_liveness_grouped(plan, max_fairness_tag);
        match liveness_result {
            LivenessResult::Satisfied => None,
            LivenessResult::Violated { prefix, cycle } => {
                // Part of #2470 Step 3: Identify action labels for liveness traces.
                // Combines prefix + cycle states, identifies labels on the combined list,
                // then splits labels back — matching the sequential checker approach.
                let prefix_states: Vec<State> = prefix.into_iter().map(|(s, _)| s).collect();
                let mut cycle_states: Vec<State> = cycle.into_iter().map(|(s, _)| s).collect();

                // Part of #2470 Step 4: append back-edge duplicate so the
                // formatter can detect "Back to state" and compute the
                // back-edge action label. Matches sequential checker path.
                if cycle_states.len() >= 2 {
                    let back_edge_state = cycle_states[0].clone();
                    cycle_states.push(back_edge_state);
                }

                let next_name = self.config.next.as_deref().unwrap_or("Next");
                let label_ctx = crate::checker_ops::ActionLabelCtx {
                    next_name,
                    next_def: self.op_defs.get(next_name),
                    file_id_to_path: &self.file_id_to_path,
                    module_name: &self.module.name.node,
                };

                let full_states: Vec<State> = prefix_states
                    .iter()
                    .chain(cycle_states.iter())
                    .cloned()
                    .collect();
                let full_labels =
                    crate::checker_ops::identify_action_labels(ctx, &label_ctx, &full_states);

                let prefix_len = prefix_states.len();
                let prefix_labels = full_labels[..prefix_len].to_vec();
                let cycle_labels = full_labels[prefix_len..].to_vec();

                let prefix_trace = Trace::from_states_with_labels(prefix_states, prefix_labels);
                let cycle_trace = Trace::from_states_with_labels(cycle_states, cycle_labels);

                Some(CheckResult::LivenessViolation {
                    property: prop_name.to_string(),
                    prefix: prefix_trace,
                    cycle: cycle_trace,
                    stats: stats.clone(),
                })
            }
            LivenessResult::ViolatedFingerprints { .. } => Some(check_error_to_result(
                LivenessCheckError::RuntimeFailure(format!(
                    "parallel liveness checker unexpectedly returned fingerprint-only counterexample data for '{prop_name}'"
                ))
                .into(),
                stats,
            )),
            LivenessResult::RuntimeFailure { reason } => Some(check_error_to_result(
                LivenessCheckError::RuntimeFailure(format!(
                    "Liveness runtime failure for '{prop_name}': {reason}"
                ))
                .into(),
                stats,
            )),
            LivenessResult::EvalFailure { error } => Some(check_error_to_result(
                EvalCheckError::Eval(error).into(),
                stats,
            )),
        }
    }

    pub(super) fn materialize_liveness_state_cache(
        &self,
        state_cache: &FxHashMap<Fingerprint, ArrayState>,
    ) -> Arc<FxHashMap<Fingerprint, State>> {
        let mut materialized: FxHashMap<Fingerprint, State> =
            FxHashMap::with_capacity_and_hasher(state_cache.len(), Default::default());
        for (fp, state) in state_cache {
            materialized.insert(*fp, state.to_state(&self.var_registry));
        }
        Arc::new(materialized)
    }
}
