// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-node check-mask precompute for grouped liveness checking (#2572).
//!
//! Part of #3174: Bitmask-only mode. With tags < 64 enforced, all liveness
//! results are captured in inline bitmask maps during BFS recording. The
//! per-tag cross-property HashMap caches have been removed.
//!
//! Evaluates each used check once across the graph, storing results in
//! `NodeInfo.state_check_mask` / `NodeInfo.action_check_masks` for O(1) SCC lookups.

use super::check_mask::CheckMask;
use super::ea_precompute_cache;
use super::ea_precompute_enabled::{collect_enabled_nodes, EnabledInfo};
use super::ea_precompute_leaf_batch::try_populate_action_masks_from_leaf_batches;
use super::ea_precompute_profile::PopulateMasksProfile;
use super::live_expr::LiveExpr;
use super::{BehaviorGraph, BehaviorGraphNode, InlineCheckResults, LivenessChecker, TirProgram};
use crate::liveness::debug::liveness_profile;
use crate::state::Fingerprint;
use rustc_hash::{FxHashMap, FxHashSet};
use std::time::Instant;

fn unique_state_error(context: &'static str, fp: Fingerprint) -> crate::error::EvalError {
    crate::error::EvalError::Internal {
        message: format!("populate_node_check_masks: missing {context} state for fp {fp}"),
        span: None,
    }
}

fn get_unique_state<'a>(
    unique_states: &'a FxHashMap<Fingerprint, crate::state::State>,
    fp: Fingerprint,
    context: &'static str,
) -> Result<&'a crate::state::State, crate::error::EvalError> {
    unique_states
        .get(&fp)
        .ok_or_else(|| unique_state_error(context, fp))
}

/// Part of #3746: Returns `Ok(false)` (instead of an error) when the state is
/// missing from the graph's state cache.  This can happen in parallel/
/// fingerprint-only mode where successor fingerprints are recorded but the
/// concrete state data is not available in the shared state cache.  Callers
/// must tolerate missing states by skipping the affected nodes.
///
/// When `TLA2_STRICT_LIVENESS=1`, returns an error instead of `Ok(false)` so
/// that missing states surface as hard failures for debugging.
fn cache_graph_state(
    unique_states: &mut FxHashMap<Fingerprint, crate::state::State>,
    graph: &BehaviorGraph,
    node: &BehaviorGraphNode,
    context: &'static str,
) -> Result<bool, crate::error::EvalError> {
    if let std::collections::hash_map::Entry::Vacant(entry) = unique_states.entry(node.state_fp) {
        if let Some(state) = graph.get_state(node) {
            entry.insert(state.clone());
        } else {
            if crate::liveness::debug::strict_liveness() {
                return Err(unique_state_error(context, node.state_fp));
            }
            return Ok(false);
        }
    }
    Ok(true)
}

/// Part of #3746: Optional state lookup that returns None for missing states
/// instead of an error.  Used for successor states that may be absent from
/// the shared state cache in parallel/fingerprint-only mode.
fn try_get_unique_state<'a>(
    unique_states: &'a FxHashMap<Fingerprint, crate::state::State>,
    fp: Fingerprint,
) -> Option<&'a crate::state::State> {
    unique_states.get(&fp)
}

impl LivenessChecker {
    /// Populate per-node check bitmasks in the behavior graph (#2572, #3065).
    ///
    /// Part of #3174: Simplified — no per-tag cross-property caches. Uses
    /// bitmask fast path when structurally cached, falls back to direct
    /// eval otherwise.
    #[cfg(test)]
    pub(super) fn populate_node_check_masks(
        &mut self,
        check_action: &[LiveExpr],
        check_state: &[LiveExpr],
        action_used: &[bool],
        state_used: &[bool],
        max_fairness_tag: u32,
    ) -> Result<(), crate::error::EvalError> {
        self.populate_node_check_masks_with_inline_cache(
            check_action,
            check_state,
            action_used,
            state_used,
            max_fairness_tag,
            None,
            None,
        )
    }

    /// Part of #3174: Bitmask-only mode. Per-tag cross-property caches removed.
    pub(super) fn populate_node_check_masks_with_inline_cache(
        &mut self,
        check_action: &[LiveExpr],
        check_state: &[LiveExpr],
        action_used: &[bool],
        state_used: &[bool],
        max_fairness_tag: u32,
        inline_results: Option<InlineCheckResults<'_>>,
        tir: Option<&TirProgram<'_>>,
    ) -> Result<(), crate::error::EvalError> {
        // Clear subscript value cache from any previous property group.
        super::subscript_cache::clear_subscript_value_cache();

        let profile = liveness_profile();

        // Part of #3065, #3100, #3174: Fast reconstruction path. When all used
        // check expressions have only fairness-tagged leaves or property-scoped
        // inline tags, skip the expensive O(V) State clone pass and reconstruct
        // masks purely from cached bitmask results.
        if Self::all_checks_structurally_cached(
            check_state,
            check_action,
            state_used,
            action_used,
            max_fairness_tag,
            inline_results,
        ) {
            if profile {
                eprintln!(
                    "    populate_masks: FAST PATH — all checks reconstructable from inline bitmask cache",
                );
            }
            return self.populate_node_check_masks_from_cache(
                check_action,
                check_state,
                action_used,
                state_used,
                max_fairness_tag,
                inline_results,
            );
        }

        // Eval fallback: snapshot topology + clone each unique state once.
        // This path is only reached for symmetry/VIEW specs where inline
        // recording doesn't cover all tags.
        struct NodeData {
            node: BehaviorGraphNode,
            successors: Vec<BehaviorGraphNode>,
        }

        let mut pf = PopulateMasksProfile::new();

        let mut unique_states: FxHashMap<Fingerprint, crate::state::State> = FxHashMap::default();
        // Part of #3746: skip nodes whose state is missing from the graph's
        // shared state cache (can happen in parallel/fingerprint-only mode).
        // Missing-state nodes get empty bitmasks, which is conservative:
        // they will never satisfy AE/EA constraints.
        let node_data: Vec<NodeData> = self
            .graph
            .node_keys()
            .into_iter()
            .filter_map(|node| {
                let info = match self.graph.try_get_node_info(&node) {
                    Ok(Some(info)) => info,
                    Ok(None) => return None,
                    Err(e) => return Some(Err(e)),
                };
                match cache_graph_state(&mut unique_states, &self.graph, &node, "graph node") {
                    Ok(false) => return None, // state missing — skip this node
                    Err(e) => return Some(Err(e)),
                    Ok(true) => {}
                }
                let successors = info.successors.clone();
                for succ in &successors {
                    // Silently skip successors with missing states;
                    // they won't be in unique_states and downstream
                    // bitmask evaluation will produce default (false) masks.
                    let _ = cache_graph_state(&mut unique_states, &self.graph, succ, "successor");
                }
                Some(Ok(NodeData { node, successors }))
            })
            .collect::<Result<Vec<_>, crate::error::EvalError>>()?;

        pf.node_count = node_data.len();
        pf.unique_state_count = unique_states.len();
        pf.state_check_start = Instant::now();

        // Evaluate state checks: for each unique fingerprint, compute bitmask.
        let mut state_mask: FxHashMap<Fingerprint, CheckMask> = FxHashMap::default();
        for (check_idx, check) in check_state.iter().enumerate() {
            if !state_used.get(check_idx).copied().unwrap_or(false) {
                continue;
            }
            let mut seen_fps: FxHashSet<Fingerprint> = FxHashSet::default();
            for nd in &node_data {
                let from_fp = nd.node.state_fp;
                if seen_fps.insert(from_fp) {
                    // Try bitmask lookup first, fall back to eval.
                    let result = Self::try_reconstruct_state_check(inline_results, from_fp, check)
                        .map_or_else(
                            || {
                                let from_state = get_unique_state(
                                    &unique_states,
                                    from_fp,
                                    "state-check source",
                                )?;
                                self.eval_live_check_expr(check, from_state, None, tir)
                            },
                            Ok,
                        )?;
                    if result {
                        state_mask.entry(from_fp).or_default().set(check_idx);
                    } else {
                        state_mask.entry(from_fp).or_default();
                    }
                }
                for succ in &nd.successors {
                    let to_fp = succ.state_fp;
                    if seen_fps.insert(to_fp) {
                        let result =
                            Self::try_reconstruct_state_check(inline_results, to_fp, check)
                                .map_or_else(
                                    || {
                                        // Part of #3746: gracefully skip successors whose
                                        // state is missing from the cache (parallel mode).
                                        let Some(succ_state) =
                                            try_get_unique_state(&unique_states, to_fp)
                                        else {
                                            return Ok(false);
                                        };
                                        self.eval_live_check_expr(check, succ_state, None, tir)
                                    },
                                    Ok,
                                )?;
                        if result {
                            state_mask.entry(to_fp).or_default().set(check_idx);
                        } else {
                            state_mask.entry(to_fp).or_default();
                        }
                    }
                }
            }
        }

        pf.state_used_count = state_used.iter().filter(|&&u| u).count();
        pf.state_total_count = state_used.len();
        pf.action_check_start = Instant::now();

        // Evaluate action checks batched per unique (from_fp, to_fp) pair.
        let mut action_masks: Vec<Vec<CheckMask>> = node_data
            .iter()
            .map(|nd| vec![CheckMask::new(); nd.successors.len()])
            .collect();

        let mut fp_to_mask: FxHashMap<(Fingerprint, Fingerprint), CheckMask> = FxHashMap::default();
        let mut seen_transitions: FxHashSet<(Fingerprint, Fingerprint)> = FxHashSet::default();
        let mut unique_transitions: Vec<(Fingerprint, Fingerprint, usize, usize)> = Vec::new();
        for (nd_idx, nd) in node_data.iter().enumerate() {
            let from_fp = nd.node.state_fp;
            for (succ_idx, succ) in nd.successors.iter().enumerate() {
                let to_fp = succ.state_fp;
                if seen_transitions.insert((from_fp, to_fp)) {
                    unique_transitions.push((from_fp, to_fp, nd_idx, succ_idx));
                }
            }
        }

        let mut by_from: FxHashMap<Fingerprint, Vec<(Fingerprint, usize, usize)>> =
            FxHashMap::default();
        for &(from_fp, to_fp, nd_idx, succ_idx) in &unique_transitions {
            by_from
                .entry(from_fp)
                .or_default()
                .push((to_fp, nd_idx, succ_idx));
        }
        for nd in &node_data {
            by_from.entry(nd.node.state_fp).or_default();
        }

        pf.subscript_start = Instant::now();
        // Always precompute subscripts on the eval fallback path.
        self.precompute_subscript_values(check_action, action_used, &unique_states)?;
        pf.unique_transition_count = unique_transitions.len();
        pf.by_from_group_count = by_from.len();
        pf.eval_loop_start = Instant::now();

        if try_populate_action_masks_from_leaf_batches(
            self,
            check_action,
            action_used,
            &unique_states,
            &by_from,
            &mut fp_to_mask,
            &mut pf,
            tir,
        )? {
            if profile {
                pf.print();
            }

            // Apply cached masks to action_masks.
            for (nd_idx, nd) in node_data.iter().enumerate() {
                let from_fp = nd.node.state_fp;
                for (succ_idx, succ) in nd.successors.iter().enumerate() {
                    let to_fp = succ.state_fp;
                    if let Some(mask) = fp_to_mask.get(&(from_fp, to_fp)) {
                        action_masks[nd_idx][succ_idx] = mask.clone();
                    }
                }
            }

            // Write results into NodeInfo.
            for (nd_idx, nd) in node_data.iter().enumerate() {
                self.graph.update_node_info(&nd.node, |info| {
                    info.state_check_mask = state_mask
                        .get(&nd.node.state_fp)
                        .cloned()
                        .unwrap_or_default();
                    info.action_check_masks.clone_from(&action_masks[nd_idx]);
                })?;
            }

            return Ok(());
        }

        // Collect ENABLED info from check expressions.
        let mut enabled_infos_raw: Vec<EnabledInfo> = Vec::new();
        for (check_idx, check) in check_action.iter().enumerate() {
            if !action_used.get(check_idx).copied().unwrap_or(false) {
                continue;
            }
            collect_enabled_nodes(check, &mut enabled_infos_raw);
        }
        let enabled_infos: Vec<&EnabledInfo> = {
            let mut seen_tags: FxHashSet<u32> = FxHashSet::default();
            enabled_infos_raw
                .iter()
                .filter(|info| seen_tags.insert(info.tag))
                .collect()
        };

        // Eval path: evaluate expressions directly without cross-property per-tag caches.
        {
            if self.succ_witnesses.is_some() || self.ctx.var_registry().is_empty() {
                // Pre-compute ENABLED (HashMap/witness path).
                if !enabled_infos.is_empty() {
                    // Part of #3962: Use ctx-aware variant to sync in_enabled_scope shadow.
                    let _enabled_guard =
                        crate::eval::enter_enabled_scope_with_ctx(&self.ctx);
                    let mut seen_fps: FxHashSet<Fingerprint> = FxHashSet::default();
                    for nd in &node_data {
                        let state_fp = nd.node.state_fp;
                        if !seen_fps.insert(state_fp) {
                            continue;
                        }
                        for info in &enabled_infos {
                            let eval_ctx = match info.bindings {
                                Some(ref chain) => self.ctx.with_liveness_bindings(chain),
                                None => self.ctx.clone(),
                            };
                            super::eval_enabled_cached(&eval_ctx, state_fp, info.tag, || {
                                let from_state =
                                    get_unique_state(&unique_states, state_fp, "ENABLED source")?;
                                self.eval_enabled(
                                    &eval_ctx,
                                    from_state,
                                    &info.action,
                                    info.bindings.as_ref(),
                                    info.require_state_change,
                                    info.subscript.as_ref(),
                                )
                            })?;
                        }
                    }
                }
                for (from_fp, transitions) in &by_from {
                    for &(to_fp, nd_idx, succ_idx) in transitions {
                        pf.fresh_eval_transitions += 1;
                        let from_state =
                            get_unique_state(&unique_states, *from_fp, "action source")?;
                        let actual_to_fp = node_data[nd_idx].successors[succ_idx].state_fp;
                        // Part of #3746: skip transitions whose destination state
                        // is missing from the cache (parallel mode).
                        let Some(to_state) = try_get_unique_state(&unique_states, actual_to_fp)
                        else {
                            fp_to_mask.insert((*from_fp, to_fp), CheckMask::new());
                            continue;
                        };

                        // Bind state variables for this transition (empty-registry path).
                        // eval_live_check_expr_inner assumes ctx is pre-configured.
                        let prev_env = self.ctx.env().clone();
                        for (name, value) in from_state.vars() {
                            self.ctx
                                .bind_mut(std::sync::Arc::clone(name), value.clone());
                        }
                        let cached_next_env = self.get_cached_env(to_state);
                        let _next_state_guard = self.ctx.take_next_state_guard();
                        *self.ctx.next_state_mut() = Some(cached_next_env);

                        let mut mask = CheckMask::new();
                        for (check_idx, check) in check_action.iter().enumerate() {
                            if !action_used.get(check_idx).copied().unwrap_or(false) {
                                continue;
                            }
                            if self.eval_live_check_expr_inner(
                                check,
                                from_state,
                                Some(to_state),
                                tir,
                            )? {
                                mask.set(check_idx);
                            }
                        }

                        *self.ctx.env_mut() = prev_env;
                        fp_to_mask.insert((*from_fp, to_fp), mask);
                    }
                }
            } else {
                // Optimized path: merged ENABLED + action checks with array binding.
                let registry_cloned = self.ctx.var_registry().clone();

                for (from_fp, transitions) in &by_from {
                    let from_state =
                        get_unique_state(&unique_states, *from_fp, "optimized source")?;
                    let current_values = from_state.to_values(&registry_cloned);
                    let _state_guard = self.ctx.bind_state_array_guard(&current_values);

                    // Phase A: ENABLED evaluation.
                    if !enabled_infos.is_empty() {
                        // Part of #3962: Use ctx-aware variant to sync in_enabled_scope shadow.
                        let _enabled_guard =
                            crate::eval::enter_enabled_scope_with_ctx(&self.ctx);
                        for info in &enabled_infos {
                            let state_fp = *from_fp;
                            if super::is_enabled_cached(state_fp, info.tag) {
                                continue;
                            }
                            let result = self.eval_enabled_for_node(
                                info,
                                from_state,
                                state_fp,
                                &registry_cloned,
                            )?;
                            super::set_enabled_cache(state_fp, info.tag, result);
                        }
                    }

                    // Phase B: Evaluate action checks.
                    for &(to_fp, nd_idx, succ_idx) in transitions {
                        pf.fresh_eval_transitions += 1;
                        let next_fp = node_data[nd_idx].successors[succ_idx].state_fp;
                        // Part of #3746: skip transitions whose destination state
                        // is missing from the cache (parallel mode).
                        let Some(next_state) = try_get_unique_state(&unique_states, next_fp) else {
                            fp_to_mask.insert((*from_fp, to_fp), CheckMask::new());
                            continue;
                        };
                        let cached_next_env = self.get_cached_env(next_state);
                        let next_values = next_state.to_values(&registry_cloned);

                        let _next_state_guard = self.ctx.take_next_state_guard();
                        let _next_guard = self.ctx.take_next_state_env_guard();
                        *self.ctx.next_state_mut() = Some(cached_next_env);
                        self.ctx.bind_next_state_array(&next_values);

                        let mut mask = CheckMask::new();
                        for (check_idx, check) in check_action.iter().enumerate() {
                            if !action_used.get(check_idx).copied().unwrap_or(false) {
                                continue;
                            }
                            let result = self.eval_live_check_expr_inner(
                                check,
                                from_state,
                                Some(next_state),
                                tir,
                            )?;
                            if result {
                                mask.set(check_idx);
                            }
                        }

                        fp_to_mask.insert((*from_fp, to_fp), mask);
                    }
                }
            }
        }
        if profile {
            pf.enabled_info_count = enabled_infos.len();
            pf.print();
        }

        // Apply cached masks to action_masks.
        for (nd_idx, nd) in node_data.iter().enumerate() {
            let from_fp = nd.node.state_fp;
            for (succ_idx, succ) in nd.successors.iter().enumerate() {
                let to_fp = succ.state_fp;
                if let Some(mask) = fp_to_mask.get(&(from_fp, to_fp)) {
                    action_masks[nd_idx][succ_idx] = mask.clone();
                }
            }
        }

        // Write results into NodeInfo.
        for (nd_idx, nd) in node_data.iter().enumerate() {
            self.graph.update_node_info(&nd.node, |info| {
                info.state_check_mask = state_mask
                    .get(&nd.node.state_fp)
                    .cloned()
                    .unwrap_or_default();
                info.action_check_masks.clone_from(&action_masks[nd_idx]);
            })?;
        }

        Ok(())
    }

    /// Try to resolve a state check result from inline bitmask results.
    ///
    /// Returns `Some(bool)` if the check can be fully reconstructed from
    /// bitmask data, `None` if eval fallback is needed.
    fn try_reconstruct_state_check(
        inline_results: Option<InlineCheckResults<'_>>,
        fp: Fingerprint,
        check: &LiveExpr,
    ) -> Option<bool> {
        let results = inline_results?;
        let sbits = results.state_bitmasks.get_bits(&fp)?;
        // If all leaves are within inline range, reconstruct from bits.
        if Self::all_leaves_within_tag_range(check, 0, results.max_tag) {
            Some(ea_precompute_cache::reconstruct_check_from_tag_bits(
                check, sbits, 0,
            ))
        } else {
            None
        }
    }

    /// Multi-word variant of `try_reconstruct_state_check` for specs with >64 tags.
    ///
    /// Part of #4159: Future-ready path for multi-word bitmask reconstruction.
    /// Currently delegates to the u64 first-word path since `InlineCheckResults`
    /// uses `&dyn StateBitmaskLookup` (trait object, u64-only). When the SCC
    /// checker is updated to pass concrete `StateBitmaskMap` references, this
    /// method can use `reconstruct_check_from_bitmask` for full multi-word support.
    #[allow(dead_code)]
    fn try_reconstruct_state_check_bitmask(
        inline_results: Option<InlineCheckResults<'_>>,
        fp: Fingerprint,
        check: &LiveExpr,
    ) -> Option<bool> {
        // For now, delegate to the u64 first-word path.
        Self::try_reconstruct_state_check(inline_results, fp, check)
    }
}
