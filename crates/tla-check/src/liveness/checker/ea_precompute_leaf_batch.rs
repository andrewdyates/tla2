// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Leaf batching helpers for EA check-mask precompute (#2399).

use super::check_mask::CheckMask;
use super::ea_precompute_profile::PopulateMasksProfile;
use super::live_expr::LiveExpr;
use super::{LivenessChecker, TirProgram};
use crate::error::EvalError;
use crate::liveness::inline_leaf_eval::eval_state_leaves_with_array_successors;
use crate::state::{ArrayState, Fingerprint, State};
use rustc_hash::{FxHashMap, FxHashSet};

pub(super) struct ActionLeafBatchPlan<'a> {
    pub(super) state_leaves: Vec<&'a LiveExpr>,
    pub(super) action_leaves: Vec<&'a LiveExpr>,
}

impl<'a> ActionLeafBatchPlan<'a> {
    pub(super) fn from_checks(check_action: &'a [LiveExpr], action_used: &[bool]) -> Option<Self> {
        let mut state_leaves = Vec::new();
        let mut action_leaves = Vec::new();
        let mut seen_state_tags = FxHashSet::default();
        let mut seen_action_tags = FxHashSet::default();

        for (check_idx, check) in check_action.iter().enumerate() {
            if !action_used.get(check_idx).copied().unwrap_or(false) {
                continue;
            }
            if !collect_action_check_leaves(
                check,
                &mut state_leaves,
                &mut action_leaves,
                &mut seen_state_tags,
                &mut seen_action_tags,
            ) {
                return None;
            }
        }

        Some(Self {
            state_leaves,
            action_leaves,
        })
    }
}

fn collect_action_check_leaves<'a>(
    expr: &'a LiveExpr,
    state_leaves: &mut Vec<&'a LiveExpr>,
    action_leaves: &mut Vec<&'a LiveExpr>,
    seen_state_tags: &mut FxHashSet<u32>,
    seen_action_tags: &mut FxHashSet<u32>,
) -> bool {
    match expr {
        LiveExpr::Bool(_) => true,
        LiveExpr::StatePred { tag, .. } | LiveExpr::Enabled { tag, .. } => {
            if seen_state_tags.insert(*tag) {
                state_leaves.push(expr);
            }
            true
        }
        LiveExpr::ActionPred { tag, .. } | LiveExpr::StateChanged { tag, .. } => {
            if seen_action_tags.insert(*tag) {
                action_leaves.push(expr);
            }
            true
        }
        LiveExpr::Not(inner) => collect_action_check_leaves(
            inner,
            state_leaves,
            action_leaves,
            seen_state_tags,
            seen_action_tags,
        ),
        LiveExpr::And(parts) | LiveExpr::Or(parts) => parts.iter().all(|part| {
            collect_action_check_leaves(
                part,
                state_leaves,
                action_leaves,
                seen_state_tags,
                seen_action_tags,
            )
        }),
        LiveExpr::Always(_) | LiveExpr::Eventually(_) | LiveExpr::Next(_) => false,
    }
}

fn reconstruct_check_from_masks(
    expr: &LiveExpr,
    state_tags: &CheckMask,
    action_tags: &CheckMask,
) -> bool {
    match expr {
        LiveExpr::Bool(value) => *value,
        LiveExpr::StatePred { tag, .. } | LiveExpr::Enabled { tag, .. } => {
            state_tags.get(*tag as usize)
        }
        LiveExpr::ActionPred { tag, .. } | LiveExpr::StateChanged { tag, .. } => {
            action_tags.get(*tag as usize)
        }
        LiveExpr::Not(inner) => !reconstruct_check_from_masks(inner, state_tags, action_tags),
        LiveExpr::And(parts) => parts
            .iter()
            .all(|part| reconstruct_check_from_masks(part, state_tags, action_tags)),
        LiveExpr::Or(parts) => parts
            .iter()
            .any(|part| reconstruct_check_from_masks(part, state_tags, action_tags)),
        LiveExpr::Always(_) | LiveExpr::Eventually(_) | LiveExpr::Next(_) => false,
    }
}

pub(super) fn try_populate_action_masks_from_leaf_batches(
    checker: &mut LivenessChecker,
    check_action: &[LiveExpr],
    action_used: &[bool],
    unique_states: &FxHashMap<Fingerprint, State>,
    by_from: &FxHashMap<Fingerprint, Vec<(Fingerprint, usize, usize)>>,
    fp_to_mask: &mut FxHashMap<(Fingerprint, Fingerprint), CheckMask>,
    pf: &mut PopulateMasksProfile,
    tir: Option<&TirProgram<'_>>,
) -> Result<bool, EvalError> {
    if checker.succ_witnesses.is_some() || checker.ctx.var_registry().is_empty() {
        return Ok(false);
    }

    let Some(leaf_plan) = ActionLeafBatchPlan::from_checks(check_action, action_used) else {
        return Ok(false);
    };

    let registry = checker.ctx.var_registry().clone();
    let unique_arrays: FxHashMap<Fingerprint, ArrayState> = unique_states
        .iter()
        .map(|(fp, state)| (*fp, ArrayState::from_state(state, &registry)))
        .collect();
    pf.enabled_info_count = leaf_plan
        .state_leaves
        .iter()
        .filter(|leaf| matches!(leaf, LiveExpr::Enabled { .. }))
        .count();

    for (from_fp, transitions) in by_from {
        let state_leaf_mask = if leaf_plan.state_leaves.is_empty() {
            CheckMask::new()
        } else {
            // Part of #3746: from_fp should always be in unique_arrays
            // (only nodes with cached states are in node_data), but guard
            // defensively against parallel-mode cache misses.
            let Some(from_array) = unique_arrays.get(from_fp) else {
                return Ok(false);
            };
            // Part of #3735: When successor fps from state_successor_fps are
            // not found in unique_arrays, bail out to the regular eval path
            // instead of returning a hard error. This can happen when the
            // behavior graph contains successor edges to states whose
            // concrete data is not available in the shared state cache.
            // The regular eval fallback path handles missing successors
            // gracefully via successor_states_for_enabled() (mod.rs:337-358).
            let state_successors: Vec<(&ArrayState, Fingerprint)> =
                if let Some(fps) = checker.state_successor_fps.get(from_fp) {
                    let mut v = Vec::with_capacity(fps.len());
                    for succ_fp in fps.iter() {
                        match unique_arrays.get(succ_fp) {
                            Some(array) => v.push((array, *succ_fp)),
                            None => return Ok(false),
                        }
                    }
                    v
                } else if let Some(succs) = checker.state_successors.get(from_fp) {
                    let mut v = Vec::with_capacity(succs.len());
                    for succ in succs.iter() {
                        let succ_fp = succ.fingerprint();
                        match unique_arrays.get(&succ_fp) {
                            Some(array) => v.push((array, succ_fp)),
                            None => return Ok(false),
                        }
                    }
                    v
                } else {
                    Vec::new()
                };
            let results = eval_state_leaves_with_array_successors(
                &mut checker.ctx,
                &leaf_plan.state_leaves,
                *from_fp,
                from_array,
                &state_successors,
            )?;
            let mut mask = CheckMask::new();
            for &(tag, result) in &results {
                if result {
                    mask.set(tag as usize);
                }
            }
            mask
        };

        // Part of #3746: from_fp should always be in unique_states (only nodes
        // with successfully cached states are included in node_data), but guard
        // against missing source states in parallel mode by skipping.
        let Some(from_state) = unique_states.get(from_fp) else {
            continue;
        };
        let current_values = from_state.to_values(&registry);
        let _state_guard = checker.ctx.bind_state_array_guard(&current_values);
        for &(to_fp, _, _) in transitions {
            pf.fresh_eval_transitions += 1;
            // Part of #3746: skip transitions whose destination state is
            // missing from the cache (parallel/fingerprint-only mode).
            let Some(to_state) = unique_states.get(&to_fp) else {
                fp_to_mask.insert((*from_fp, to_fp), CheckMask::new());
                continue;
            };
            let cached_next_env = checker.get_cached_env(to_state);
            let next_values = to_state.to_values(&registry);
            let _next_state_guard = checker.ctx.take_next_state_guard();
            let _next_guard = checker.ctx.take_next_state_env_guard();
            *checker.ctx.next_state_mut() = Some(cached_next_env);
            checker.ctx.bind_next_state_array(&next_values);

            let action_leaf_mask = if leaf_plan.action_leaves.is_empty() {
                CheckMask::new()
            } else {
                let mut mask = CheckMask::new();
                for leaf in &leaf_plan.action_leaves {
                    if let Some(tag) = leaf.tag() {
                        if checker.eval_live_check_expr_inner(
                            leaf,
                            from_state,
                            Some(to_state),
                            tir,
                        )? {
                            mask.set(tag as usize);
                        }
                    }
                }
                mask
            };

            let mut mask = CheckMask::new();
            for (check_idx, check) in check_action.iter().enumerate() {
                if !action_used.get(check_idx).copied().unwrap_or(false) {
                    continue;
                }
                if reconstruct_check_from_masks(check, &state_leaf_mask, &action_leaf_mask) {
                    mask.set(check_idx);
                }
            }

            fp_to_mask.insert((*from_fp, to_fp), mask);
        }
    }

    Ok(true)
}
