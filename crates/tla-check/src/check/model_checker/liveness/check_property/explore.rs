// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! BFS/fingerprint-only exploration for grouped liveness plans.
//!
//! Extracted from `check_property.rs` (#3525) to keep both files under
//! the 500 LOC policy threshold.

use super::super::super::debug::liveness_profile;
use super::super::super::{
    check_error_to_result, Arc, ArrayState, CheckError, CheckResult, Fingerprint, LivenessChecker,
    ModelChecker, State,
};
use super::{GroupResolution, LivenessPropertyCtx};
use crate::error::EvalError;
use crate::liveness::GroupedLivenessPlan;
use crate::{ConfigCheckError, EvalCheckError, LivenessCheckError};
use rustc_hash::FxHashMap;
use tla_eval::tir::TirProgram;

impl ModelChecker<'_> {
    pub(in crate::check::model_checker::liveness) fn generate_liveness_successors_on_the_fly(
        &mut self,
        state: &State,
    ) -> Result<Vec<State>, CheckError> {
        let next_name = self
            .config
            .next
            .as_deref()
            .ok_or(ConfigCheckError::MissingNext)?;
        let successors = self.generate_successors(next_name, state)?;
        let registry = self.ctx.var_registry().clone();
        let current_arr = ArrayState::from_state(state, &registry);
        let mut filtered = Vec::with_capacity(successors.len() + 1);
        for successor in successors {
            let succ_arr = ArrayState::from_state(&successor, &registry);
            if self.check_state_constraints_array(&succ_arr)?
                && self.check_action_constraints_array(&current_arr, &succ_arr)?
            {
                filtered.push(successor);
            }
        }
        if self.exploration.stuttering_allowed {
            filtered.push(state.clone());
        }
        Ok(filtered)
    }

    pub(in crate::check::model_checker::liveness) fn build_on_the_fly_init_states(
        &self,
    ) -> Vec<State> {
        let registry = self.ctx.var_registry().clone();
        self.liveness_cache
            .init_states
            .iter()
            .map(|(_, arr)| arr.to_state(&registry))
            .collect()
    }

    pub(in crate::check::model_checker::liveness) fn explore_grouped_liveness_plan_on_the_fly(
        &mut self,
        group_idx: usize,
        grouped_plan_count: usize,
        plan: &GroupedLivenessPlan,
        tir: Option<&TirProgram>,
    ) -> Result<LivenessChecker, CheckResult> {
        if liveness_profile() {
            eprintln!(
                "[liveness] group {}/{}: on-the-fly exploration ({} PEMs, {} check_state, {} check_action)...",
                group_idx + 1,
                grouped_plan_count,
                plan.pems.len(),
                plan.check_state.len(),
                plan.check_action.len()
            );
        }

        let tableau = crate::liveness::Tableau::new(plan.tf.clone());
        // Estimate behavior-graph node count as (discovered states * tableau nodes)
        // for auto-disk detection on large multi-property liveness specs.
        let estimated_nodes = self.stats.states_found.checked_mul(tableau.len().max(1));
        let mut checker = match LivenessChecker::new_from_env_with_hint(
            tableau,
            self.ctx.clone(),
            estimated_nodes,
        ) {
            Ok(checker) => checker,
            Err(error) => {
                return Err(check_error_to_result(
                    LivenessCheckError::RuntimeFailure(format!(
                        "Failed to create on-the-fly liveness checker for group {}: {error}",
                        group_idx + 1
                    ))
                    .into(),
                    &self.stats,
                ));
            }
        };
        let init_states = self.build_on_the_fly_init_states();
        let stats = self.stats.clone();
        let needs_canonical_fp =
            self.compiled.cached_view_name.is_some() || !self.symmetry.perms.is_empty();
        let checker_ref = std::cell::RefCell::new(self);
        let mut state_fp_to_canon_fp: Option<FxHashMap<Fingerprint, Fingerprint>> =
            needs_canonical_fp.then(FxHashMap::default);
        let explore_start = std::time::Instant::now();
        let explore_result = {
            let mut get_successors = |state: &State| {
                checker_ref
                    .borrow_mut()
                    .generate_liveness_successors_on_the_fly(state)
                    .map_err(|error| match error {
                        CheckError::Eval(EvalCheckError::Eval(inner)) => inner,
                        other => EvalError::Internal {
                            message: format!(
                                "on-the-fly liveness successor generation failed: {other}"
                            ),
                            span: None,
                        },
                    })
            };
            let mut state_fp_of = |state: &State| -> Result<Fingerprint, EvalError> {
                if let Some(fp_map) = state_fp_to_canon_fp.as_mut() {
                    let raw_fp = state.fingerprint();
                    if let Some(&canon_fp) = fp_map.get(&raw_fp) {
                        return Ok(canon_fp);
                    }
                    let canon_fp =
                        checker_ref
                            .borrow_mut()
                            .state_fingerprint(state)
                            .map_err(|error| match error {
                                CheckError::Eval(EvalCheckError::Eval(inner)) => inner,
                                other => EvalError::Internal {
                                    message: format!(
                                    "on-the-fly liveness fingerprint generation failed: {other}"
                                ),
                                    span: None,
                                },
                            })?;
                    fp_map.insert(raw_fp, canon_fp);
                    Ok(canon_fp)
                } else {
                    Ok(state.fingerprint())
                }
            };

            if matches!(&plan.tf, crate::liveness::LiveExpr::Bool(true)) {
                checker.explore_state_graph_direct_with_state_fp(
                    &init_states,
                    &mut get_successors,
                    &mut state_fp_of,
                )
            } else {
                checker.explore_bfs_with_state_fp(
                    &init_states,
                    &mut get_successors,
                    tir,
                    &mut state_fp_of,
                )
            }
        };
        if let Err(error) = explore_result {
            return Err(check_error_to_result(
                EvalCheckError::Eval(error).into(),
                &stats,
            ));
        }
        if let Some(fp_map) = state_fp_to_canon_fp.filter(|map| !map.is_empty()) {
            checker.set_successor_maps(Arc::new(fp_map), None);
        }
        if liveness_profile() {
            // Part of #4083: log and collect thread-local cache stats before reporting.
            crate::liveness::log_cache_stats();
            checker.collect_cache_stats();
            let stats = checker.stats();
            eprintln!(
                "[liveness] group {}: on-the-fly explore {:.3}s ({} nodes, {} edges, {} checks)",
                group_idx + 1,
                explore_start.elapsed().as_secs_f64(),
                stats.graph_nodes,
                stats.graph_edges,
                stats.consistency_checks
            );
        }

        Ok(checker)
    }

    pub(in crate::check::model_checker::liveness) fn explore_grouped_liveness_plan(
        &mut self,
        group_idx: usize,
        grouped_plan_count: usize,
        plan: &GroupedLivenessPlan,
        ctx: &LivenessPropertyCtx<'_>,
        resolved: &GroupResolution,
        tir: Option<&TirProgram>,
    ) -> Result<LivenessChecker, CheckResult> {
        if liveness_profile() {
            eprintln!(
                "[liveness] group {}/{}: building tableau ({} PEMs, {} check_state, {} check_action)...",
                group_idx + 1,
                grouped_plan_count,
                plan.pems.len(),
                plan.check_state.len(),
                plan.check_action.len()
            );
        }
        let tableau_start = if liveness_profile() {
            Some(std::time::Instant::now())
        } else {
            None
        };
        let tableau = crate::liveness::Tableau::new(plan.tf.clone());
        if let Some(start) = tableau_start {
            eprintln!(
                "[liveness] group {}: tableau built in {:.3}s ({} nodes, {} init)",
                group_idx + 1,
                start.elapsed().as_secs_f64(),
                tableau.len(),
                tableau.init_count()
            );
        } else if liveness_profile() {
            eprintln!(
                "[liveness] group {}: tableau has {} nodes, {} init",
                group_idx + 1,
                tableau.len(),
                tableau.init_count()
            );
        }

        let ctx_start = if liveness_profile() {
            Some(std::time::Instant::now())
        } else {
            None
        };
        // Estimate behavior-graph node count as (discovered states * tableau nodes)
        // for auto-disk detection on large multi-property liveness specs.
        // Use self.stats.states_found (full BFS count) rather than
        // ctx.cached_successors.len() which may be incomplete.
        let estimated_nodes = self.stats.states_found.checked_mul(tableau.len().max(1));
        let mut checker = match LivenessChecker::new_from_env_with_hint(
            tableau,
            self.ctx.clone(),
            estimated_nodes,
        ) {
            Ok(checker) => checker,
            Err(error) => {
                return Err(check_error_to_result(
                    LivenessCheckError::RuntimeFailure(format!(
                        "Failed to create liveness checker for group {}: {error}",
                        group_idx + 1
                    ))
                    .into(),
                    &self.stats,
                ));
            }
        };
        if let Some(start) = ctx_start {
            eprintln!(
                "[liveness] group {}: checker created (ctx.clone) in {:.3}s",
                group_idx + 1,
                start.elapsed().as_secs_f64(),
            );
        }
        checker.set_successor_maps(
            Arc::clone(&resolved.state_fp_to_canon_fp),
            ctx.succ_witnesses.map(Arc::clone),
        );

        let add_stuttering = self.exploration.stuttering_allowed;
        let init_states = if resolved.no_tableau_fast_path {
            None
        } else {
            let init_state_materialize_start = std::time::Instant::now();
            let registry = self.ctx.var_registry().clone();
            let states: Vec<State> = self
                .liveness_cache
                .init_states
                .iter()
                .map(|(_, arr)| arr.to_state(&registry))
                .collect();
            if liveness_profile() {
                eprintln!(
                    "  init_states build:   {:.3}s ({} init states, tableau path)",
                    init_state_materialize_start.elapsed().as_secs_f64(),
                    states.len()
                );
            }
            Some(states)
        };
        let cached_successors = ctx.cached_successors;
        let group_state_cache = &resolved.state_cache;
        let group_state_fp_to_canon_fp = &resolved.state_fp_to_canon_fp;
        let mut get_successors = |state: &State| {
            let fp = self.state_fingerprint(state).map_err(|error| {
                if let CheckError::Eval(EvalCheckError::Eval(
                    inner @ EvalError::ExitRequested { .. },
                )) = error
                {
                    inner
                } else {
                    EvalError::Internal {
                        message: format!(
                            "VIEW fingerprint failed during liveness (BFS precondition violated): \
                             {error}"
                        ),
                        span: None,
                    }
                }
            })?;
            // Part of #4080: Use get_ref() to avoid cloning the entire Vec<Fingerprint>
            // on every lookup in the in-memory backend. Falls back to get() for disk.
            let owned_fallback;
            let succs_slice: Option<&[Fingerprint]> =
                if let Some(s) = cached_successors.get_ref(&fp) {
                    Some(s)
                } else {
                    owned_fallback = cached_successors.get(&fp);
                    owned_fallback.as_deref()
                };
            let mut succs: Vec<State> = succs_slice
                .map(|fps| {
                    fps.iter()
                        .filter_map(|sfp| group_state_cache.get(sfp).cloned())
                        .collect()
                })
                .unwrap_or_default();
            if add_stuttering && succs_slice.is_some() {
                succs.push(state.clone());
            }
            Ok(succs)
        };

        if liveness_profile() {
            eprintln!(
                "[liveness] group {}: starting {} ({} init states)...",
                group_idx + 1,
                if resolved.no_tableau_fast_path {
                    "explore_state_graph_direct_fp"
                } else {
                    "explore_bfs"
                },
                ctx.init_fps.len()
            );
        }
        let bfs_start = std::time::Instant::now();
        let explore_result = if resolved.no_tableau_fast_path {
            checker.set_behavior_graph_shared_cache(Arc::clone(&resolved.state_cache));
            let mut get_successor_fps = |fp: Fingerprint| -> Result<Vec<Fingerprint>, EvalError> {
                let canon_fp = group_state_fp_to_canon_fp.get(&fp).copied().unwrap_or(fp);
                let entry = cached_successors.get(&canon_fp);
                let has_entry = entry.is_some();
                let mut succs: Vec<Fingerprint> = entry.unwrap_or_default();
                if add_stuttering && has_entry {
                    succs.push(fp);
                }
                Ok(succs)
            };
            let result =
                checker.explore_state_graph_direct_fp(ctx.init_fps, &mut get_successor_fps);
            if let Err(error) = checker.populate_state_successor_fps_from_graph() {
                return Err(check_error_to_result(
                    LivenessCheckError::RuntimeFailure(format!(
                        "Failed to derive liveness successor fingerprints for group {}: {error}",
                        group_idx + 1
                    ))
                    .into(),
                    &self.stats,
                ));
            }
            result
        } else {
            checker.explore_bfs(
                init_states
                    .as_deref()
                    .expect("tableau explore_bfs path must materialize init states"),
                &mut get_successors,
                tir,
            )
        };
        if let Err(error) = explore_result {
            return Err(check_error_to_result(
                EvalCheckError::Eval(error).into(),
                &self.stats,
            ));
        }

        if liveness_profile() {
            // Part of #4083: collect thread-local cache stats before reporting.
            checker.collect_cache_stats();
            let stats = checker.stats();
            eprintln!(
                "[liveness] group {}: explore_bfs {:.3}s ({} nodes, {} edges, {} checks)",
                group_idx + 1,
                bfs_start.elapsed().as_secs_f64(),
                stats.graph_nodes,
                stats.graph_edges,
                stats.consistency_checks
            );
            eprintln!(
                "=== Liveness profiling (group {}/{}) ===",
                group_idx + 1,
                grouped_plan_count
            );
            eprintln!(
                "  init_state_time:     {:.3}s",
                stats.init_state_time_us as f64 / 1_000_000.0
            );
            eprintln!(
                "  state_clone_time:    {:.3}s",
                stats.state_clone_time_us as f64 / 1_000_000.0
            );
            eprintln!(
                "  get_successors_time: {:.3}s",
                stats.get_successors_time_us as f64 / 1_000_000.0
            );
            eprintln!(
                "  add_successors_time: {:.3}s",
                stats.add_successors_time_us as f64 / 1_000_000.0
            );
            eprintln!("  consistency_checks:  {}", stats.consistency_checks);
            eprintln!("  graph_nodes:         {}", stats.graph_nodes);
            eprintln!("  graph_edges:         {}", stats.graph_edges);
            eprintln!("  pems_in_group:       {}", plan.pems.len());
            // Part of #4083: cache hit/miss statistics
            let sub_total = stats.subscript_cache_hits + stats.subscript_cache_misses;
            let sub_rate = if sub_total > 0 {
                stats.subscript_cache_hits as f64 / sub_total as f64 * 100.0
            } else {
                0.0
            };
            eprintln!(
                "  subscript_cache:     {} hits / {} misses ({:.1}%), {} evictions",
                stats.subscript_cache_hits,
                stats.subscript_cache_misses,
                sub_rate,
                stats.subscript_cache_evictions
            );
            let en_total = stats.enabled_cache_hits + stats.enabled_cache_misses;
            let en_rate = if en_total > 0 {
                stats.enabled_cache_hits as f64 / en_total as f64 * 100.0
            } else {
                0.0
            };
            eprintln!(
                "  enabled_cache:       {} hits / {} misses ({:.1}%), {} evictions",
                stats.enabled_cache_hits,
                stats.enabled_cache_misses,
                en_rate,
                stats.enabled_cache_evictions
            );
            let cc_total = stats.consistency_cache_hits + stats.consistency_cache_misses;
            let cc_rate = if cc_total > 0 {
                stats.consistency_cache_hits as f64 / cc_total as f64 * 100.0
            } else {
                0.0
            };
            eprintln!(
                "  consistency_cache:   {} hits / {} misses ({:.1}%)",
                stats.consistency_cache_hits, stats.consistency_cache_misses, cc_rate
            );
            let se_total = stats.state_env_cache_hits + stats.state_env_cache_misses;
            let se_rate = if se_total > 0 {
                stats.state_env_cache_hits as f64 / se_total as f64 * 100.0
            } else {
                0.0
            };
            eprintln!(
                "  state_env_cache:     {} hits / {} misses ({:.1}%)",
                stats.state_env_cache_hits, stats.state_env_cache_misses, se_rate
            );
            eprintln!("===================================");
        }

        Ok(checker)
    }
}
