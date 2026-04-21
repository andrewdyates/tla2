// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! On-the-fly post-BFS liveness checking for the parallel checker.
//!
//! This mirrors the sequential on-the-fly `PROPERTY` path: safety buckets are
//! checked directly on regenerated successors, and the temporal remainder is
//! explored with the liveness checker using on-demand successor generation.

use super::*;

use crate::check::{CheckError, PropertyViolationKind, Trace};
use crate::error::EvalError;
use crate::liveness::{AstToLive, LiveExpr, LivenessChecker, LivenessResult, Tableau};
use crate::{EvalCheckError, LivenessCheckError, Value};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::VecDeque;

impl ParallelChecker {
    pub(super) fn run_on_the_fly_liveness(
        &self,
        ctx: &mut EvalCtx,
        stats: &CheckStats,
        promoted_properties: &[String],
        partial_graph: bool,
        root_name: &str,
    ) -> Option<CheckResult> {
        if partial_graph {
            return None;
        }

        crate::eval::clear_for_phase_boundary();
        for prop_name in &self.config.properties {
            if promoted_properties.contains(prop_name) {
                continue;
            }
            if let Some(result) =
                self.check_single_property_on_the_fly(ctx, stats, root_name, prop_name)
            {
                return Some(result);
            }
        }

        None
    }

    fn check_single_property_on_the_fly(
        &self,
        ctx: &mut EvalCtx,
        stats: &CheckStats,
        root_name: &str,
        prop_name: &str,
    ) -> Option<CheckResult> {
        crate::liveness::clear_enabled_cache();

        let planned = match self.split_property_terms_for_liveness(ctx, stats, prop_name) {
            Ok(planned) => planned,
            Err(result) => return Some(result),
        };
        if let Some(result) = self.check_safety_temporal_terms_on_the_fly(
            ctx,
            stats,
            prop_name,
            &planned.init_terms,
            &planned.always_state_terms,
            &planned.always_action_terms,
        ) {
            return Some(result);
        }
        let Some(liveness_expr) = planned.liveness_expr else {
            return None;
        };

        let converter = AstToLive::new().with_location_module_name(root_name);
        let mut fairness_exprs: Vec<LiveExpr> = Vec::new();
        for constraint in &self.fairness {
            match crate::checker_ops::fairness_to_live_expr(
                constraint,
                &self.op_defs,
                ctx,
                &converter,
            ) {
                Ok(expr) => fairness_exprs.push(expr),
                Err(error) => {
                    return Some(check_error_to_result(
                        LivenessCheckError::RuntimeFailure(format!(
                            "Failed to process fairness for property '{prop_name}': {error}"
                        ))
                        .into(),
                        stats,
                    ));
                }
            }
        }
        let max_fairness_tag = converter.next_tag().saturating_sub(1);

        let prop_live = match converter.convert(ctx, &liveness_expr) {
            Ok(live) => live,
            Err(error) => {
                return Some(check_error_to_result(
                    LivenessCheckError::RuntimeFailure(format!(
                        "Failed to convert property '{prop_name}' to liveness formula: {error}"
                    ))
                    .into(),
                    stats,
                ));
            }
        };
        let negated = LiveExpr::not(prop_live).push_negation();
        if crate::checker_ops::is_trivially_unsatisfiable(&negated) {
            return Some(check_error_to_result(
                LivenessCheckError::FormulaTautology {
                    property: prop_name.to_string(),
                }
                .into(),
                stats,
            ));
        }

        let formula = if fairness_exprs.is_empty() {
            negated
        } else {
            fairness_exprs.push(negated);
            LiveExpr::and(fairness_exprs).push_negation()
        };
        let grouped_plans = match LivenessChecker::from_formula_grouped(&formula) {
            Ok(plans) => plans,
            Err(error) => {
                return Some(check_error_to_result(
                    LivenessCheckError::RuntimeFailure(format!(
                        "Failed to create liveness checker for '{prop_name}': {error}"
                    ))
                    .into(),
                    stats,
                ));
            }
        };

        for plan in &grouped_plans {
            if let Some(result) =
                self.run_plan_group_on_the_fly(ctx, stats, prop_name, plan, max_fairness_tag)
            {
                return Some(result);
            }
        }

        None
    }

    fn build_on_the_fly_init_states(&self) -> Vec<State> {
        self.liveness_init_states
            .iter()
            .map(|entry| entry.value().to_state(&self.var_registry))
            .collect()
    }

    fn resolve_on_the_fly_next_def<'a>(
        &'a self,
        ctx: &EvalCtx,
        stats: &CheckStats,
    ) -> Result<&'a OperatorDef, CheckResult> {
        let next_name =
            self.config.next.as_deref().ok_or_else(|| {
                check_error_to_result(ConfigCheckError::MissingNext.into(), stats)
            })?;
        let resolved_next_name = ctx.resolve_op_name(next_name);
        self.op_defs
            .get(resolved_next_name)
            .ok_or_else(|| check_error_to_result(ConfigCheckError::MissingNext.into(), stats))
    }

    fn prepare_on_the_fly_fingerprinting(
        &self,
        ctx: &EvalCtx,
        stats: &CheckStats,
    ) -> Result<(Option<String>, Vec<crate::value::MVPerm>), CheckResult> {
        let cached_view_name = crate::checker_ops::validate_view_operator(ctx, &self.config);
        let mvperms = if self.config.symmetry.is_some() {
            let perms = crate::check::compute_symmetry_perms(ctx, &self.config)
                .map_err(|error| check_error_to_result(error, stats))?;
            perms
                .iter()
                .map(crate::value::MVPerm::from_func_value)
                .collect::<Result<Vec<_>, _>>()
                .map_err(|error| check_error_to_result(EvalCheckError::Eval(error).into(), stats))?
        } else {
            Vec::new()
        };
        Ok((cached_view_name, mvperms))
    }

    fn state_fingerprint_on_the_fly(
        &self,
        ctx: &mut EvalCtx,
        state: &State,
        cached_view_name: Option<&str>,
        mvperms: &[crate::value::MVPerm],
    ) -> Result<Fingerprint, CheckError> {
        if let Some(view_name) = cached_view_name {
            return crate::checker_ops::compute_view_fingerprint(
                ctx,
                state,
                view_name,
                ctx.get_tlc_level(),
            );
        }
        if !mvperms.is_empty() {
            return Ok(state.fingerprint_with_symmetry_fast(mvperms));
        }
        Ok(state.fingerprint())
    }

    fn generate_liveness_successors_on_the_fly(
        &self,
        ctx: &mut EvalCtx,
        next_def: &OperatorDef,
        state: &State,
    ) -> Result<Vec<State>, CheckError> {
        let _scope_guard = ctx.scope_guard();
        for (name, value) in state.vars() {
            ctx.bind_mut(Arc::clone(name), value.clone());
        }

        let current_arr = ArrayState::from_state(state, &self.var_registry);
        let successors = crate::enumerate::enumerate_successors(ctx, next_def, state, &self.vars)
            .map_err(|error| EvalCheckError::Eval(error))?;
        let mut filtered = Vec::with_capacity(successors.len() + 1);
        for successor in successors {
            let succ_arr = ArrayState::from_state(&successor, &self.var_registry);
            let passes_constraints = crate::checker_ops::check_constraints_for_successor_array(
                ctx,
                &self.config.constraints,
                &self.config.action_constraints,
                &current_arr,
                &succ_arr,
            )?;
            if passes_constraints {
                filtered.push(successor);
            }
        }
        if self.stuttering_allowed {
            filtered.push(state.clone());
        }
        Ok(filtered)
    }

    fn check_safety_temporal_terms_on_the_fly(
        &self,
        ctx: &mut EvalCtx,
        stats: &CheckStats,
        prop_name: &str,
        init_terms: &[tla_core::Spanned<tla_core::ast::Expr>],
        always_state_terms: &[tla_core::Spanned<tla_core::ast::Expr>],
        always_action_terms: &[tla_core::Spanned<tla_core::ast::Expr>],
    ) -> Option<CheckResult> {
        for entry in self.liveness_init_states.iter() {
            let init_array = entry.value();
            let _scope_guard = ctx.scope_guard_with_next_state();
            *ctx.next_state_mut() = None;
            let _next_env_guard = ctx.take_next_state_env_guard();
            let _state_guard = ctx.bind_state_env_guard(init_array.env_ref());
            crate::eval::clear_for_bound_state_eval_scope(ctx);

            for term in init_terms {
                let value = match crate::eval::eval_entry(ctx, term) {
                    Ok(value) => value,
                    Err(error) => {
                        return Some(check_error_to_result(
                            EvalCheckError::Eval(error).into(),
                            stats,
                        ));
                    }
                };
                match value {
                    Value::Bool(true) => {}
                    Value::Bool(false) => {
                        let trace =
                            Trace::from_states(vec![init_array.to_state(&self.var_registry)]);
                        return Some(CheckResult::PropertyViolation {
                            property: prop_name.to_string(),
                            kind: PropertyViolationKind::StateLevel,
                            trace,
                            stats: stats.clone(),
                        });
                    }
                    _ => {
                        return Some(check_error_to_result(
                            EvalCheckError::PropertyNotBoolean(prop_name.to_string()).into(),
                            stats,
                        ));
                    }
                }
            }
        }

        if always_state_terms.is_empty() && always_action_terms.is_empty() {
            return None;
        }

        let next_def = match self.resolve_on_the_fly_next_def(ctx, stats) {
            Ok(next_def) => next_def,
            Err(result) => return Some(result),
        };
        let (cached_view_name, mvperms) = match self.prepare_on_the_fly_fingerprinting(ctx, stats) {
            Ok(result) => result,
            Err(result) => return Some(result),
        };

        let mut seen = FxHashSet::default();
        let mut fp_cache: Option<FxHashMap<Fingerprint, Fingerprint>> =
            (cached_view_name.is_some() || !mvperms.is_empty()).then(FxHashMap::default);
        let mut queue = VecDeque::new();
        for state in self.build_on_the_fly_init_states() {
            let state_fp = {
                let raw_fp = state.fingerprint();
                if let Some(cache) = fp_cache.as_mut() {
                    if let Some(&canon_fp) = cache.get(&raw_fp) {
                        canon_fp
                    } else {
                        let canon_fp = match self.state_fingerprint_on_the_fly(
                            ctx,
                            &state,
                            cached_view_name.as_deref(),
                            &mvperms,
                        ) {
                            Ok(fp) => fp,
                            Err(error) => return Some(check_error_to_result(error, stats)),
                        };
                        cache.insert(raw_fp, canon_fp);
                        canon_fp
                    }
                } else {
                    raw_fp
                }
            };
            if seen.insert(state_fp) {
                queue.push_back(state);
            }
        }

        while let Some(from_state) = queue.pop_front() {
            let from_fp = {
                let raw_fp = from_state.fingerprint();
                if let Some(cache) = fp_cache.as_mut() {
                    if let Some(&canon_fp) = cache.get(&raw_fp) {
                        canon_fp
                    } else {
                        let canon_fp = match self.state_fingerprint_on_the_fly(
                            ctx,
                            &from_state,
                            cached_view_name.as_deref(),
                            &mvperms,
                        ) {
                            Ok(fp) => fp,
                            Err(error) => return Some(check_error_to_result(error, stats)),
                        };
                        cache.insert(raw_fp, canon_fp);
                        canon_fp
                    }
                } else {
                    raw_fp
                }
            };
            let from_arr = ArrayState::from_state(&from_state, &self.var_registry);

            if !always_state_terms.is_empty() {
                let _scope_guard = ctx.scope_guard_with_next_state();
                *ctx.next_state_mut() = None;
                let _next_env_guard = ctx.take_next_state_env_guard();
                let _state_guard = ctx.bind_state_env_guard(from_arr.env_ref());
                crate::eval::clear_for_bound_state_eval_scope(ctx);

                for term in always_state_terms {
                    let value = match crate::eval::eval_entry(ctx, term) {
                        Ok(value) => value,
                        Err(error) => {
                            return Some(check_error_to_result(
                                EvalCheckError::Eval(error).into(),
                                stats,
                            ));
                        }
                    };
                    match value {
                        Value::Bool(true) => {}
                        Value::Bool(false) => {
                            let trace = Trace::from_states(vec![from_state.clone()]);
                            return Some(CheckResult::PropertyViolation {
                                property: prop_name.to_string(),
                                kind: PropertyViolationKind::StateLevel,
                                trace,
                                stats: stats.clone(),
                            });
                        }
                        _ => {
                            return Some(check_error_to_result(
                                EvalCheckError::PropertyNotBoolean(prop_name.to_string()).into(),
                                stats,
                            ));
                        }
                    }
                }
            }

            let successors =
                match self.generate_liveness_successors_on_the_fly(ctx, next_def, &from_state) {
                    Ok(successors) => successors,
                    Err(error) => return Some(check_error_to_result(error, stats)),
                };

            if always_action_terms.is_empty() {
                for succ_state in successors {
                    let succ_fp = {
                        let raw_fp = succ_state.fingerprint();
                        if let Some(cache) = fp_cache.as_mut() {
                            if let Some(&canon_fp) = cache.get(&raw_fp) {
                                canon_fp
                            } else {
                                let canon_fp = match self.state_fingerprint_on_the_fly(
                                    ctx,
                                    &succ_state,
                                    cached_view_name.as_deref(),
                                    &mvperms,
                                ) {
                                    Ok(fp) => fp,
                                    Err(error) => return Some(check_error_to_result(error, stats)),
                                };
                                cache.insert(raw_fp, canon_fp);
                                canon_fp
                            }
                        } else {
                            raw_fp
                        }
                    };
                    if seen.insert(succ_fp) {
                        queue.push_back(succ_state);
                    }
                }
                continue;
            }

            let _scope_guard = ctx.scope_guard_with_next_state();
            let _state_guard = ctx.bind_state_env_guard(from_arr.env_ref());
            *ctx.next_state_mut() = None;
            let _outer_next_env_guard = ctx.take_next_state_env_guard();

            for succ_state in successors {
                let succ_fp = {
                    let raw_fp = succ_state.fingerprint();
                    if let Some(cache) = fp_cache.as_mut() {
                        if let Some(&canon_fp) = cache.get(&raw_fp) {
                            canon_fp
                        } else {
                            let canon_fp = match self.state_fingerprint_on_the_fly(
                                ctx,
                                &succ_state,
                                cached_view_name.as_deref(),
                                &mvperms,
                            ) {
                                Ok(fp) => fp,
                                Err(error) => return Some(check_error_to_result(error, stats)),
                            };
                            cache.insert(raw_fp, canon_fp);
                            canon_fp
                        }
                    } else {
                        raw_fp
                    }
                };
                let succ_arr = ArrayState::from_state(&succ_state, &self.var_registry);
                let _inner_next_guard = ctx.bind_next_state_env_guard(succ_arr.env_ref());
                crate::eval::clear_for_state_boundary();

                for term in always_action_terms {
                    let value = match crate::eval::eval_entry(ctx, term) {
                        Ok(value) => value,
                        Err(error) => {
                            return Some(check_error_to_result(
                                EvalCheckError::Eval(error).into(),
                                stats,
                            ));
                        }
                    };
                    match value {
                        Value::Bool(true) => {}
                        Value::Bool(false) => {
                            if from_fp == succ_fp {
                                continue;
                            }
                            let trace =
                                Trace::from_states(vec![from_state.clone(), succ_state.clone()]);
                            return Some(CheckResult::PropertyViolation {
                                property: prop_name.to_string(),
                                kind: PropertyViolationKind::ActionLevel,
                                trace,
                                stats: stats.clone(),
                            });
                        }
                        _ => {
                            return Some(check_error_to_result(
                                EvalCheckError::PropertyNotBoolean(prop_name.to_string()).into(),
                                stats,
                            ));
                        }
                    }
                }

                if seen.insert(succ_fp) {
                    queue.push_back(succ_state);
                }
            }
        }

        None
    }

    fn run_plan_group_on_the_fly(
        &self,
        ctx: &mut EvalCtx,
        stats: &CheckStats,
        prop_name: &str,
        plan: &crate::liveness::GroupedLivenessPlan,
        max_fairness_tag: u32,
    ) -> Option<CheckResult> {
        let tableau = Tableau::new(plan.tf.clone());
        let mut checker = match LivenessChecker::new_from_env(tableau, ctx.clone()) {
            Ok(checker) => checker,
            Err(error) => {
                return Some(check_error_to_result(
                    LivenessCheckError::RuntimeFailure(format!(
                        "Failed to create on-the-fly liveness checker for '{prop_name}': {error}"
                    ))
                    .into(),
                    stats,
                ));
            }
        };
        let next_def = match self.resolve_on_the_fly_next_def(ctx, stats) {
            Ok(next_def) => next_def.clone(),
            Err(result) => return Some(result),
        };
        let (cached_view_name, mvperms) = match self.prepare_on_the_fly_fingerprinting(ctx, stats) {
            Ok(result) => result,
            Err(result) => return Some(result),
        };

        let init_states = self.build_on_the_fly_init_states();
        let needs_canonical_fp = cached_view_name.is_some() || !mvperms.is_empty();
        let mut state_fp_to_canon_fp: Option<FxHashMap<Fingerprint, Fingerprint>> =
            needs_canonical_fp.then(FxHashMap::default);
        let mut successor_ctx = ctx.clone();
        let mut fingerprint_ctx = ctx.clone();
        let explore_result = {
            let mut get_successors = |state: &State| {
                self.generate_liveness_successors_on_the_fly(&mut successor_ctx, &next_def, state)
                    .map_err(|error| match error {
                        CheckError::Eval(EvalCheckError::Eval(inner)) => inner,
                        other => EvalError::Internal {
                            message: format!(
                                "parallel on-the-fly liveness successor generation failed: {other}"
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
                    let canon_fp = self.state_fingerprint_on_the_fly(
                        &mut fingerprint_ctx,
                        state,
                        cached_view_name.as_deref(),
                        &mvperms,
                    )
                    .map_err(|error| match error {
                        CheckError::Eval(EvalCheckError::Eval(inner)) => inner,
                        other => EvalError::Internal {
                            message: format!(
                                "parallel on-the-fly liveness fingerprint generation failed: {other}"
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

            if matches!(&plan.tf, LiveExpr::Bool(true)) {
                checker.explore_state_graph_direct_with_state_fp(
                    &init_states,
                    &mut get_successors,
                    &mut state_fp_of,
                )
            } else {
                checker.explore_bfs_with_state_fp(
                    &init_states,
                    &mut get_successors,
                    None,
                    &mut state_fp_of,
                )
            }
        };
        if let Err(error) = explore_result {
            return Some(check_error_to_result(
                EvalCheckError::Eval(error).into(),
                stats,
            ));
        }
        if let Some(fp_map) = state_fp_to_canon_fp.filter(|map| !map.is_empty()) {
            checker.set_successor_maps(Arc::new(fp_map), None);
        }

        match checker.check_liveness_grouped(plan, max_fairness_tag) {
            LivenessResult::Satisfied => None,
            LivenessResult::Violated { prefix, cycle } => {
                let prefix_states: Vec<State> = prefix.into_iter().map(|(state, _)| state).collect();
                let mut cycle_states: Vec<State> = cycle.into_iter().map(|(state, _)| state).collect();
                if cycle_states.len() >= 2 {
                    cycle_states.push(cycle_states[0].clone());
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
                let prefix_trace =
                    Trace::from_states_with_labels(prefix_states, full_labels[..prefix_len].to_vec());
                let cycle_trace =
                    Trace::from_states_with_labels(cycle_states, full_labels[prefix_len..].to_vec());

                Some(CheckResult::LivenessViolation {
                    property: prop_name.to_string(),
                    prefix: prefix_trace,
                    cycle: cycle_trace,
                    stats: stats.clone(),
                })
            }
            LivenessResult::ViolatedFingerprints { .. } => Some(check_error_to_result(
                LivenessCheckError::RuntimeFailure(format!(
                    "parallel on-the-fly liveness unexpectedly returned fingerprint-only counterexample data for '{prop_name}'"
                ))
                .into(),
                stats,
            )),
            LivenessResult::RuntimeFailure { reason } => Some(check_error_to_result(
                LivenessCheckError::RuntimeFailure(format!(
                    "On-the-fly liveness runtime failure for '{prop_name}': {reason}"
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
}
