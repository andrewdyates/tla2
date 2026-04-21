// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(debug_assertions)]
use super::super::debug::debug_liveness_formula;
use super::super::debug::liveness_profile;
use super::super::{
    check_error_to_result, Arc, CheckResult, Expr, Fingerprint, FxHashMap, LiveExpr,
    LivenessChecker, ModelChecker, PropertySafetyParts, Spanned, State, SuccessorWitnessMap,
};
use crate::liveness::GroupedLivenessPlan;
use crate::storage::{ActionBitmaskMap, StateBitmaskMap, SuccessorGraph};
use crate::ConfigCheckError;
use tla_eval::tir::TirProgram;

mod explore;
mod fp_only;
mod results;

/// Bundled context for checking a liveness property.
///
/// Groups the cached state/successor/bitmask data that flows from
/// `run_liveness_properties` through `check_liveness_property` and its
/// callees, reducing the argument count below clippy's `too_many_arguments`
/// threshold.
pub(in crate::check::model_checker) struct LivenessPropertyCtx<'a> {
    pub init_fps: &'a [Fingerprint],
    pub cached_successors: &'a SuccessorGraph,
    pub state_cache: &'a Arc<FxHashMap<Fingerprint, State>>,
    pub state_fp_to_canon_fp: &'a Arc<FxHashMap<Fingerprint, Fingerprint>>,
    pub succ_witnesses: Option<&'a Arc<SuccessorWitnessMap>>,
    pub cross_state_bitmasks: &'a StateBitmaskMap,
    pub cross_action_bitmasks: &'a ActionBitmaskMap,
}

/// Resolved per-group state cache from `resolve_group_state_cache`.
pub(super) struct GroupResolution {
    pub(super) state_cache: Arc<FxHashMap<Fingerprint, State>>,
    pub(super) state_fp_to_canon_fp: Arc<FxHashMap<Fingerprint, Fingerprint>>,
    pub(super) no_tableau_fast_path: bool,
}

impl ModelChecker<'_> {
    fn property_definition_body(&self, prop_name: &str) -> Result<Spanned<Expr>, CheckResult> {
        self.module
            .op_defs
            .get(prop_name)
            .map(|def| def.body.clone())
            .ok_or_else(|| {
                check_error_to_result(
                    ConfigCheckError::MissingProperty(prop_name.to_string()).into(),
                    &self.stats,
                )
            })
    }

    fn separate_property_parts_with_profile(
        &mut self,
        prop_name: &str,
        body: &Spanned<Expr>,
    ) -> Option<(PropertySafetyParts, Option<Spanned<Expr>>)> {
        let split_start = if liveness_profile() {
            Some(std::time::Instant::now())
        } else {
            None
        };
        let (safety_parts, liveness_expr) = self.separate_safety_liveness_parts(prop_name, body)?;
        if let Some(start) = split_start {
            eprintln!(
                "  separate_safety_liveness_parts: {:.3}s (init_terms={}, always_terms={})",
                start.elapsed().as_secs_f64(),
                safety_parts.init_terms.len(),
                safety_parts.always_terms.len(),
            );
        }
        Some((safety_parts, liveness_expr))
    }

    fn check_property_safety_parts_with_profile(
        &mut self,
        prop_name: &str,
        safety_parts: &PropertySafetyParts,
        cached_successors: &SuccessorGraph,
        succ_witnesses: Option<&Arc<SuccessorWitnessMap>>,
    ) -> Option<CheckResult> {
        let safety_start = if liveness_profile() {
            Some(std::time::Instant::now())
        } else {
            None
        };
        let init_state_cache = self.liveness_cache.init_states.clone();
        let result = self.check_property_safety_parts(
            prop_name,
            safety_parts,
            &init_state_cache,
            cached_successors,
            succ_witnesses,
        );
        if let Some(start) = safety_start {
            let transition_count = cached_successors.total_successors();
            eprintln!(
                "  check_property_safety_parts: {:.3}s (transitions={})",
                start.elapsed().as_secs_f64(),
                transition_count,
            );
        }
        result
    }

    fn resolve_grouped_plans(
        &mut self,
        prop_name: &str,
        liveness_expr: &Spanned<Expr>,
    ) -> Result<(Vec<GroupedLivenessPlan>, u32), CheckResult> {
        if let Some(plan) = self.inline_property_plan(prop_name) {
            if liveness_profile() {
                let dnf_clause_count: usize = plan.grouped_plans.iter().map(|p| p.pems.len()).sum();
                eprintln!(
                    "[liveness] reusing inline grouped plans: {} groups, {} DNF clauses total",
                    plan.grouped_plans.len(),
                    dnf_clause_count
                );
            }
            Ok((plan.grouped_plans.clone(), plan.max_fairness_tag))
        } else {
            self.build_grouped_plans_for_property(prop_name, liveness_expr)
        }
    }

    fn resolve_group_state_cache(
        &mut self,
        prop_name: &str,
        plan: &GroupedLivenessPlan,
        max_fairness_tag: u32,
        ctx: &LivenessPropertyCtx<'_>,
    ) -> Result<GroupResolution, CheckResult> {
        let has_inline_results = self.inline_property_plan(prop_name).is_some()
            || !ctx.cross_state_bitmasks.is_empty()
            || !ctx.cross_action_bitmasks.is_empty();
        let max_inline_tag = self
            .inline_property_plan(prop_name)
            .map_or(max_fairness_tag, |plan| plan.max_cached_tag);
        let no_tableau_fast_path = matches!(&plan.tf, LiveExpr::Bool(true));
        let needs_full_state_cache = match self.liveness_mode {
            super::LivenessMode::FingerprintOnly { .. } => {
                !no_tableau_fast_path
                    || !fp_only::all_checks_structurally_cached(
                        plan,
                        max_fairness_tag,
                        max_inline_tag,
                        has_inline_results,
                    )
            }
            super::LivenessMode::Disabled | super::LivenessMode::FullState { .. } => false,
        };

        if needs_full_state_cache {
            let (state_cache, state_fp_to_canon_fp) =
                self.build_fp_only_liveness_state_cache(ctx.init_fps, ctx.cached_successors)?;
            Ok(GroupResolution {
                state_cache,
                state_fp_to_canon_fp,
                no_tableau_fast_path,
            })
        } else {
            Ok(GroupResolution {
                state_cache: Arc::clone(ctx.state_cache),
                state_fp_to_canon_fp: Arc::clone(ctx.state_fp_to_canon_fp),
                no_tableau_fast_path,
            })
        }
    }

    fn check_grouped_liveness_plan(
        &mut self,
        prop_name: &str,
        group_idx: usize,
        plan: &GroupedLivenessPlan,
        max_fairness_tag: u32,
        ctx: &LivenessPropertyCtx<'_>,
        tir: Option<&TirProgram>,
        checker: &mut LivenessChecker,
    ) -> Option<CheckResult> {
        if liveness_profile() {
            eprintln!(
                "[liveness] group {}: starting SCC + PEM checking...",
                group_idx + 1
            );
        }
        let check_start = std::time::Instant::now();
        let inline_results = if let Some(prop_plan) = self.inline_property_plan(prop_name) {
            Some(prop_plan.inline_results())
        } else if !ctx.cross_state_bitmasks.is_empty() || !ctx.cross_action_bitmasks.is_empty() {
            Some(crate::liveness::InlineCheckResults {
                max_tag: max_fairness_tag,
                state_bitmasks: ctx.cross_state_bitmasks,
                action_bitmasks: ctx.cross_action_bitmasks,
            })
        } else {
            None
        };
        let check_result = checker.check_liveness_grouped_with_inline_cache(
            plan,
            max_fairness_tag,
            inline_results,
            tir,
        );
        if liveness_profile() {
            crate::liveness::log_cache_stats();
        }
        checker.collect_cache_stats();
        if liveness_profile() {
            let stats = checker.stats();
            eprintln!(
                "[liveness cache] consistency: hits={}, misses={}",
                stats.consistency_cache_hits, stats.consistency_cache_misses
            );
            eprintln!(
                "[liveness cache] state_env: hits={}, misses={}",
                stats.state_env_cache_hits, stats.state_env_cache_misses
            );
            eprintln!(
                "[liveness] group {}: SCC done in {:.3}s",
                group_idx + 1,
                check_start.elapsed().as_secs_f64()
            );
            eprintln!(
                "  check_liveness_grouped time: {:.3}s",
                check_start.elapsed().as_secs_f64()
            );
        }
        self.map_liveness_result(prop_name, check_result)
    }

    /// Check a single liveness property
    ///
    /// Returns `Some(CheckResult)` if the property is violated, `None` if satisfied.
    ///
    /// Part of #3065: `state_cache` is `Arc`-wrapped for zero-copy sharing with
    /// the behavior graph on the fingerprint-based direct path. `init_fps` provides
    /// initial state fingerprints for the same path.
    pub(in crate::check::model_checker) fn check_liveness_property(
        &mut self,
        prop_name: &str,
        ctx: &LivenessPropertyCtx<'_>,
    ) -> Option<CheckResult> {
        let func_start = std::time::Instant::now();

        crate::liveness::clear_enabled_cache();
        if liveness_profile() {
            eprintln!("[liveness] check_liveness_property: starting '{prop_name}'");
        }

        let body = match self.property_definition_body(prop_name) {
            Ok(body) => body,
            Err(result) => return Some(result),
        };
        let (safety_parts, liveness_expr) =
            self.separate_property_parts_with_profile(prop_name, &body)?;
        if let Some(result) = self.check_property_safety_parts_with_profile(
            prop_name,
            &safety_parts,
            ctx.cached_successors,
            ctx.succ_witnesses,
        ) {
            return Some(result);
        }

        let liveness_expr = liveness_expr?;
        let (grouped_plans, max_fairness_tag) =
            match self.resolve_grouped_plans(prop_name, &liveness_expr) {
                Ok(result) => result,
                Err(check_result) => return Some(check_result),
            };

        let tir_modules = self
            .tir_parity
            .as_ref()
            .and_then(|tp| tp.clone_modules_for_selected_eval(prop_name));
        let tir = tir_modules.as_ref().map(|(root, deps)| {
            let dep_refs: Vec<&_> = deps.iter().collect();
            TirProgram::from_modules(root, &dep_refs)
        });

        for (group_idx, plan) in grouped_plans.iter().enumerate() {
            debug_eprintln!(
                debug_liveness_formula(),
                "[DEBUG] Starting grouped plan {} ({} PEMs)",
                group_idx,
                plan.pems.len()
            );

            let resolved =
                match self.resolve_group_state_cache(prop_name, plan, max_fairness_tag, ctx) {
                    Ok(result) => result,
                    Err(check_result) => return Some(check_result),
                };
            let mut checker = match self.explore_grouped_liveness_plan(
                group_idx,
                grouped_plans.len(),
                plan,
                ctx,
                &resolved,
                tir.as_ref(),
            ) {
                Ok(checker) => checker,
                Err(check_result) => return Some(check_result),
            };
            if let Some(result) = self.check_grouped_liveness_plan(
                prop_name,
                group_idx,
                plan,
                max_fairness_tag,
                ctx,
                tir.as_ref(),
                &mut checker,
            ) {
                return Some(result);
            }
        }

        if liveness_profile() {
            eprintln!(
                "Total check_liveness_property time: {:.3}s",
                func_start.elapsed().as_secs_f64()
            );
        }
        None
    }

    pub(in crate::check::model_checker) fn check_liveness_property_on_the_fly(
        &mut self,
        prop_name: &str,
    ) -> Option<CheckResult> {
        crate::liveness::clear_enabled_cache();
        if liveness_profile() {
            eprintln!("[liveness] on-the-fly check_liveness_property: starting '{prop_name}'");
        }

        let body = match self.property_definition_body(prop_name) {
            Ok(body) => body,
            Err(result) => return Some(result),
        };
        let (safety_parts, liveness_expr) =
            self.separate_property_parts_with_profile(prop_name, &body)?;
        if let Some(result) = self.check_property_safety_parts_on_the_fly(prop_name, &safety_parts)
        {
            return Some(result);
        }

        let liveness_expr = liveness_expr?;
        let (grouped_plans, max_fairness_tag) =
            match self.build_grouped_plans_for_property(prop_name, &liveness_expr) {
                Ok(result) => result,
                Err(check_result) => return Some(check_result),
            };

        let tir_modules = self
            .tir_parity
            .as_ref()
            .and_then(|tp| tp.clone_modules_for_selected_eval(prop_name));
        let tir = tir_modules.as_ref().map(|(root, deps)| {
            let dep_refs: Vec<&_> = deps.iter().collect();
            TirProgram::from_modules(root, &dep_refs)
        });

        for (group_idx, plan) in grouped_plans.iter().enumerate() {
            let mut checker = match self.explore_grouped_liveness_plan_on_the_fly(
                group_idx,
                grouped_plans.len(),
                plan,
                tir.as_ref(),
            ) {
                Ok(checker) => checker,
                Err(check_result) => return Some(check_result),
            };
            let check_result = checker.check_liveness_grouped_with_inline_cache(
                plan,
                max_fairness_tag,
                None,
                tir.as_ref(),
            );
            if liveness_profile() {
                crate::liveness::log_cache_stats();
            }
            checker.collect_cache_stats();
            if liveness_profile() {
                let stats = checker.stats();
                eprintln!(
                    "[liveness cache] consistency: hits={}, misses={}",
                    stats.consistency_cache_hits, stats.consistency_cache_misses
                );
                eprintln!(
                    "[liveness cache] state_env: hits={}, misses={}",
                    stats.state_env_cache_hits, stats.state_env_cache_misses
                );
            }
            if let Some(result) = self.map_liveness_result(prop_name, check_result) {
                return Some(result);
            }
        }

        None
    }
}
