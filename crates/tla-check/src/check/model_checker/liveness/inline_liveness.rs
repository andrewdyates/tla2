// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::inline_helpers::collect_live_leaves;
use super::inline_record::{record_missing_action_results, record_missing_state_results};
use crate::check::model_checker::{Fingerprint, ModelChecker};
use crate::check::CheckError;
use crate::eval::EvalCtx;
use crate::liveness::{AstToLive, GroupedLivenessPlan, LiveExpr, LivenessChecker};
use crate::state::ArrayState;
use crate::storage::{ActionBitmaskMap, StateBitmaskMap};
use rustc_hash::FxHashSet;
use std::io;

pub(crate) struct InlineLivenessPropertyPlan {
    pub(crate) property: String,
    pub(crate) grouped_plans: Vec<GroupedLivenessPlan>,
    pub(in crate::check::model_checker) max_fairness_tag: u32,
    pub(in crate::check::model_checker) max_cached_tag: u32,
    pub(super) state_leaves: Vec<LiveExpr>,
    pub(super) action_leaves: Vec<LiveExpr>,
    /// Bitmask-only state results. Bit `tag` set when true. FP presence = all tags evaluated.
    /// Part of #3177: uses the same backend selection as fairness-level caches so
    /// property-scoped inline recording stays memory-bounded when disk bitmasks are enabled.
    pub(super) state_bitmasks: StateBitmaskMap,
    /// Bitmask-only action results. Bit `tag` set when true. Key presence = all tags evaluated.
    /// Part of #3177: uses the same backend selection as fairness-level caches so
    /// property-scoped inline recording stays memory-bounded when disk bitmasks are enabled.
    pub(super) action_bitmasks: ActionBitmaskMap,
}

impl InlineLivenessPropertyPlan {
    fn new_state_bitmasks() -> StateBitmaskMap {
        if crate::liveness::debug::use_disk_bitmasks() {
            StateBitmaskMap::disk().expect("disk state bitmask map creation failed")
        } else {
            StateBitmaskMap::default()
        }
    }

    fn new_action_bitmasks() -> ActionBitmaskMap {
        if crate::liveness::debug::use_disk_bitmasks() {
            ActionBitmaskMap::disk().expect("disk action bitmask map creation failed")
        } else {
            ActionBitmaskMap::default()
        }
    }

    fn new(
        property: String,
        grouped_plans: Vec<GroupedLivenessPlan>,
        max_fairness_tag: u32,
        max_cached_tag: u32,
        state_leaves: Vec<LiveExpr>,
        action_leaves: Vec<LiveExpr>,
    ) -> Self {
        Self {
            property,
            grouped_plans,
            max_fairness_tag,
            max_cached_tag,
            state_leaves,
            action_leaves,
            state_bitmasks: Self::new_state_bitmasks(),
            action_bitmasks: Self::new_action_bitmasks(),
        }
    }

    pub(super) fn inline_results(&self) -> crate::liveness::InlineCheckResults<'_> {
        crate::liveness::InlineCheckResults {
            max_tag: self.max_cached_tag,
            state_bitmasks: &self.state_bitmasks,
            action_bitmasks: &self.action_bitmasks,
        }
    }

    pub(super) fn maybe_flush(&mut self) -> io::Result<()> {
        self.state_bitmasks.maybe_flush()?;
        self.action_bitmasks.maybe_flush()?;
        Ok(())
    }

    pub(super) fn record_results(
        &mut self,
        ctx: &mut EvalCtx,
        stuttering_allowed: bool,
        current_fp: Fingerprint,
        current_array: &ArrayState,
        successors: &[(ArrayState, Fingerprint)],
    ) -> Result<(), CheckError> {
        self.record_state_results(
            ctx,
            stuttering_allowed,
            current_fp,
            current_array,
            successors,
        )?;

        if self.action_leaves.is_empty() {
            return Ok(());
        }

        for (next_array, next_fp) in successors {
            self.record_action_results_for_transition(
                ctx,
                current_fp,
                current_array,
                *next_fp,
                next_array,
            )?;
        }

        if stuttering_allowed {
            self.record_action_results_for_transition(
                ctx,
                current_fp,
                current_array,
                current_fp,
                current_array,
            )?;
        }

        Ok(())
    }

    fn record_state_results(
        &mut self,
        ctx: &mut EvalCtx,
        stuttering_allowed: bool,
        current_fp: Fingerprint,
        current_array: &ArrayState,
        successors: &[(ArrayState, Fingerprint)],
    ) -> Result<(), CheckError> {
        record_missing_state_results(
            ctx,
            &self.state_leaves,
            &mut self.state_bitmasks,
            stuttering_allowed,
            current_fp,
            current_array,
            successors,
        )
    }

    fn record_action_results_for_transition(
        &mut self,
        ctx: &mut EvalCtx,
        current_fp: Fingerprint,
        current_array: &ArrayState,
        next_fp: Fingerprint,
        next_array: &ArrayState,
    ) -> Result<(), CheckError> {
        // Property-level plans don't have a skip bitmask.
        record_missing_action_results(
            ctx,
            &self.action_leaves,
            &mut self.action_bitmasks,
            current_fp,
            current_array,
            next_fp,
            next_array,
            None,
        )
    }
}

/// Collect all unique leaf expressions from grouped liveness plans.
fn collect_all_plan_leaves(
    plans: &[crate::liveness::GroupedLivenessPlan],
) -> (Vec<LiveExpr>, Vec<LiveExpr>) {
    let mut state_leaves = Vec::new();
    let mut action_leaves = Vec::new();
    let mut seen_state_tags = FxHashSet::default();
    let mut seen_action_tags = FxHashSet::default();
    for plan in plans {
        for expr in &plan.check_state {
            collect_live_leaves(
                expr,
                &mut state_leaves,
                &mut action_leaves,
                &mut seen_state_tags,
                &mut seen_action_tags,
            );
        }
        for expr in &plan.check_action {
            collect_live_leaves(
                expr,
                &mut state_leaves,
                &mut action_leaves,
                &mut seen_state_tags,
                &mut seen_action_tags,
            );
        }
    }
    (state_leaves, action_leaves)
}

/// Part of #3100: Check if all collected leaves are covered by the shared
/// fairness inline cache (tags ≤ max_fairness_tag). When true, per-property
/// inline recording is redundant — the bitmask caches provide all data
/// needed for the FAST PATH in `populate_node_check_masks_with_inline_cache`.
fn all_leaves_covered_by_fairness(
    state_leaves: &[LiveExpr],
    action_leaves: &[LiveExpr],
    max_fairness_tag: u32,
) -> bool {
    if max_fairness_tag == 0 {
        return false;
    }
    let tag_in_range = |leaf: &LiveExpr| {
        leaf.tag()
            .is_some_and(|tag| tag > 0 && tag <= max_fairness_tag)
    };
    state_leaves.iter().all(tag_in_range) && action_leaves.iter().all(tag_in_range)
}

impl ModelChecker<'_> {
    pub(in crate::check::model_checker) fn inline_liveness_active(&self) -> bool {
        self.inline_fairness_active() || !self.liveness_cache.inline_property_plans.is_empty()
    }

    pub(in crate::check::model_checker) fn prepare_inline_liveness_cache(&mut self) {
        self.prepare_inline_fairness_cache();
        self.liveness_cache.inline_property_plans.clear();

        let mode_supports_inline = match self.liveness_mode {
            super::LivenessMode::Disabled => false,
            super::LivenessMode::FullState {
                symmetry: false,
                view: false,
            } => true,
            super::LivenessMode::FullState { .. } => false,
            super::LivenessMode::FingerprintOnly { view: false } => true,
            super::LivenessMode::FingerprintOnly { view: true } => false,
        };
        if !self.liveness_cache.cache_for_liveness || !mode_supports_inline {
            return;
        }

        for prop_name in &self.config.properties {
            if let Some(plan) = self.build_inline_property_plan(prop_name) {
                self.liveness_cache.inline_property_plans.push(plan);
            }
        }
    }
    pub(in crate::check::model_checker) fn inline_property_plan(
        &self,
        prop_name: &str,
    ) -> Option<&InlineLivenessPropertyPlan> {
        self.liveness_cache
            .inline_property_plans
            .iter()
            .find(|plan| plan.property == prop_name)
    }

    fn build_inline_property_plan(&self, prop_name: &str) -> Option<InlineLivenessPropertyPlan> {
        let name = prop_name.to_string();
        if self.compiled.promoted_property_invariants.contains(&name)
            || self
                .compiled
                .promoted_implied_action_properties
                .contains(&name)
        {
            return None;
        }

        let def = self.module.op_defs.get(prop_name)?;
        let (_safety_parts, liveness_expr) =
            self.separate_safety_liveness_parts(prop_name, &def.body)?;
        let liveness_expr = liveness_expr?;

        let converter = AstToLive::new().with_location_module_name(self.module.root_name.as_str());
        let mut fairness_exprs: Vec<LiveExpr> =
            Vec::with_capacity(self.liveness_cache.fairness.len());
        for constraint in &self.liveness_cache.fairness {
            let Ok(expr) = self.fairness_to_live_expr(constraint, &converter) else {
                return None;
            };
            fairness_exprs.push(expr);
        }
        let max_fairness_tag = converter.next_tag().saturating_sub(1);

        let Ok(prop_live) = converter.convert(&self.ctx, &liveness_expr) else {
            return None;
        };

        // Part of #4159: max_tag >= 64 gate removed — LiveBitmask supports
        // arbitrary tag counts via SmallVec<[u64; 1]>.
        let _max_tag = converter.next_tag().saturating_sub(1);

        let negated_prop = LiveExpr::not(prop_live).push_negation();
        if crate::checker_ops::is_trivially_unsatisfiable(&negated_prop) {
            return None;
        }

        let formula = if fairness_exprs.is_empty() {
            negated_prop
        } else {
            fairness_exprs.push(negated_prop);
            LiveExpr::and(fairness_exprs).push_negation()
        };
        let grouped_plans = LivenessChecker::from_formula_grouped(&formula).ok()?;

        let (state_leaves, action_leaves) = collect_all_plan_leaves(&grouped_plans);

        // Part of #3100: Skip per-property inline recording when all leaves
        // are fairness-derived. See `all_leaves_covered_by_fairness`.
        if all_leaves_covered_by_fairness(&state_leaves, &action_leaves, max_fairness_tag) {
            return None;
        }

        Some(InlineLivenessPropertyPlan::new(
            prop_name.to_string(),
            grouped_plans,
            max_fairness_tag,
            converter.next_tag().saturating_sub(1),
            state_leaves,
            action_leaves,
        ))
    }
}
