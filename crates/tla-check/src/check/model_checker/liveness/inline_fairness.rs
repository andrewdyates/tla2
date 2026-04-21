// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

pub(in crate::check::model_checker) use super::inline_fairness_enabled::EnabledActionGroup;
pub(in crate::check::model_checker) use super::inline_fairness_enabled::EnabledProvenanceEntry;
use super::inline_fairness_enabled::{
    build_action_provenance_from_hints, build_enabled_provenance, extract_enabled_action_groups,
    log_inline_fairness_stats,
};
use super::inline_helpers::collect_live_leaves;
#[cfg(test)]
use super::inline_record::{record_missing_action_results, record_missing_state_results};
use super::subscript_action_pair::extract_subscript_action_pairs;
pub(in crate::check::model_checker) use super::subscript_action_pair::SubscriptActionPair;
use crate::check::model_checker::ModelChecker;
use crate::liveness::AstToLive;
use rustc_hash::FxHashSet;

impl<'a> ModelChecker<'a> {
    pub(in crate::check::model_checker) fn inline_fairness_active(&self) -> bool {
        let mode_supports_inline = match self.liveness_mode {
            super::LivenessMode::Disabled => false,
            // VIEW is NOT safe for inline liveness: VIEW collapses distinct
            // states to the same fingerprint, but inline bitmasks record
            // per-original-state leaf evaluations keyed by fingerprint.
            // When two original states map to the same VIEW fingerprint,
            // only one bitmask entry survives (last writer wins),
            // corrupting downstream SCC checks and causing false positive
            // liveness violations (observed on EWD998ChanID).
            // Symmetry is also NOT safe: inline recording sees pre-permutation
            // states while post-BFS sees canonical permuted states.
            super::LivenessMode::FullState {
                symmetry: false,
                view: false,
            } => true,
            super::LivenessMode::FullState { .. } => false,
            super::LivenessMode::FingerprintOnly { view: false } => true,
            super::LivenessMode::FingerprintOnly { view: true } => false,
        };

        self.liveness_cache.cache_for_liveness
            && mode_supports_inline
            && self.liveness_cache.fairness_max_tag > 0
            && (!self.liveness_cache.fairness_state_checks.is_empty()
                || !self.liveness_cache.fairness_action_checks.is_empty())
    }

    pub(in crate::check::model_checker) fn prepare_inline_fairness_cache(&mut self) {
        self.liveness_cache.fairness_state_checks.clear();
        self.liveness_cache.fairness_action_checks.clear();
        self.liveness_cache.action_provenance_tags.clear();
        self.liveness_cache.action_fast_path_provenance_tags.clear();
        self.liveness_cache.enabled_action_groups.clear();
        self.liveness_cache.enabled_provenance.clear();
        self.liveness_cache.subscript_action_pairs.clear();
        // Bitmask maps cleared below (per-tag inline_state/action_results removed).
        self.liveness_cache.inline_state_bitmasks.clear();
        self.liveness_cache.inline_action_bitmasks.clear();
        self.liveness_cache.fairness_max_tag = 0;
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
        if self.liveness_cache.fairness.is_empty() {
            return;
        }
        let converter = AstToLive::new().with_location_module_name(self.module.root_name.as_str());
        let mut fairness_exprs = Vec::with_capacity(self.liveness_cache.fairness.len());
        for constraint in &self.liveness_cache.fairness {
            let Ok(expr) = self.fairness_to_live_expr(constraint, &converter) else {
                return;
            };
            fairness_exprs.push(expr);
        }

        let max_tag = converter.next_tag().saturating_sub(1);
        if max_tag == 0 {
            return;
        }

        let mut seen_state_tags = FxHashSet::default();
        let mut seen_action_tags = FxHashSet::default();
        let mut state_checks = Vec::new();
        let mut action_checks = Vec::new();
        for expr in &fairness_exprs {
            collect_live_leaves(
                expr,
                &mut state_checks,
                &mut action_checks,
                &mut seen_state_tags,
                &mut seen_action_tags,
            );
        }

        // Part of #3100: Extract ENABLED-to-action tag groups for the WF
        // disjunction short-circuit.
        let mut enabled_groups = Vec::new();
        for expr in &fairness_exprs {
            extract_enabled_action_groups(expr, &mut enabled_groups);
        }

        // Part of #3100: Extract subscript-action pairs for the LNAction-style
        // short-circuit. When StateChanged(v) is false for transition (s, s'),
        // the paired ActionPred(A) can be skipped because <<A>>_v = false.
        let mut subscript_pairs = Vec::new();
        for expr in &fairness_exprs {
            extract_subscript_action_pairs(expr, &mut subscript_pairs);
        }

        // Build action provenance tags: split_action index → [fairness ActionPred tags].
        let hints = converter.take_action_pred_hints();
        if let Some(ref meta) = self.compiled.split_action_meta {
            let (provenance_tags, fast_path_provenance_tags) =
                build_action_provenance_from_hints(&hints, meta, &action_checks);
            self.liveness_cache.action_provenance_tags = provenance_tags;
            self.liveness_cache.action_fast_path_provenance_tags = fast_path_provenance_tags;
        } else {
            self.liveness_cache.action_provenance_tags.clear();
            self.liveness_cache.action_fast_path_provenance_tags.clear();
        }

        // Build ENABLED provenance — connect ENABLED tags to split_action indices.
        let enabled_provenance = build_enabled_provenance(
            &enabled_groups,
            &state_checks,
            &self.liveness_cache.action_fast_path_provenance_tags,
        );

        log_inline_fairness_stats(
            &state_checks,
            &action_checks,
            self.liveness_cache.action_provenance_tags.len(),
            self.liveness_cache.action_fast_path_provenance_tags.len(),
            &enabled_groups,
            subscript_pairs.len(),
            max_tag,
            &enabled_provenance,
        );

        // Bitmask-only recording requires all tags fit in a u64 (< 64).
        if max_tag >= 64 {
            eprintln!(
                "Warning: liveness spec has {} fairness tags (max supported: 63). \
                 Inline bitmask recording requires tags < 64. Falling back to \
                 evaluator-backed liveness checking.",
                max_tag
            );
            return;
        }

        self.liveness_cache.fairness_state_checks = state_checks;
        self.liveness_cache.fairness_action_checks = action_checks;
        self.liveness_cache.fairness_max_tag = max_tag;
        self.liveness_cache.enabled_action_groups = enabled_groups;
        self.liveness_cache.enabled_provenance = enabled_provenance;
        self.liveness_cache.subscript_action_pairs = subscript_pairs;

        // Part of #3992: Try to compile fairness predicates for JIT-accelerated
        // evaluation during BFS inline liveness recording.
        #[cfg(feature = "jit")]
        self.try_compile_liveness_batch();
    }

    #[cfg(test)]
    pub(in crate::check::model_checker) fn record_inline_fairness_results(
        &mut self,
        current_fp: crate::check::model_checker::Fingerprint,
        current_array: &crate::state::ArrayState,
        successors: &[(
            crate::state::ArrayState,
            crate::check::model_checker::Fingerprint,
        )],
    ) -> Result<(), crate::check::CheckError> {
        if !self.inline_fairness_active() {
            return Ok(());
        }

        record_missing_state_results(
            &mut self.ctx,
            &self.liveness_cache.fairness_state_checks,
            &mut self.liveness_cache.inline_state_bitmasks,
            self.exploration.stuttering_allowed,
            current_fp,
            current_array,
            successors,
            None, // Test path does not use compiled batch
        )?;

        // Part of #3100: ENABLED-based action skip (WF disjunction short-circuit).
        // Read from state bitmask (record_missing_state_results just ran).
        if !self.liveness_cache.enabled_action_groups.is_empty() {
            let state_bits = self
                .liveness_cache
                .inline_state_bitmasks
                .get(&current_fp)
                .unwrap_or(0);
            for group in &self.liveness_cache.enabled_action_groups {
                let enabled =
                    group.enabled_tag < 64 && state_bits & (1u64 << group.enabled_tag) != 0;
                if !enabled {
                    // Action not enabled -> ensure transition entries exist (all false = 0 bits).
                    for (_, succ_fp) in successors {
                        self.liveness_cache
                            .inline_action_bitmasks
                            .get_or_insert_default((current_fp, *succ_fp));
                    }
                    if self.exploration.stuttering_allowed {
                        self.liveness_cache
                            .inline_action_bitmasks
                            .get_or_insert_default((current_fp, current_fp));
                    }
                }
            }
        }

        if self.liveness_cache.fairness_action_checks.is_empty() {
            return Ok(());
        }

        for (succ_array, succ_fp) in successors {
            record_missing_action_results(
                &mut self.ctx,
                &self.liveness_cache.fairness_action_checks,
                &mut self.liveness_cache.inline_action_bitmasks,
                current_fp,
                current_array,
                *succ_fp,
                succ_array,
                None, // Test path does not use compiled batch
            )?;
        }

        if self.exploration.stuttering_allowed {
            record_missing_action_results(
                &mut self.ctx,
                &self.liveness_cache.fairness_action_checks,
                &mut self.liveness_cache.inline_action_bitmasks,
                current_fp,
                current_array,
                current_fp,
                current_array,
                None, // Test path does not use compiled batch
            )?;
        }

        Ok(())
    }
}
