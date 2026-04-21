// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing control accessors and scheduling predicates.

use super::*;

/// Generate `set_*_enabled()`, `is_*_enabled()`, and `*_stats()` accessors
/// for inprocessing techniques. All scheduling state lives in `self.inproc_ctrl`.
///
/// Techniques with non-standard stats (factor: by-value, decompose: field access)
/// are kept manual below the macro invocation.
macro_rules! inprocessing_accessors {
    ($(
        $ctrl:ident,
        $(#[$set_attr:meta])*
        $set_vis:vis $set_fn:ident,
        $(#[$is_attr:meta])*
        $is_vis:vis $is_fn:ident,
        $(#[$stats_attr:meta])*
        $stats_vis:vis $stats_fn:ident -> $stats_ty:ty, $engine:ident
    );+ $(;)?) => {$(
        #[doc = "Enable or disable this inprocessing technique."]
        $(#[$set_attr])*
        $set_vis fn $set_fn(&mut self, enabled: bool) {
            self.inproc_ctrl.$ctrl.enabled = enabled;
        }
        #[doc = "Returns whether this inprocessing technique is enabled."]
        $(#[$is_attr])*
        $is_vis fn $is_fn(&self) -> bool {
            self.inproc_ctrl.$ctrl.enabled
        }
        #[doc = "Get cumulative statistics for this inprocessing technique."]
        $(#[$stats_attr])*
        $stats_vis fn $stats_fn(&self) -> &$stats_ty {
            self.inproc.$engine.stats()
        }
    )+};
}

/// Generate `should_*()` scheduling predicates using `self.inproc_ctrl`.
macro_rules! should_inprocess {
    ($fn_name:ident, $ctrl:ident) => {
        pub(in crate::solver) fn $fn_name(&self) -> bool {
            self.inproc_ctrl.$ctrl.should_fire(self.num_conflicts)
        }
    };
}

impl Solver {
    // ======== Macro-generated inprocessing accessors (#3546) ========
    //
    // Each technique gets: `set_*_enabled(bool)` + `is_*_enabled()` + `*_stats()`.
    // Exceptions kept manual: factor_stats (by-value), decompose_stats (field access).
    inprocessing_accessors! {
        vivify, pub set_vivify_enabled, pub is_vivify_enabled,
            pub vivify_stats -> VivifyStats, vivifier;
        subsume, pub set_subsume_enabled, pub is_subsume_enabled,
            pub subsume_stats -> SubsumeStats, subsumer;
        probe, pub set_probe_enabled, pub is_probe_enabled,
            pub probe_stats -> ProbeStats, prober;
        bve, pub set_bve_enabled, pub is_bve_enabled,
            pub bve_stats -> BVEStats, bve;
        bce, pub set_bce_enabled, pub is_bce_enabled,
            pub bce_stats -> BCEStats, bce;
        transred, pub set_transred_enabled, pub is_transred_enabled,
            pub transred_stats -> crate::transred::TransRedStats, transred_engine;
        htr, pub set_htr_enabled, pub is_htr_enabled,
            pub htr_stats -> HTRStats, htr;
        gate, pub set_gate_enabled, pub is_gate_enabled,
            pub gate_stats -> GateStats, gate_extractor;
        congruence, pub set_congruence_enabled, pub is_congruence_enabled,
            pub congruence_stats -> crate::congruence::CongruenceStats, congruence;
        sweep, pub set_sweep_enabled, pub is_sweep_enabled,
            pub sweep_stats -> SweepStats, sweeper;
        cce, pub set_cce_enabled, pub is_cce_enabled,
            pub cce_stats -> crate::cce::CCEStats, cce
    }

    // Conditioning: manual accessors.
    /// Enable or disable conditioning inprocessing.
    pub fn set_condition_enabled(&mut self, enabled: bool) {
        self.inproc_ctrl.condition.enabled = enabled;
    }
    /// Returns whether conditioning inprocessing is enabled.
    pub fn is_condition_enabled(&self) -> bool {
        self.inproc_ctrl.condition.enabled
    }
    /// Get cumulative statistics for conditioning (GBCE).
    #[doc(hidden)]
    pub fn conditioning_stats(&self) -> &crate::condition::ConditioningStats {
        self.inproc.conditioning.stats()
    }

    // Non-standard stats: keep manual.
    /// Get decompose statistics.
    pub fn decompose_stats(&self) -> &crate::decompose::DecomposeStats {
        &self.inproc.decompose_engine.stats
    }
    /// Get factorization statistics (constructed from solver fields).
    pub fn factor_stats(&self) -> FactorStats {
        FactorStats {
            rounds: self.cold.factor_rounds,
            factored_count: self.cold.factor_factored_total,
            extension_vars: self.cold.factor_extension_vars_total,
        }
    }

    // Additional setters/getters for techniques with non-standard stats.
    /// Enable or disable factorization inprocessing.
    pub fn set_factor_enabled(&mut self, enabled: bool) {
        self.inproc_ctrl.factor.enabled = enabled;
    }
    /// Enable or disable SCC decomposition inprocessing.
    pub fn set_decompose_enabled(&mut self, enabled: bool) {
        self.inproc_ctrl.decompose.enabled = enabled;
    }
    /// Returns whether factorization inprocessing is enabled.
    #[cfg(test)]
    pub(crate) fn is_factor_enabled(&self) -> bool {
        self.inproc_ctrl.factor.enabled
    }
    /// Returns whether SCC decomposition inprocessing is enabled.
    #[cfg(test)]
    pub(crate) fn is_decompose_enabled(&self) -> bool {
        self.inproc_ctrl.decompose.enabled
    }
    /// Returns whether hyper-binary resolution is enabled during probing.
    pub fn is_hbr_enabled(&self) -> bool {
        self.hbr_enabled
    }
    /// Returns whether clause shrinking (vivification) is enabled.
    pub fn is_shrink_enabled(&self) -> bool {
        self.shrink_enabled
    }
    /// Enable or disable hyper-binary resolution during probing.
    pub fn set_hbr_enabled(&mut self, enabled: bool) {
        self.hbr_enabled = enabled;
    }
    /// Enable or disable backbone literal computation.
    pub fn set_backbone_enabled(&mut self, enabled: bool) {
        self.inproc_ctrl.backbone.enabled = enabled;
    }
    /// Returns whether backbone literal computation is enabled.
    pub fn is_backbone_enabled(&self) -> bool {
        self.inproc_ctrl.backbone.enabled
    }
    /// Enable or disable Kissat-style clause-weighted VMTF queue reorder.
    pub fn set_reorder_enabled(&mut self, enabled: bool) {
        self.inproc_ctrl.reorder.enabled = enabled;
    }

    /// Returns whether Kissat-style clause-weighted VMTF queue reorder is enabled.
    pub fn is_reorder_enabled(&self) -> bool {
        self.inproc_ctrl.reorder.enabled
    }

    /// Disable all inprocessing techniques.
    ///
    /// For ephemeral solver instances (e.g., CHC DPLL(T) checks) where the solver
    /// is created fresh for each query, inprocessing is pure overhead: reductions
    /// don't carry over and the problems are typically small. This also eliminates
    /// noisy diagnostic output (CONDITIONING round messages) from repeated solves.
    pub fn disable_all_inprocessing(&mut self) {
        self.inproc_ctrl.vivify.enabled = false;
        self.inproc_ctrl.vivify_irred.enabled = false;
        self.inproc_ctrl.subsume.enabled = false;
        self.inproc_ctrl.probe.enabled = false;
        self.inproc_ctrl.bve.enabled = false;
        self.inproc_ctrl.bce.enabled = false;
        self.inproc_ctrl.condition.enabled = false;
        self.inproc_ctrl.decompose.enabled = false;
        self.inproc_ctrl.factor.enabled = false;
        self.inproc_ctrl.transred.enabled = false;
        self.inproc_ctrl.htr.enabled = false;
        self.inproc_ctrl.gate.enabled = false;
        self.inproc_ctrl.congruence.enabled = false;
        self.inproc_ctrl.sweep.enabled = false;
        self.inproc_ctrl.backbone.enabled = false;
        self.inproc_ctrl.cce.enabled = false;
        self.inproc_ctrl.reorder.enabled = false;
    }

    /// Enable or disable block-level shrinking in conflict analysis.
    pub fn set_shrink_enabled(&mut self, enabled: bool) {
        self.shrink_enabled = enabled;
    }

    // ======== Destructive inprocessing guard (#5031, #3662) ========

    /// Permanently disable destructive inprocessing techniques.
    ///
    /// Called when the solver enters incremental mode (push/pop) or when a
    /// second solve() is performed on the same instance (#5031, #3662).
    /// Destructive techniques (conditioning, BVE, BCE, sweep, congruence,
    /// factorize, decompose) rewrite the clause database in ways that cannot
    /// be reversed across solve boundaries or push/pop scopes.
    ///
    /// Sets `has_been_incremental` which is checked by each destructive
    /// technique's entry function. Does NOT modify `inproc_ctrl.*.enabled`
    /// flags, preserving the user-facing feature profile (#5166).
    pub fn disable_destructive_inprocessing(&mut self) {
        self.cold.has_been_incremental = true;
    }

    // ======== Inprocessing precondition helpers (#5074) ========

    /// Level-0 precondition check shared by all inprocessing entry points.
    ///
    /// Asserts (in debug) that the solver is at decision level 0 and returns
    /// `false` in release builds when the precondition is violated, allowing
    /// callers to bail out with their own return convention (`return;` or
    /// `return false;`).
    #[inline]
    pub(super) fn require_level_zero(&self) -> bool {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: inprocessing at decision level {}",
            self.decision_level,
        );
        self.decision_level == 0
    }

    /// Combined inprocessing entry guard: level-0 check + reason mark sync.
    ///
    /// Most inprocessing techniques need both `require_level_zero()` and
    /// `ensure_reason_clause_marks_current()` at entry. This method combines
    /// them into a single call to reduce boilerplate.
    ///
    /// Techniques that call `ensure_reason_clause_marks_current()` later
    /// (e.g., congruence, factorize) or not at all (e.g., probe, backbone)
    /// should continue using `require_level_zero()` directly.
    #[inline]
    pub(super) fn enter_inprocessing(&mut self) -> bool {
        if !self.require_level_zero() {
            return false;
        }
        self.ensure_reason_clause_marks_current();
        true
    }

    // ======== Adaptive tick-threshold scaling (#8099) ========

    /// Adaptive tick-threshold scaling factor (#8099).
    ///
    /// When the measured per-round inprocessing overhead (rebuild_watches,
    /// sort_all_binary_first, trail re-propagation) is low, techniques
    /// benefit from more frequent firing because the cost of entering an
    /// inprocessing round is small. Returns a factor in `(0, 1]` that is
    /// multiplied into tick thresholds.
    ///
    /// Currently conservative: returns 1.0 unless overhead drops below 2ms,
    /// which would indicate incremental state maintenance (other #8092
    /// issues) is active and effective. This function will become more
    /// aggressive as incremental maintenance lands.
    #[inline]
    pub(in crate::solver) fn adaptive_tick_scale(&self) -> f64 {
        let overhead = self.cold.last_inprocessing_overhead_ms;
        if overhead > 0.0 && overhead < 2.0 {
            0.5
        } else {
            1.0
        }
    }

    // ======== Scheduling predicates (#3546) ========
    //
    // Standard: uses TechniqueControl::should_fire(num_conflicts).
    // Exceptions kept manual: should_vivify (dual schedule), should_bve (fixpoint guard).
    should_inprocess!(should_subsume, subsume);
    should_inprocess!(should_probe, probe);
    should_inprocess!(should_bce, bce);
    should_inprocess!(should_transred, transred);
    should_inprocess!(should_condition, condition);
    should_inprocess!(should_congruence, congruence);
    should_inprocess!(should_decompose, decompose);
    should_inprocess!(should_cce, cce);
    should_inprocess!(should_reorder, reorder);

    /// Check if we should run vivification (dual schedule: learned + irredundant,
    /// with CaDiCaL-style tick-threshold gating).
    pub(in crate::solver) fn should_vivify(&self) -> bool {
        self.vivify_skip_reason().is_none()
    }

    #[inline]
    pub(in crate::solver) fn should_vivify_learned(&self) -> bool {
        self.num_conflicts >= self.inproc_ctrl.vivify.next_conflict
    }

    /// Check if we should run irredundant vivification
    #[inline]
    pub(in crate::solver) fn should_vivify_irred(&self) -> bool {
        self.inproc_ctrl.vivify.enabled
            && self.num_conflicts >= self.inproc_ctrl.vivify_irred.next_conflict
    }

    #[inline]
    fn floor_log10(mut value: usize) -> u64 {
        let mut log = 0_u64;
        while value >= 10 {
            value /= 10;
            log += 1;
        }
        log
    }

    /// Evaluate the factor pass skip reason with CaDiCaL-style delay and
    /// mark-watermark gates.
    pub(in crate::solver) fn factor_skip_reason(&self) -> Option<FactorSkipReason> {
        let control = &self.inproc_ctrl.factor;
        if !control.enabled {
            return Some(FactorSkipReason::DisabledFlag);
        }
        if self.num_conflicts < control.next_conflict {
            return Some(FactorSkipReason::IntervalNotDue);
        }

        // CaDiCaL factor.cpp: delay gate based on active vars and elimination rounds.
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed());
        let active_log10 = Self::floor_log10(active_vars);
        let delay_limit = u64::from(self.cold.bve_phases) + FACTOR_DELAY;
        if active_log10 > delay_limit {
            return Some(FactorSkipReason::DelayGuard);
        }

        // CaDiCaL limit.hpp:136-164 + factor.cpp:961-964:
        // later factor rounds require enough accumulated search ticks relative
        // to the current clause database. The first round skips this threshold
        // and uses FACTOR_INIT_TICKS instead.
        // Adaptive scaling (#8099): when inprocessing overhead is low, lower
        // the threshold so factorization fires more frequently.
        if self.cold.factor_rounds > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_factor_ticks);
            let base_threshold = FACTOR_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(FactorSkipReason::ThresholdDelay);
            }
        }

        // CaDiCaL factor.cpp: skip if no new factor marks since last completed pass.
        if self.cold.factor_last_completed_epoch >= self.cold.factor_marked_epoch {
            return Some(FactorSkipReason::NoNewMarks);
        }

        None
    }

    /// Evaluate the HTR pass skip reason with a CaDiCaL-style tick-threshold delay.
    pub(in crate::solver) fn htr_skip_reason(&self) -> Option<HtrSkipReason> {
        let control = &self.inproc_ctrl.htr;
        if !control.enabled {
            return Some(HtrSkipReason::DisabledFlag);
        }
        if self.num_conflicts < control.next_conflict {
            return Some(HtrSkipReason::IntervalNotDue);
        }

        // CaDiCaL ternary.cpp:360 + options.hpp:244:
        // later HTR calls are delayed until enough search ticks accumulate
        // relative to the current clause database.
        // Adaptive scaling (#8099): lower threshold when overhead is low.
        if let Some(last_ticks) = self.inproc.htr.last_search_ticks() {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(last_ticks);
            let base_threshold = HTR_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(HtrSkipReason::ThresholdDelay);
            }
        }

        None
    }

    /// Check if we should run HTR (interval + tick-threshold delay).
    pub(in crate::solver) fn should_htr(&self) -> bool {
        self.htr_skip_reason().is_none()
    }

    /// Check if we should run factorization (interval + delay + mark-watermark).
    pub(in crate::solver) fn should_factor(&self) -> bool {
        self.factor_skip_reason().is_none()
    }

    /// Check if preprocessing should run factorization.
    ///
    /// Preprocessing has no meaningful conflict-based interval yet, so it uses
    /// only the CaDiCaL-style delay guard plus the factor mark-watermark gate.
    pub(in crate::solver) fn should_preprocess_factor(&self) -> bool {
        if !self.inproc_ctrl.factor.enabled {
            return false;
        }

        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed());
        let active_log10 = Self::floor_log10(active_vars);
        let delay_limit = u64::from(self.cold.bve_phases) + FACTOR_DELAY;
        if active_log10 > delay_limit {
            return false;
        }

        self.cold.factor_last_completed_epoch < self.cold.factor_marked_epoch
    }

    /// Evaluate the backbone pass skip reason with a CaDiCaL-style tick-threshold
    /// delay (limit.hpp:136-164, options.hpp: `backbonethresh = 5`).
    pub(in crate::solver) fn backbone_skip_reason(&self) -> Option<BackboneSkipReason> {
        let control = &self.inproc_ctrl.backbone;
        if !control.enabled {
            return Some(BackboneSkipReason::DisabledFlag);
        }
        if self.num_conflicts < control.next_conflict {
            return Some(BackboneSkipReason::IntervalNotDue);
        }

        // CaDiCaL backbone.cpp + limit.hpp SET_EFFORT_LIMIT:
        // skip if not enough search ticks have accumulated since the last
        // backbone call relative to the current clause database size.
        // The first call (last_backbone_ticks == 0 and num_conflicts > 0)
        // always passes since ticks_delta equals the full search tick count.
        // Adaptive scaling (#8099): lower threshold when overhead is low.
        if self.cold.last_backbone_ticks > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_backbone_ticks);
            let base_threshold =
                BACKBONE_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(BackboneSkipReason::ThresholdDelay);
            }
        }

        None
    }

    /// Check if we should run backbone (interval + tick-threshold delay).
    pub(in crate::solver) fn should_backbone(&self) -> bool {
        self.backbone_skip_reason().is_none()
    }

    /// Evaluate the sweep pass skip reason with a CaDiCaL-style tick-threshold
    /// delay (limit.hpp:136-164, options.hpp: `sweepthresh = 5`).
    pub(in crate::solver) fn sweep_skip_reason(&self) -> Option<SweepSkipReason> {
        let control = &self.inproc_ctrl.sweep;
        if !control.enabled {
            return Some(SweepSkipReason::DisabledFlag);
        }
        if self.num_conflicts < control.next_conflict {
            return Some(SweepSkipReason::IntervalNotDue);
        }

        // CaDiCaL sweep.cpp + limit.hpp SET_EFFORT_LIMIT:
        // skip if not enough search ticks have accumulated since the last
        // sweep call relative to the current clause database size.
        // Adaptive scaling (#8099): lower threshold when overhead is low.
        if self.cold.last_sweep_ticks > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_sweep_ticks);
            let base_threshold =
                SWEEP_TICK_THRESHOLD.saturating_mul(self.num_clauses() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(SweepSkipReason::ThresholdDelay);
            }
        }

        None
    }

    /// Check if we should run sweep (interval + tick-threshold delay).
    pub(in crate::solver) fn should_sweep(&self) -> bool {
        self.sweep_skip_reason().is_none()
    }

    /// Record an affected trail position for minimal trail rewind (#8095).
    ///
    /// Called when inprocessing derives a new unit (enqueued at `trail.len()`)
    /// or deletes/clears a reason clause for a variable at a given trail position.
    /// Updates `earliest_affected_trail_pos` to the minimum of the current value
    /// and the given position.
    #[inline]
    pub(in crate::solver) fn mark_trail_affected(&mut self, pos: usize) {
        self.earliest_affected_trail_pos = Some(
            self.earliest_affected_trail_pos
                .map_or(pos, |cur| cur.min(pos)),
        );
    }

    /// Evaluate the vivify pass skip reason with a CaDiCaL-style tick-threshold
    /// delay (limit.hpp:136-164, options.hpp: `vivifythresh = 20`).
    ///
    /// Vivification uses a dual schedule (learned + irredundant). The tick
    /// threshold is checked against the learned vivify tick watermark, since
    /// that is the primary vivification pass (CaDiCaL's vivify uses a single
    /// learned tick watermark for the SET_EFFORT_LIMIT threshold).
    pub(in crate::solver) fn vivify_skip_reason(&self) -> Option<VivifySkipReason> {
        if !self.inproc_ctrl.vivify.enabled {
            return Some(VivifySkipReason::DisabledFlag);
        }
        if !self.should_vivify_learned() && !self.should_vivify_irred() {
            return Some(VivifySkipReason::IntervalNotDue);
        }

        // CaDiCaL vivify.cpp + limit.hpp SET_EFFORT_LIMIT:
        // skip if not enough search ticks have accumulated since the last
        // vivify call relative to the current clause database size.
        // Adaptive scaling (#8099): lower threshold when overhead is low.
        if self.cold.last_vivify_ticks > 0 {
            let ticks_now = self.search_ticks[0] + self.search_ticks[1];
            let ticks_delta = ticks_now.saturating_sub(self.cold.last_vivify_ticks);
            let base_threshold =
                VIVIFY_TICK_THRESHOLD.saturating_mul(self.arena.active_clause_count() as u64);
            let threshold = (base_threshold as f64 * self.adaptive_tick_scale()) as u64;
            if ticks_delta < threshold {
                return Some(VivifySkipReason::ThresholdDelay);
            }
        }

        None
    }
}
