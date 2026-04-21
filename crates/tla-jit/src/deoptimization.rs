// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Deoptimization tracking and fallback for speculative type specialization.

use crate::type_specializer::SpecializationPlan;

const DEFAULT_MAX_DEOPT_RATIO: f64 = 0.01;
const DEFAULT_MAX_DEOPT_ABSOLUTE: u64 = 1_000;

/// Tracks deoptimization events and decides when to abandon specialization.
#[derive(Debug, Clone)]
pub(crate) struct DeoptimizationTracker {
    /// Number of deoptimization events (type guard failures) observed.
    deopt_count: u64,
    /// Total number of states processed since specialization was applied.
    states_since_specialization: u64,
    /// Maximum deopt ratio before permanently abandoning specialization.
    max_deopt_ratio: f64,
    /// Absolute maximum deopt count before abandoning.
    max_deopt_absolute: u64,
    /// Whether specialization has been permanently abandoned.
    abandoned: bool,
    /// The specialization plan that was active (for diagnostics).
    active_plan: Option<SpecializationPlan>,
}

impl DeoptimizationTracker {
    /// Create a tracker with default abandonment thresholds.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::with_config(DEFAULT_MAX_DEOPT_RATIO, DEFAULT_MAX_DEOPT_ABSOLUTE)
    }

    /// Create a tracker with explicit abandonment thresholds.
    #[must_use]
    pub(crate) fn with_config(max_deopt_ratio: f64, max_deopt_absolute: u64) -> Self {
        let max_deopt_ratio = if max_deopt_ratio.is_finite() {
            max_deopt_ratio.max(0.0)
        } else {
            DEFAULT_MAX_DEOPT_RATIO
        };

        Self {
            deopt_count: 0,
            states_since_specialization: 0,
            max_deopt_ratio,
            max_deopt_absolute,
            abandoned: false,
            active_plan: None,
        }
    }

    /// Record that specialization was applied with a given plan.
    pub(crate) fn activate(&mut self, plan: SpecializationPlan) {
        self.deopt_count = 0;
        self.states_since_specialization = 0;
        self.abandoned = false;
        self.active_plan = Some(plan);
    }

    /// Record one state processed through the specialized path.
    pub(crate) fn record_specialized_state(&mut self) {
        if self.is_active() {
            self.states_since_specialization = self.states_since_specialization.saturating_add(1);
        }
    }

    /// Record a deoptimization event and decide whether to abandon specialization.
    #[must_use]
    pub(crate) fn record_deopt(&mut self) -> DeoptAction {
        if self.abandoned {
            return DeoptAction::Abandon;
        }
        if self.active_plan.is_none() {
            return DeoptAction::Continue;
        }

        self.deopt_count = self.deopt_count.saturating_add(1);
        self.states_since_specialization = self.states_since_specialization.saturating_add(1);

        if self.should_abandon() {
            self.abandoned = true;
            return DeoptAction::Abandon;
        }

        DeoptAction::Continue
    }

    /// Whether specialization has been abandoned.
    #[must_use]
    pub(crate) fn is_abandoned(&self) -> bool {
        self.abandoned
    }

    /// Whether specialization is currently active (activated and not abandoned).
    #[must_use]
    pub(crate) fn is_active(&self) -> bool {
        self.active_plan.is_some() && !self.abandoned
    }

    /// Get diagnostic stats.
    #[must_use]
    pub(crate) fn stats(&self) -> DeoptStats {
        let deopt_ratio = if self.states_since_specialization == 0 {
            0.0
        } else {
            self.deopt_count as f64 / self.states_since_specialization as f64
        };

        DeoptStats {
            deopt_count: self.deopt_count,
            states_since_specialization: self.states_since_specialization,
            deopt_ratio,
            abandoned: self.abandoned,
        }
    }

    fn should_abandon(&self) -> bool {
        self.deopt_count >= self.max_deopt_absolute
            || self.stats().deopt_ratio > self.max_deopt_ratio
    }
}

impl Default for DeoptimizationTracker {
    fn default() -> Self {
        Self::new()
    }
}

/// Action to take after recording a deoptimization event.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DeoptAction {
    /// Continue using specialized code.
    Continue,
    /// Abandon specialization and revert to generic code.
    Abandon,
}

/// Diagnostic deoptimization counters.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct DeoptStats {
    pub(crate) deopt_count: u64,
    pub(crate) states_since_specialization: u64,
    pub(crate) deopt_ratio: f64,
    pub(crate) abandoned: bool,
}

#[cfg(test)]
mod tests {
    use super::{DeoptAction, DeoptStats, DeoptimizationTracker};
    use crate::type_profile::{SpecType, TypeProfile};
    use crate::type_specializer::{SpecializationPlan, SpecializationPlanExt};

    fn make_plan(types: &[SpecType]) -> SpecializationPlan {
        let mut profile = TypeProfile::new(types.len());
        profile.record_state(types);
        profile.record_state(types);
        profile.mark_stable();
        SpecializationPlan::from_profile(&profile)
    }

    fn approx_eq(lhs: f64, rhs: f64) {
        let diff = (lhs - rhs).abs();
        assert!(
            diff <= 1e-9,
            "expected {lhs} to be within tolerance of {rhs}, diff={diff}"
        );
    }

    #[test]
    fn tracker_counts_specialized_states_and_deopts() {
        let mut tracker = DeoptimizationTracker::with_config(0.5, 10);
        tracker.activate(make_plan(&[SpecType::Int]));

        tracker.record_specialized_state();
        tracker.record_specialized_state();

        assert_eq!(tracker.record_deopt(), DeoptAction::Continue);

        let stats = tracker.stats();
        assert_eq!(
            stats,
            DeoptStats {
                deopt_count: 1,
                states_since_specialization: 3,
                deopt_ratio: 1.0 / 3.0,
                abandoned: false,
            }
        );
    }

    #[test]
    fn tracker_abandons_when_deopt_ratio_exceeds_threshold() {
        let mut tracker = DeoptimizationTracker::with_config(0.2, 10);
        tracker.activate(make_plan(&[SpecType::Bool]));

        for _ in 0..4 {
            tracker.record_specialized_state();
        }

        assert_eq!(tracker.record_deopt(), DeoptAction::Continue);
        assert!(!tracker.is_abandoned());

        assert_eq!(tracker.record_deopt(), DeoptAction::Abandon);
        assert!(tracker.is_abandoned());

        let stats = tracker.stats();
        assert_eq!(stats.deopt_count, 2);
        assert_eq!(stats.states_since_specialization, 6);
        approx_eq(stats.deopt_ratio, 2.0 / 6.0);
        assert!(stats.abandoned);
    }

    #[test]
    fn tracker_abandons_when_deopt_absolute_threshold_is_hit() {
        let mut tracker = DeoptimizationTracker::with_config(1.0, 3);
        tracker.activate(make_plan(&[SpecType::Int, SpecType::Bool]));

        assert_eq!(tracker.record_deopt(), DeoptAction::Continue);
        assert_eq!(tracker.record_deopt(), DeoptAction::Continue);
        assert_eq!(tracker.record_deopt(), DeoptAction::Abandon);
        assert!(tracker.is_abandoned());
    }

    #[test]
    fn tracker_stats_are_zero_before_activation() {
        let tracker = DeoptimizationTracker::new();
        assert!(!tracker.is_active());
        assert!(!tracker.is_abandoned());

        let stats = tracker.stats();
        assert_eq!(stats.deopt_count, 0);
        assert_eq!(stats.states_since_specialization, 0);
        approx_eq(stats.deopt_ratio, 0.0);
        assert!(!stats.abandoned);
    }

    #[test]
    fn tracker_reactivation_clears_previous_counters() {
        let mut tracker = DeoptimizationTracker::with_config(0.01, 10);
        tracker.activate(make_plan(&[SpecType::Int]));
        assert_eq!(tracker.record_deopt(), DeoptAction::Abandon);
        assert!(tracker.is_abandoned());

        tracker.activate(make_plan(&[SpecType::Bool]));
        assert!(tracker.is_active());
        assert!(!tracker.is_abandoned());

        let stats = tracker.stats();
        assert_eq!(stats.deopt_count, 0);
        assert_eq!(stats.states_since_specialization, 0);
        approx_eq(stats.deopt_ratio, 0.0);
        assert!(!stats.abandoned);
    }

    #[test]
    fn tracker_ignores_deopts_before_activation() {
        let mut tracker = DeoptimizationTracker::new();
        assert_eq!(tracker.record_deopt(), DeoptAction::Continue);

        let stats = tracker.stats();
        assert_eq!(stats.deopt_count, 0);
        assert_eq!(stats.states_since_specialization, 0);
        approx_eq(stats.deopt_ratio, 0.0);
        assert!(!stats.abandoned);
    }
}
