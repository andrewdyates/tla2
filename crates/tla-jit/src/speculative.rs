// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unified speculative type specialization orchestrator.

use std::env;

use crate::deoptimization::{DeoptAction, DeoptStats, DeoptimizationTracker};
use crate::type_profile::{SpecType, TypeProfiler};
use crate::type_specializer::{SpecializationPlan, SpecializationPlanExt};

const DEFAULT_MIN_SPEEDUP_THRESHOLD: f64 = 1.05;
const SPECULATION_ENABLED_ENV: &str = "TLA2_JIT_SPECULATION";

/// Unified orchestrator for the speculative type specialization pipeline.
///
/// Lifecycle:
/// 1. Profiling: During warmup BFS rounds, observe types via `TypeProfiler`
/// 2. Stabilization: When profile stabilizes, build `SpecializationPlan`
/// 3. Recompilation: Trigger background Tier 2 recompilation with the plan
/// 4. Activation: Swap in recompiled cache when ready
/// 5. Monitoring: Track deopt events, abandon if types destabilize
///
/// The orchestrator is not `Sync`. It is owned by a single coordination
/// thread.
#[derive(Debug, Clone)]
pub(crate) struct SpeculativeState {
    /// Type profiler (collects runtime type observations).
    profiler: TypeProfiler,
    /// Specialization plan (derived from stable profile).
    plan: Option<SpecializationPlan>,
    /// Deoptimization tracker (monitors guard failures after activation).
    deopt_tracker: DeoptimizationTracker,
    /// Current phase of the speculative pipeline.
    phase: SpeculativePhase,
    /// Environment-configurable settings.
    config: SpeculativeConfig,
}

/// Current phase of the speculative pipeline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SpeculativePhase {
    /// Collecting type observations during BFS warmup.
    Profiling,
    /// Profile has stabilized; plan built; awaiting recompilation trigger.
    PlanReady,
    /// Background recompilation in progress.
    Recompiling,
    /// Specialized code is active.
    Active,
    /// Specialization was abandoned due to excessive deoptimizations.
    Abandoned,
    /// Disabled (no type profiling configured).
    Disabled,
}

/// Configuration for speculative specialization.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct SpeculativeConfig {
    /// Minimum speedup factor required before recompilation is worthwhile.
    pub(crate) min_speedup_threshold: f64,
    /// Whether speculation is enabled at all.
    pub(crate) enabled: bool,
}

impl SpeculativeConfig {
    #[must_use]
    pub(crate) fn from_env() -> Self {
        Self {
            min_speedup_threshold: DEFAULT_MIN_SPEEDUP_THRESHOLD,
            enabled: env::var(SPECULATION_ENABLED_ENV)
                .map(|value| value != "0")
                .unwrap_or(true),
        }
    }
}

impl Default for SpeculativeConfig {
    fn default() -> Self {
        Self::from_env()
    }
}

impl SpeculativeState {
    /// Create a speculative orchestrator using environment-derived settings.
    #[must_use]
    pub(crate) fn new(var_count: usize) -> Self {
        let config = SpeculativeConfig::from_env();
        if !config.enabled {
            return Self::disabled();
        }

        Self {
            profiler: TypeProfiler::new(var_count),
            plan: None,
            deopt_tracker: DeoptimizationTracker::new(),
            phase: SpeculativePhase::Profiling,
            config,
        }
    }

    /// Create a permanently disabled speculative state.
    #[must_use]
    pub(crate) fn disabled() -> Self {
        Self {
            profiler: TypeProfiler::with_config(0, u64::MAX, 1),
            plan: None,
            deopt_tracker: DeoptimizationTracker::new(),
            phase: SpeculativePhase::Disabled,
            config: SpeculativeConfig {
                min_speedup_threshold: DEFAULT_MIN_SPEEDUP_THRESHOLD,
                enabled: false,
            },
        }
    }

    /// Observe one state's variable types.
    ///
    /// Returns a [`SpeculativeEvent`] when this call transitions the
    /// orchestrator into a new externally relevant phase.
    pub(crate) fn observe_state(&mut self, types: &[SpecType]) -> Option<SpeculativeEvent> {
        if !matches!(self.phase, SpeculativePhase::Profiling) {
            return None;
        }

        if !self.profiler.observe_state(types) {
            return None;
        }

        let plan = SpecializationPlan::from_profile(self.profiler.profile());
        if !self.is_viable_plan(&plan) {
            return None;
        }

        self.plan = Some(plan.clone());
        self.phase = SpeculativePhase::PlanReady;
        Some(SpeculativeEvent::ProfileStabilized { plan })
    }

    /// Return the plan that is ready to trigger recompilation, if any.
    #[must_use]
    pub(crate) fn pending_plan(&self) -> Option<&SpecializationPlan> {
        if matches!(self.phase, SpeculativePhase::PlanReady) {
            self.plan.as_ref()
        } else {
            None
        }
    }

    /// Mark that Tier 2 recompilation has been triggered.
    pub(crate) fn mark_recompiling(&mut self) {
        if self.pending_plan().is_some() {
            self.phase = SpeculativePhase::Recompiling;
        }
    }

    /// Mark that Tier 2 recompilation completed and specialized code is active.
    pub(crate) fn mark_active(&mut self) {
        if !matches!(
            self.phase,
            SpeculativePhase::PlanReady | SpeculativePhase::Recompiling
        ) {
            return;
        }

        let Some(plan) = self.plan.clone() else {
            return;
        };

        self.deopt_tracker.activate(plan);
        self.phase = SpeculativePhase::Active;
    }

    /// Record a deoptimization event.
    #[must_use]
    pub(crate) fn record_deopt(&mut self) -> DeoptAction {
        if !matches!(self.phase, SpeculativePhase::Active) {
            return DeoptAction::Continue;
        }

        let action = self.deopt_tracker.record_deopt();
        if matches!(action, DeoptAction::Abandon) {
            self.phase = SpeculativePhase::Abandoned;
        }
        action
    }

    /// Record a state processed through the specialized path.
    pub(crate) fn record_specialized_state(&mut self) {
        if matches!(self.phase, SpeculativePhase::Active) {
            self.deopt_tracker.record_specialized_state();
        }
    }

    /// Return the current speculative phase.
    #[must_use]
    pub(crate) fn phase(&self) -> &SpeculativePhase {
        &self.phase
    }

    /// Return a diagnostic snapshot of the orchestrator.
    #[must_use]
    pub(crate) fn stats(&self) -> SpeculativeStats {
        let deopt = if self.deopt_tracker.is_active() || self.deopt_tracker.is_abandoned() {
            Some(self.deopt_tracker.stats())
        } else {
            None
        };

        SpeculativeStats {
            phase: self.phase.as_str().to_string(),
            profile_states_sampled: self.profiler.profile().total_states(),
            plan_speedup: self.plan.as_ref().map(|plan| plan.expected_speedup_factor),
            deopt,
        }
    }

    fn is_viable_plan(&self, plan: &SpecializationPlan) -> bool {
        plan.has_specializable_vars()
            && plan.expected_speedup_factor >= self.config.min_speedup_threshold
    }

    #[cfg(test)]
    pub(crate) fn with_test_config(
        var_count: usize,
        warmup_threshold: u64,
        sampling_rate: u32,
        config: SpeculativeConfig,
    ) -> Self {
        if !config.enabled {
            return Self::disabled();
        }

        Self {
            profiler: TypeProfiler::with_config(var_count, warmup_threshold, sampling_rate),
            plan: None,
            deopt_tracker: DeoptimizationTracker::new(),
            phase: SpeculativePhase::Profiling,
            config,
        }
    }
}

/// Externally visible phase transitions from the speculative pipeline.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum SpeculativeEvent {
    /// Profile has stabilized with a viable specialization plan.
    ProfileStabilized { plan: SpecializationPlan },
    /// Specialization was abandoned.
    SpecializationAbandoned { stats: DeoptStats },
}

/// Diagnostic snapshot of speculative-specialization state.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct SpeculativeStats {
    pub(crate) phase: String,
    pub(crate) profile_states_sampled: u64,
    pub(crate) plan_speedup: Option<f64>,
    pub(crate) deopt: Option<DeoptStats>,
}

impl SpeculativePhase {
    fn as_str(self) -> &'static str {
        match self {
            SpeculativePhase::Profiling => "profiling",
            SpeculativePhase::PlanReady => "plan_ready",
            SpeculativePhase::Recompiling => "recompiling",
            SpeculativePhase::Active => "active",
            SpeculativePhase::Abandoned => "abandoned",
            SpeculativePhase::Disabled => "disabled",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        SpeculativeConfig, SpeculativeEvent, SpeculativePhase, SpeculativeState,
        SPECULATION_ENABLED_ENV,
    };
    use crate::deoptimization::DeoptAction;
    use crate::type_profile::SpecType;
    use crate::type_specializer::SpecializationPlanExt;
    use std::{env, sync::Mutex};

    static SPECULATION_ENV_LOCK: Mutex<()> = Mutex::new(());

    fn test_config(enabled: bool) -> SpeculativeConfig {
        SpeculativeConfig {
            min_speedup_threshold: 1.05,
            enabled,
        }
    }

    #[test]
    fn full_lifecycle_progresses_from_profiling_to_active() {
        let mut state = SpeculativeState::with_test_config(2, 2, 1, test_config(true));

        assert!(state
            .observe_state(&[SpecType::Int, SpecType::Bool])
            .is_none());
        assert_eq!(state.phase(), &SpeculativePhase::Profiling);
        assert!(state.pending_plan().is_none());

        let event = state.observe_state(&[SpecType::Int, SpecType::Bool]);
        let Some(SpeculativeEvent::ProfileStabilized { plan }) = event else {
            panic!("expected profile stabilization event");
        };

        assert!(plan.has_specializable_vars());
        assert!(plan.expected_speedup_factor >= 1.05);
        assert_eq!(state.phase(), &SpeculativePhase::PlanReady);
        assert_eq!(
            state
                .pending_plan()
                .map(|pending| pending.var_specializations.len()),
            Some(plan.var_specializations.len())
        );

        state.mark_recompiling();
        assert_eq!(state.phase(), &SpeculativePhase::Recompiling);

        state.mark_active();
        assert_eq!(state.phase(), &SpeculativePhase::Active);

        state.record_specialized_state();
        state.record_specialized_state();

        let stats = state.stats();
        assert_eq!(stats.phase, "active");
        assert_eq!(stats.profile_states_sampled, 2);
        assert_eq!(stats.plan_speedup, Some(plan.expected_speedup_factor));

        let deopt = stats.deopt.expect("active state should expose deopt stats");
        assert_eq!(deopt.deopt_count, 0);
        assert_eq!(deopt.states_since_specialization, 2);
        assert!(!deopt.abandoned);
    }

    #[test]
    fn disabled_state_ignores_observations_and_plans() {
        let mut state = SpeculativeState::disabled();

        assert_eq!(state.phase(), &SpeculativePhase::Disabled);
        assert!(state.observe_state(&[]).is_none());
        assert!(state.pending_plan().is_none());
        assert_eq!(state.record_deopt(), DeoptAction::Continue);

        let stats = state.stats();
        assert_eq!(stats.phase, "disabled");
        assert_eq!(stats.profile_states_sampled, 0);
        assert!(stats.plan_speedup.is_none());
        assert!(stats.deopt.is_none());
    }

    #[test]
    fn deopt_path_abandons_specialization() {
        let mut state = SpeculativeState::with_test_config(1, 1, 1, test_config(true));

        let event = state.observe_state(&[SpecType::Int]);
        assert!(matches!(
            event,
            Some(SpeculativeEvent::ProfileStabilized { .. })
        ));

        state.mark_recompiling();
        state.mark_active();
        assert_eq!(state.phase(), &SpeculativePhase::Active);

        assert_eq!(state.record_deopt(), DeoptAction::Abandon);
        assert_eq!(state.phase(), &SpeculativePhase::Abandoned);

        let stats = state.stats();
        assert_eq!(stats.phase, "abandoned");
        let deopt = stats
            .deopt
            .expect("abandoned state should expose deopt stats");
        assert_eq!(deopt.deopt_count, 1);
        assert_eq!(deopt.states_since_specialization, 1);
        assert!(deopt.abandoned);
    }

    #[test]
    fn zero_var_specs_never_produce_a_plan() {
        let mut state = SpeculativeState::with_test_config(0, 1, 1, test_config(true));

        assert!(state.observe_state(&[]).is_none());
        assert_eq!(state.phase(), &SpeculativePhase::Profiling);
        assert!(state.pending_plan().is_none());

        let stats = state.stats();
        assert_eq!(stats.profile_states_sampled, 1);
        assert!(stats.plan_speedup.is_none());
    }

    #[test]
    fn immediate_stabilization_emits_plan_on_first_sample() {
        let mut state = SpeculativeState::with_test_config(1, 1, 1, test_config(true));

        let event = state.observe_state(&[SpecType::Bool]);
        let Some(SpeculativeEvent::ProfileStabilized { plan }) = event else {
            panic!("expected immediate stabilization event");
        };

        assert_eq!(state.phase(), &SpeculativePhase::PlanReady);
        assert_eq!(state.stats().profile_states_sampled, 1);
        assert_eq!(
            state.pending_plan().map(|pending| pending.bool_var_count()),
            Some(1)
        );
        assert!(plan.has_specializable_vars());
    }

    #[test]
    fn never_stabilizing_profile_stays_in_profiling() {
        let mut state = SpeculativeState::with_test_config(1, 3, 1, test_config(true));

        assert!(state.observe_state(&[SpecType::Int]).is_none());
        assert!(state.observe_state(&[SpecType::Bool]).is_none());

        assert_eq!(state.phase(), &SpeculativePhase::Profiling);
        assert!(state.pending_plan().is_none());
        assert_eq!(state.stats().profile_states_sampled, 2);
    }

    #[test]
    fn low_speedup_plans_are_filtered_out() {
        let mut state = SpeculativeState::with_test_config(
            2,
            1,
            1,
            SpeculativeConfig {
                min_speedup_threshold: 2.0,
                enabled: true,
            },
        );

        assert!(state
            .observe_state(&[SpecType::Int, SpecType::Bool])
            .is_none());
        assert_eq!(state.phase(), &SpeculativePhase::Profiling);
        assert!(state.pending_plan().is_none());

        let stats = state.stats();
        assert_eq!(stats.profile_states_sampled, 1);
        assert!(stats.plan_speedup.is_none());
    }

    #[test]
    fn new_respects_speculation_disable_environment_variable() {
        let _guard = SPECULATION_ENV_LOCK
            .lock()
            .expect("speculation env test lock should not be poisoned");

        env::remove_var(SPECULATION_ENABLED_ENV);
        env::set_var(SPECULATION_ENABLED_ENV, "0");

        let state = SpeculativeState::new(3);
        assert_eq!(state.phase(), &SpeculativePhase::Disabled);
        assert!(!state.config.enabled);

        env::remove_var(SPECULATION_ENABLED_ENV);
    }
}
