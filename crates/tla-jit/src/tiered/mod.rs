// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tiered JIT compilation with profiling feedback.
//!
//! Implements HotSpot-style tiered compilation for TLA+ actions:
//!
//! - **Tier 0 (Interpreter):** Default for all actions. Zero compilation cost.
//! - **Tier 1 (Basic JIT):** Triggered after N evaluations. Quick Cranelift
//!   compilation with standard optimizations (`opt_level = "speed"`).
//! - **Tier 2 (Optimized JIT):** Triggered after M evaluations. Uses profiling
//!   data (branching factor, evaluation frequency) to guide compilation decisions.
//!   Cranelift `opt_level = "speed"` with additional inlining and loop
//!   optimizations enabled.
//!
//! # Thresholds
//!
//! Default thresholds are configurable via environment variables:
//!
//! | Tier | Default | Env Var |
//! |------|---------|---------|
//! | 1    | 100     | `TLA2_JIT_TIER1_THRESHOLD` |
//! | 2    | 10,000  | `TLA2_JIT_TIER2_THRESHOLD` |
//!
//! # Usage
//!
//! ```text
//! let mut manager = TierManager::new(action_count);
//!
//! // During model checking, periodically:
//! let promotions = manager.promotion_check(&action_stats);
//! for p in promotions {
//!     match p.new_tier {
//!         CompilationTier::Tier1 => { /* trigger basic JIT compile */ }
//!         CompilationTier::Tier2 => { /* trigger optimized JIT compile */ }
//!         _ => {}
//!     }
//! }
//! ```
//!
//! Part of #3850.

#[cfg(test)]
mod tests;

use std::fmt;

use crate::type_profile::{SpecType, TypeProfile, TypeProfiler};
use crate::type_specializer::{SpecializationPlan, SpecializationPlanExt};

// ---------------------------------------------------------------------------
// Compilation tier
// ---------------------------------------------------------------------------

/// Re-export the canonical [`CompilationTier`] enum from `tla-jit-abi`.
///
/// The definition moved to `tla-jit-abi::tier_types` in Wave 11b-redo of
/// epic #4251 Stage 2d so that `tla-check` can hold tier-state fields
/// without pulling `tla-jit` (and its Cranelift forks) into the dep graph.
pub use tla_jit_abi::CompilationTier;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Re-export the canonical [`TierConfig`] struct from `tla-jit-abi`.
///
/// Moved to `tla-jit-abi::tier_types` in Wave 14 TL-R1 (Part of #4267 Stage 2d)
/// so `tla-check` can construct `TierConfig` values (e.g., via
/// `TierConfig::from_env()`) without pulling `tla-jit` (and its Cranelift
/// forks) into the dep graph.
pub use tla_jit_abi::{TierConfig, DEFAULT_TIER1_THRESHOLD, DEFAULT_TIER2_THRESHOLD};

// ---------------------------------------------------------------------------
// Action profiling snapshot
// ---------------------------------------------------------------------------

/// Re-export the canonical [`ActionProfile`] struct from `tla-jit-abi`.
///
/// Moved to `tla-jit-abi::tier_types` in Wave 14 TL-R1 (Part of #4267 Stage 2d)
/// so `tla-check` can build `Vec<ActionProfile>` snapshots without pulling
/// `tla-jit` (and its Cranelift forks) into the dep graph.
pub use tla_jit_abi::ActionProfile;

// ---------------------------------------------------------------------------
// Promotion event
// ---------------------------------------------------------------------------

/// Re-export the canonical [`TierPromotion`] event struct from `tla-jit-abi`.
///
/// The definition moved to `tla-jit-abi::tier_types` in Wave 11b-redo of
/// epic #4251 Stage 2d so that `tla-check::tier_promotion_history` (a
/// `Vec<TierPromotion>`) does not pull `tla-jit` (and its Cranelift forks)
/// into the dep graph.
pub use tla_jit_abi::TierPromotion;

// ---------------------------------------------------------------------------
// Per-action state
// ---------------------------------------------------------------------------

/// Internal per-action tracking state.
#[derive(Debug, Clone)]
struct ActionTierState {
    /// Current compilation tier.
    tier: CompilationTier,
    /// Whether this action is eligible for JIT compilation at all.
    /// Actions that fail the eligibility gate stay at Tier 0 forever.
    jit_eligible: bool,
}

impl Default for ActionTierState {
    fn default() -> Self {
        ActionTierState {
            tier: CompilationTier::Interpreter,
            jit_eligible: false,
        }
    }
}

// ---------------------------------------------------------------------------
// TierManager
// ---------------------------------------------------------------------------

/// Manages tiered JIT compilation decisions for TLA+ actions.
///
/// The `TierManager` tracks the compilation tier of each action and uses
/// profiling data from the model checker to decide when to promote actions
/// to higher tiers. It does **not** perform compilation itself; instead it
/// emits [`TierPromotion`] events that the model checker acts on.
///
/// # Thread Safety
///
/// `TierManager` is **not** `Sync`. It should be owned by a single
/// coordination thread that periodically calls `promotion_check` and
/// dispatches compilations. The profiling data it reads (`ActionProfile`)
/// is a snapshot copied from the atomic counters in `ActionMetrics`.
pub struct TierManager {
    config: TierConfig,
    actions: Vec<ActionTierState>,
    /// Runtime type profiler for Tier 2 speculative specialization.
    ///
    /// Initialized via [`TierManager::enable_type_profiling`] after the
    /// state variable count is known. Profiles observed types of state
    /// variables during BFS and produces a `SpecializationPlan` when
    /// the profile stabilizes (at Tier 2 promotion).
    ///
    /// Part of #3989: speculative type specialization.
    type_profiler: Option<TypeProfiler>,
}

impl TierManager {
    /// Create a new tier manager for `action_count` actions.
    ///
    /// All actions start at Tier 0 (Interpreter). Use [`TierManager::set_eligible`]
    /// to mark actions that pass the JIT eligibility gate.
    pub fn new(action_count: usize) -> Self {
        TierManager {
            config: TierConfig::from_env(),
            actions: vec![ActionTierState::default(); action_count],
            type_profiler: None,
        }
    }

    /// Create a new tier manager with explicit configuration.
    pub fn with_config(action_count: usize, config: TierConfig) -> Self {
        TierManager {
            config,
            actions: vec![ActionTierState::default(); action_count],
            type_profiler: None,
        }
    }

    /// Mark an action as JIT-eligible.
    ///
    /// Only eligible actions can be promoted beyond Tier 0. Call this after
    /// running the JIT eligibility check on the action's bytecode.
    pub fn set_eligible(&mut self, action_id: usize) {
        if let Some(state) = self.actions.get_mut(action_id) {
            state.jit_eligible = true;
        }
    }

    /// Get the current compilation tier for an action.
    pub fn current_tier(&self, action_id: usize) -> CompilationTier {
        self.actions
            .get(action_id)
            .map_or(CompilationTier::Interpreter, |s| s.tier)
    }

    /// Check whether an action is eligible for JIT compilation.
    pub fn is_eligible(&self, action_id: usize) -> bool {
        self.actions
            .get(action_id)
            .map_or(false, |s| s.jit_eligible)
    }

    /// Return the tier configuration.
    pub fn config(&self) -> &TierConfig {
        &self.config
    }

    /// Number of actions tracked.
    pub fn action_count(&self) -> usize {
        self.actions.len()
    }

    /// Check all actions for tier promotions based on current profiling data.
    ///
    /// `profiles` must have the same length as `action_count` (one entry per
    /// action). Returns a list of promotions that occurred. Each action can
    /// only be promoted once per call (Tier 0 -> Tier 1 or Tier 1 -> Tier 2,
    /// never skipping a tier).
    ///
    /// The model checker should call this periodically (e.g., every BFS level
    /// or every N states) and act on the returned promotions by triggering
    /// the appropriate JIT compilation.
    pub fn promotion_check(&mut self, profiles: &[ActionProfile]) -> Vec<TierPromotion> {
        assert_eq!(
            profiles.len(),
            self.actions.len(),
            "profiles length ({}) must match action count ({})",
            profiles.len(),
            self.actions.len()
        );

        // Pre-compute specialization plan once (shared across all Tier 2 promotions
        // in this check). Done before entering the iter_mut loop to avoid borrow conflict.
        let spec_plan = self.build_specialization_plan();

        let mut promotions = Vec::new();

        for (action_id, (state, profile)) in
            self.actions.iter_mut().zip(profiles.iter()).enumerate()
        {
            // Skip ineligible actions — they stay at Tier 0 forever
            if !state.jit_eligible {
                continue;
            }

            let evals = profile.times_evaluated;
            let old_tier = state.tier;

            let new_tier = match old_tier {
                CompilationTier::Interpreter if evals >= self.config.tier1_threshold => {
                    CompilationTier::Tier1
                }
                CompilationTier::Tier1 if evals >= self.config.tier2_threshold => {
                    CompilationTier::Tier2
                }
                _ => continue,
            };

            state.tier = new_tier;
            let specialization_plan = if new_tier == CompilationTier::Tier2 {
                spec_plan.clone()
            } else {
                None
            };
            promotions.push(TierPromotion {
                action_id,
                old_tier,
                new_tier,
                evaluations_at_promotion: evals,
                branching_factor: profile.branching_factor,
                specialization_plan,
            });
        }

        promotions
    }

    /// Promote all eligible actions to `target_tier` using the aggregate
    /// evaluation count from a single "Next" bucket.
    ///
    /// In monolithic BFS mode, only the combined "Next" action accumulates
    /// evaluations — individual split actions stay at 0. This method bridges
    /// that gap: when the aggregate "Next" counter crosses a threshold, the
    /// caller invokes this to promote every eligible sub-action together.
    ///
    /// Returns the list of promotions that actually occurred (actions already
    /// at or above `target_tier` are skipped).
    ///
    /// Part of #3910: fix split-action promotion in monolithic BFS paths.
    pub fn promote_all_actions(
        &mut self,
        target_tier: CompilationTier,
        aggregate_evals: u64,
        aggregate_branching_factor: f64,
    ) -> Vec<TierPromotion> {
        // Pre-compute specialization plan once (shared across all Tier 2 promotions).
        let spec_plan = self.build_specialization_plan();
        let mut promotions = Vec::new();
        for (action_id, state) in self.actions.iter_mut().enumerate() {
            if !state.jit_eligible {
                continue;
            }
            if state.tier >= target_tier {
                continue;
            }
            let old_tier = state.tier;
            // Promote one step at a time (Interpreter -> Tier1 -> Tier2).
            let new_tier = match old_tier {
                CompilationTier::Interpreter => CompilationTier::Tier1,
                CompilationTier::Tier1 => CompilationTier::Tier2,
                CompilationTier::Tier2 => continue,
            };
            state.tier = new_tier;
            let specialization_plan = if new_tier == CompilationTier::Tier2 {
                spec_plan.clone()
            } else {
                None
            };
            promotions.push(TierPromotion {
                action_id,
                old_tier,
                new_tier,
                evaluations_at_promotion: aggregate_evals,
                branching_factor: aggregate_branching_factor,
                specialization_plan,
            });
        }
        promotions
    }

    /// Force-promote an action to a specific tier (for testing or manual override).
    ///
    /// Returns `true` if the promotion was applied, `false` if the action_id
    /// is out of range or the action is not eligible.
    pub fn force_promote(&mut self, action_id: usize, tier: CompilationTier) -> bool {
        if let Some(state) = self.actions.get_mut(action_id) {
            if state.jit_eligible || tier == CompilationTier::Interpreter {
                state.tier = tier;
                return true;
            }
        }
        false
    }

    /// Collect a summary of current tier distribution (for logging/diagnostics).
    pub fn tier_summary(&self) -> TierSummary {
        let mut summary = TierSummary::default();
        for state in &self.actions {
            match state.tier {
                CompilationTier::Interpreter => summary.interpreter += 1,
                CompilationTier::Tier1 => summary.tier1 += 1,
                CompilationTier::Tier2 => summary.tier2 += 1,
            }
            if state.jit_eligible {
                summary.eligible += 1;
            }
        }
        summary.total = self.actions.len();
        summary
    }

    // -----------------------------------------------------------------------
    // Type profiling for Tier 2 specialization (Part of #3989)
    // -----------------------------------------------------------------------

    /// Enable runtime type profiling for Tier 2 speculative specialization.
    ///
    /// `var_count` is the number of state variables in the spec. The profiler
    /// uses environment-derived warmup and sampling configuration.
    ///
    /// Call this after the state variable count is known (post-init-state).
    /// Profiling data is consumed by `build_specialization_plan` when a Tier 2
    /// promotion fires.
    pub fn enable_type_profiling(&mut self, var_count: usize) {
        self.type_profiler = Some(TypeProfiler::new(var_count));
    }

    /// Enable runtime type profiling with explicit configuration.
    ///
    /// Useful in tests to control warmup threshold and sampling rate.
    pub fn enable_type_profiling_with_config(
        &mut self,
        var_count: usize,
        warmup_threshold: u64,
        sampling_rate: u32,
    ) {
        self.type_profiler = Some(TypeProfiler::with_config(
            var_count,
            warmup_threshold,
            sampling_rate,
        ));
    }

    /// Record the types of state variable values for one explored state.
    ///
    /// Called on the BFS hot path (after successor generation). Returns `true`
    /// if this call caused the type profile to stabilize (warmup complete).
    ///
    /// When no profiler is active (type profiling not enabled), returns `false`.
    pub fn observe_state_types(&mut self, types: &[SpecType]) -> bool {
        match self.type_profiler.as_mut() {
            Some(profiler) => profiler.observe_state(types),
            None => false,
        }
    }

    /// Return `true` when the type profiler has collected a stable profile.
    #[must_use]
    pub fn type_profile_stable(&self) -> bool {
        self.type_profiler
            .as_ref()
            .map_or(false, TypeProfiler::is_stable)
    }

    /// Borrow the current type profile, if profiling is active.
    #[must_use]
    pub fn type_profile(&self) -> Option<&TypeProfile> {
        self.type_profiler.as_ref().map(TypeProfiler::profile)
    }

    /// Build a `SpecializationPlan` from the current type profile, if available
    /// and the profile has stabilized with specializable variables.
    ///
    /// Returns `None` when:
    /// - No profiler is active
    /// - The profile has not stabilized yet
    /// - No Int or Bool monomorphic variables were observed
    #[must_use]
    fn build_specialization_plan(&self) -> Option<SpecializationPlan> {
        let profiler = self.type_profiler.as_ref()?;
        if !profiler.is_stable() {
            return None;
        }
        let plan = SpecializationPlan::from_profile(profiler.profile());
        if plan.has_specializable_vars() {
            Some(plan)
        } else {
            None
        }
    }
}

/// Summary of tier distribution across all actions.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TierSummary {
    /// Total number of actions.
    pub total: usize,
    /// Number of JIT-eligible actions.
    pub eligible: usize,
    /// Number of actions at Tier 0 (Interpreter).
    pub interpreter: usize,
    /// Number of actions at Tier 1 (Basic JIT).
    pub tier1: usize,
    /// Number of actions at Tier 2 (Optimized JIT).
    pub tier2: usize,
}

impl fmt::Display for TierSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "actions={} eligible={} tier0={} tier1={} tier2={}",
            self.total, self.eligible, self.interpreter, self.tier1, self.tier2
        )
    }
}

// ---------------------------------------------------------------------------
// Compilation statistics
// ---------------------------------------------------------------------------

// `CompileStats` moved to `tla-jit-abi` in Wave 16 Gate 1 Batch E
// (Part of #4267 / #4291). Re-exported for backward compatibility with
// existing `tla_jit::CompileStats` callers.
pub use tla_jit_abi::CompileStats;

// `CacheBuildStats` moved to `tla-jit-abi` in Wave 16 Gate 1 Batch E
// (Part of #4267 / #4291) so `tla-check` can hold build-stat fields on
// `ModelChecker` without depending on the Cranelift JIT crate. Re-exported
// here for backward compatibility with existing `tla_jit::CacheBuildStats`
// callers.
pub use tla_jit_abi::CacheBuildStats;
