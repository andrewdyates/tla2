// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for tiered JIT compilation manager.
//!
//! Part of #3850.

use super::*;

// ---------------------------------------------------------------------------
// Helper: build profiles slice
// ---------------------------------------------------------------------------

fn profile(evals: u64, branching: f64, eligible: bool) -> ActionProfile {
    ActionProfile {
        times_evaluated: evals,
        branching_factor: branching,
        jit_eligible: eligible,
    }
}

// ---------------------------------------------------------------------------
// TierConfig
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_config_defaults() {
    let cfg = TierConfig::default();
    assert_eq!(cfg.tier1_threshold, 500);
    assert_eq!(cfg.tier2_threshold, 5_000);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_config_custom() {
    let cfg = TierConfig::new(50, 5_000);
    assert_eq!(cfg.tier1_threshold, 50);
    assert_eq!(cfg.tier2_threshold, 5_000);
}

// ---------------------------------------------------------------------------
// CompilationTier ordering
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier_ordering() {
    assert!(CompilationTier::Interpreter < CompilationTier::Tier1);
    assert!(CompilationTier::Tier1 < CompilationTier::Tier2);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier_display() {
    assert_eq!(
        format!("{}", CompilationTier::Interpreter),
        "Tier0/Interpreter"
    );
    assert_eq!(format!("{}", CompilationTier::Tier1), "Tier1/BasicJIT");
    assert_eq!(format!("{}", CompilationTier::Tier2), "Tier2/OptimizedJIT");
}

// ---------------------------------------------------------------------------
// TierManager creation
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_new_all_at_interpreter() {
    let mgr = TierManager::with_config(3, TierConfig::default());
    assert_eq!(mgr.action_count(), 3);
    for i in 0..3 {
        assert_eq!(mgr.current_tier(i), CompilationTier::Interpreter);
        assert!(!mgr.is_eligible(i));
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_eligible() {
    let mut mgr = TierManager::with_config(2, TierConfig::default());
    mgr.set_eligible(0);
    assert!(mgr.is_eligible(0));
    assert!(!mgr.is_eligible(1));
}

// ---------------------------------------------------------------------------
// Tier 0 -> Tier 1 promotion
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_promote_to_tier1_at_threshold() {
    let cfg = TierConfig::new(100, 10_000);
    let mut mgr = TierManager::with_config(2, cfg);
    mgr.set_eligible(0);
    mgr.set_eligible(1);

    // Below threshold: no promotions
    let profiles = vec![profile(99, 1.0, true), profile(50, 2.0, true)];
    let promotions = mgr.promotion_check(&profiles);
    assert!(promotions.is_empty());
    assert_eq!(mgr.current_tier(0), CompilationTier::Interpreter);

    // At threshold: action 0 promoted
    let profiles = vec![profile(100, 1.0, true), profile(50, 2.0, true)];
    let promotions = mgr.promotion_check(&profiles);
    assert_eq!(promotions.len(), 1);
    assert_eq!(promotions[0].action_id, 0);
    assert_eq!(promotions[0].old_tier, CompilationTier::Interpreter);
    assert_eq!(promotions[0].new_tier, CompilationTier::Tier1);
    assert_eq!(promotions[0].evaluations_at_promotion, 100);
    assert_eq!(mgr.current_tier(0), CompilationTier::Tier1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_promote_to_tier1_above_threshold() {
    let cfg = TierConfig::new(100, 10_000);
    let mut mgr = TierManager::with_config(1, cfg);
    mgr.set_eligible(0);

    // Well above threshold: still just promoted to Tier 1 (no skip)
    let profiles = vec![profile(500, 3.0, true)];
    let promotions = mgr.promotion_check(&profiles);
    assert_eq!(promotions.len(), 1);
    assert_eq!(promotions[0].new_tier, CompilationTier::Tier1);
    assert_eq!(mgr.current_tier(0), CompilationTier::Tier1);
}

// ---------------------------------------------------------------------------
// Tier 1 -> Tier 2 promotion
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_promote_to_tier2() {
    let cfg = TierConfig::new(100, 10_000);
    let mut mgr = TierManager::with_config(1, cfg);
    mgr.set_eligible(0);

    // First: promote to Tier 1
    let profiles = vec![profile(100, 1.0, true)];
    let _ = mgr.promotion_check(&profiles);
    assert_eq!(mgr.current_tier(0), CompilationTier::Tier1);

    // Below Tier 2 threshold: no further promotion
    let profiles = vec![profile(9_999, 5.0, true)];
    let promotions = mgr.promotion_check(&profiles);
    assert!(promotions.is_empty());
    assert_eq!(mgr.current_tier(0), CompilationTier::Tier1);

    // At Tier 2 threshold: promoted
    let profiles = vec![profile(10_000, 5.0, true)];
    let promotions = mgr.promotion_check(&profiles);
    assert_eq!(promotions.len(), 1);
    assert_eq!(promotions[0].old_tier, CompilationTier::Tier1);
    assert_eq!(promotions[0].new_tier, CompilationTier::Tier2);
    assert_eq!(promotions[0].evaluations_at_promotion, 10_000);
    assert!((promotions[0].branching_factor - 5.0).abs() < f64::EPSILON);
    assert_eq!(mgr.current_tier(0), CompilationTier::Tier2);
}

// ---------------------------------------------------------------------------
// No double promotion in single check
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_no_skip_tier() {
    let cfg = TierConfig::new(100, 10_000);
    let mut mgr = TierManager::with_config(1, cfg);
    mgr.set_eligible(0);

    // Even if evals exceeds both thresholds, only promote one step
    let profiles = vec![profile(50_000, 10.0, true)];
    let promotions = mgr.promotion_check(&profiles);
    assert_eq!(promotions.len(), 1);
    assert_eq!(promotions[0].new_tier, CompilationTier::Tier1);
    assert_eq!(mgr.current_tier(0), CompilationTier::Tier1);

    // Second check: now promote to Tier 2
    let promotions = mgr.promotion_check(&profiles);
    assert_eq!(promotions.len(), 1);
    assert_eq!(promotions[0].new_tier, CompilationTier::Tier2);
    assert_eq!(mgr.current_tier(0), CompilationTier::Tier2);
}

// ---------------------------------------------------------------------------
// Ineligible actions never promoted
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ineligible_never_promoted() {
    let cfg = TierConfig::new(10, 100);
    let mut mgr = TierManager::with_config(1, cfg);
    // Do NOT call set_eligible

    let profiles = vec![profile(1_000_000, 50.0, false)];
    let promotions = mgr.promotion_check(&profiles);
    assert!(promotions.is_empty());
    assert_eq!(mgr.current_tier(0), CompilationTier::Interpreter);
}

// ---------------------------------------------------------------------------
// Already at Tier 2: no further promotions
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier2_stable() {
    let cfg = TierConfig::new(10, 100);
    let mut mgr = TierManager::with_config(1, cfg);
    mgr.set_eligible(0);

    // Promote through both tiers
    let profiles = vec![profile(10, 1.0, true)];
    let _ = mgr.promotion_check(&profiles);
    let profiles = vec![profile(100, 1.0, true)];
    let _ = mgr.promotion_check(&profiles);
    assert_eq!(mgr.current_tier(0), CompilationTier::Tier2);

    // Further checks produce no promotions
    let profiles = vec![profile(1_000_000, 100.0, true)];
    let promotions = mgr.promotion_check(&profiles);
    assert!(promotions.is_empty());
}

// ---------------------------------------------------------------------------
// Multiple actions promoted in one check
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multiple_actions_promoted() {
    let cfg = TierConfig::new(100, 10_000);
    let mut mgr = TierManager::with_config(4, cfg);
    mgr.set_eligible(0);
    mgr.set_eligible(1);
    mgr.set_eligible(2);
    // action 3 NOT eligible

    let profiles = vec![
        profile(200, 2.0, true),  // action 0: promote to Tier 1
        profile(50, 1.0, true),   // action 1: below threshold
        profile(150, 3.0, true),  // action 2: promote to Tier 1
        profile(500, 5.0, false), // action 3: ineligible
    ];
    let promotions = mgr.promotion_check(&profiles);
    assert_eq!(promotions.len(), 2);
    assert_eq!(promotions[0].action_id, 0);
    assert_eq!(promotions[1].action_id, 2);
}

// ---------------------------------------------------------------------------
// force_promote
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_force_promote() {
    let mut mgr = TierManager::with_config(2, TierConfig::default());
    mgr.set_eligible(0);

    // Force-promote eligible action
    assert!(mgr.force_promote(0, CompilationTier::Tier2));
    assert_eq!(mgr.current_tier(0), CompilationTier::Tier2);

    // Force-promote ineligible action: fails
    assert!(!mgr.force_promote(1, CompilationTier::Tier1));
    assert_eq!(mgr.current_tier(1), CompilationTier::Interpreter);

    // Force-demote to Interpreter works even for ineligible
    assert!(mgr.force_promote(1, CompilationTier::Interpreter));

    // Out-of-range: fails
    assert!(!mgr.force_promote(99, CompilationTier::Tier1));
}

// ---------------------------------------------------------------------------
// tier_summary
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier_summary() {
    let cfg = TierConfig::new(10, 100);
    let mut mgr = TierManager::with_config(5, cfg);
    mgr.set_eligible(0);
    mgr.set_eligible(1);
    mgr.set_eligible(2);

    // Promote action 0 to Tier 1, action 1 to Tier 2
    let profiles = vec![
        profile(10, 1.0, true),
        profile(10, 1.0, true),
        profile(5, 1.0, true),
        profile(0, 0.0, false),
        profile(0, 0.0, false),
    ];
    let _ = mgr.promotion_check(&profiles);
    // action 0 and 1 at Tier 1 now
    let profiles = vec![
        profile(50, 1.0, true),
        profile(100, 1.0, true),
        profile(5, 1.0, true),
        profile(0, 0.0, false),
        profile(0, 0.0, false),
    ];
    let _ = mgr.promotion_check(&profiles);
    // action 1 at Tier 2 now

    let summary = mgr.tier_summary();
    assert_eq!(summary.total, 5);
    assert_eq!(summary.eligible, 3);
    assert_eq!(summary.interpreter, 3); // actions 2, 3, 4
    assert_eq!(summary.tier1, 1); // action 0
    assert_eq!(summary.tier2, 1); // action 1
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier_summary_display() {
    let summary = TierSummary {
        total: 10,
        eligible: 6,
        interpreter: 4,
        tier1: 4,
        tier2: 2,
    };
    assert_eq!(
        format!("{summary}"),
        "actions=10 eligible=6 tier0=4 tier1=4 tier2=2"
    );
}

// ---------------------------------------------------------------------------
// Edge cases
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_zero_actions() {
    let mut mgr = TierManager::with_config(0, TierConfig::default());
    let promotions = mgr.promotion_check(&[]);
    assert!(promotions.is_empty());

    let summary = mgr.tier_summary();
    assert_eq!(summary.total, 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_out_of_range_current_tier() {
    let mgr = TierManager::with_config(1, TierConfig::default());
    // Out-of-range returns Interpreter
    assert_eq!(mgr.current_tier(999), CompilationTier::Interpreter);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_out_of_range_is_eligible() {
    let mgr = TierManager::with_config(1, TierConfig::default());
    assert!(!mgr.is_eligible(999));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_eligible_out_of_range_noop() {
    let mut mgr = TierManager::with_config(1, TierConfig::default());
    // Should not panic, and the out-of-range index should remain ineligible
    mgr.set_eligible(999);
    assert!(
        !mgr.is_eligible(999),
        "out-of-range index should remain ineligible after set_eligible"
    );
    // Verify valid index 0 is unaffected
    assert!(
        !mgr.is_eligible(0),
        "valid index should be unaffected by out-of-range set_eligible"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[should_panic(expected = "profiles length")]
fn test_promotion_check_mismatched_profiles() {
    let mut mgr = TierManager::with_config(2, TierConfig::default());
    // Providing wrong number of profiles should panic
    let _ = mgr.promotion_check(&[profile(100, 1.0, true)]);
}

// ---------------------------------------------------------------------------
// Threshold = 0 edge case (immediate promotion)
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_threshold_zero_immediate_promotion() {
    let cfg = TierConfig::new(0, 0);
    let mut mgr = TierManager::with_config(1, cfg);
    mgr.set_eligible(0);

    let profiles = vec![profile(0, 0.0, true)];
    let promotions = mgr.promotion_check(&profiles);
    assert_eq!(promotions.len(), 1);
    assert_eq!(promotions[0].new_tier, CompilationTier::Tier1);

    let promotions = mgr.promotion_check(&profiles);
    assert_eq!(promotions.len(), 1);
    assert_eq!(promotions[0].new_tier, CompilationTier::Tier2);
}

// ---------------------------------------------------------------------------
// promote_all_actions — monolithic counting batch promotion
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_promote_all_actions_tier1() {
    let cfg = TierConfig::new(100, 10_000);
    let mut mgr = TierManager::with_config(4, cfg);
    mgr.set_eligible(0);
    mgr.set_eligible(1);
    mgr.set_eligible(2);
    // action 3 NOT eligible

    let promotions = mgr.promote_all_actions(CompilationTier::Tier1, 500, 2.5);
    assert_eq!(promotions.len(), 3); // actions 0, 1, 2
    for promo in &promotions {
        assert_eq!(promo.old_tier, CompilationTier::Interpreter);
        assert_eq!(promo.new_tier, CompilationTier::Tier1);
        assert_eq!(promo.evaluations_at_promotion, 500);
        assert!((promo.branching_factor - 2.5).abs() < f64::EPSILON);
    }
    assert_eq!(promotions[0].action_id, 0);
    assert_eq!(promotions[1].action_id, 1);
    assert_eq!(promotions[2].action_id, 2);

    // Verify tiers updated
    assert_eq!(mgr.current_tier(0), CompilationTier::Tier1);
    assert_eq!(mgr.current_tier(1), CompilationTier::Tier1);
    assert_eq!(mgr.current_tier(2), CompilationTier::Tier1);
    assert_eq!(mgr.current_tier(3), CompilationTier::Interpreter);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_promote_all_actions_tier2_steps_through_tier1() {
    let cfg = TierConfig::new(100, 10_000);
    let mut mgr = TierManager::with_config(2, cfg);
    mgr.set_eligible(0);
    mgr.set_eligible(1);

    // Request Tier2, but actions are at Interpreter — should step to Tier1 first
    let promotions = mgr.promote_all_actions(CompilationTier::Tier2, 50_000, 5.0);
    assert_eq!(promotions.len(), 2);
    assert_eq!(promotions[0].new_tier, CompilationTier::Tier1);
    assert_eq!(promotions[1].new_tier, CompilationTier::Tier1);

    // Second call: now step from Tier1 to Tier2
    let promotions = mgr.promote_all_actions(CompilationTier::Tier2, 50_000, 5.0);
    assert_eq!(promotions.len(), 2);
    assert_eq!(promotions[0].new_tier, CompilationTier::Tier2);
    assert_eq!(promotions[1].new_tier, CompilationTier::Tier2);

    // Third call: already at Tier2, no promotions
    let promotions = mgr.promote_all_actions(CompilationTier::Tier2, 50_000, 5.0);
    assert!(promotions.is_empty());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_promote_all_actions_skips_already_promoted() {
    let cfg = TierConfig::new(100, 10_000);
    let mut mgr = TierManager::with_config(3, cfg);
    mgr.set_eligible(0);
    mgr.set_eligible(1);
    mgr.set_eligible(2);

    // Manually promote action 0 to Tier1 first
    mgr.force_promote(0, CompilationTier::Tier1);

    // Now promote_all to Tier1: only actions 1 and 2 should get promoted
    let promotions = mgr.promote_all_actions(CompilationTier::Tier1, 500, 1.0);
    assert_eq!(promotions.len(), 2);
    assert_eq!(promotions[0].action_id, 1);
    assert_eq!(promotions[1].action_id, 2);
}

// ---------------------------------------------------------------------------
// Idempotent re-checks after promotion
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_repeated_checks_no_duplicate_promotions() {
    let cfg = TierConfig::new(100, 10_000);
    let mut mgr = TierManager::with_config(1, cfg);
    mgr.set_eligible(0);

    let profiles = vec![profile(200, 1.0, true)];
    let promotions = mgr.promotion_check(&profiles);
    assert_eq!(promotions.len(), 1); // promoted to Tier 1

    // Same profiles again: already at Tier 1, evals < Tier 2 threshold
    let promotions = mgr.promotion_check(&profiles);
    assert!(promotions.is_empty());
}

// ---------------------------------------------------------------------------
// Type profiling integration (Part of #3989)
// ---------------------------------------------------------------------------

use crate::type_profile::SpecType;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_type_profiling_enable_and_observe() {
    let cfg = TierConfig::new(5, 20);
    let mut mgr = TierManager::with_config(1, cfg);
    mgr.set_eligible(0);

    // No profiler initially.
    assert!(!mgr.type_profile_stable());
    assert!(mgr.type_profile().is_none());

    // Enable profiling for 3 state variables.
    mgr.enable_type_profiling(3);
    assert!(!mgr.type_profile_stable());
    assert!(mgr.type_profile().is_some());

    // Observe states until warmup (default is 1000, but we use env-derived
    // which defaults to 1000). Use explicit config instead.
    mgr.enable_type_profiling_with_config(3, 5, 1);

    for _ in 0..4 {
        let stabilized = mgr.observe_state_types(&[SpecType::Int, SpecType::Bool, SpecType::Int]);
        assert!(!stabilized);
    }
    assert!(!mgr.type_profile_stable());

    // 5th observation stabilizes the profile.
    let stabilized = mgr.observe_state_types(&[SpecType::Int, SpecType::Bool, SpecType::Int]);
    assert!(stabilized);
    assert!(mgr.type_profile_stable());

    // Further observations are no-ops.
    let stabilized =
        mgr.observe_state_types(&[SpecType::String, SpecType::String, SpecType::String]);
    assert!(!stabilized);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier2_promotion_includes_specialization_plan() {
    let cfg = TierConfig::new(5, 10);
    let mut mgr = TierManager::with_config(1, cfg);
    mgr.set_eligible(0);
    mgr.enable_type_profiling_with_config(2, 3, 1);

    // Feed type profiling with monomorphic Int + Bool.
    for _ in 0..3 {
        mgr.observe_state_types(&[SpecType::Int, SpecType::Bool]);
    }
    assert!(mgr.type_profile_stable());

    // Promote to Tier 1 — should NOT have specialization plan.
    let profiles = vec![profile(5, 1.0, true)];
    let promotions = mgr.promotion_check(&profiles);
    assert_eq!(promotions.len(), 1);
    assert_eq!(promotions[0].new_tier, CompilationTier::Tier1);
    assert!(
        promotions[0].specialization_plan.is_none(),
        "Tier 1 should not have specialization plan"
    );

    // Promote to Tier 2 — SHOULD have specialization plan with Int + Bool.
    let profiles = vec![profile(10, 2.0, true)];
    let promotions = mgr.promotion_check(&profiles);
    assert_eq!(promotions.len(), 1);
    assert_eq!(promotions[0].new_tier, CompilationTier::Tier2);
    let plan = promotions[0]
        .specialization_plan
        .as_ref()
        .expect("Tier 2 promotion should include specialization plan");
    assert_eq!(plan.specialized_var_count(), 2);
    assert_eq!(plan.int_var_count(), 1);
    assert_eq!(plan.bool_var_count(), 1);
    assert!(plan.has_specializable_vars());
    assert!(plan.guard_needed);
    assert!(plan.expected_speedup_factor > 1.0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier2_promotion_no_plan_without_profiling() {
    let cfg = TierConfig::new(5, 10);
    let mut mgr = TierManager::with_config(1, cfg);
    mgr.set_eligible(0);
    // Do NOT enable type profiling.

    // Promote to Tier 1, then Tier 2.
    let profiles = vec![profile(5, 1.0, true)];
    let _ = mgr.promotion_check(&profiles);
    let profiles = vec![profile(10, 2.0, true)];
    let promotions = mgr.promotion_check(&profiles);
    assert_eq!(promotions.len(), 1);
    assert_eq!(promotions[0].new_tier, CompilationTier::Tier2);
    assert!(
        promotions[0].specialization_plan.is_none(),
        "Tier 2 without profiling should have no specialization plan"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier2_no_plan_when_polymorphic() {
    let cfg = TierConfig::new(5, 10);
    let mut mgr = TierManager::with_config(1, cfg);
    mgr.set_eligible(0);
    mgr.enable_type_profiling_with_config(2, 4, 1);

    // Feed polymorphic data: variable 0 is sometimes Int, sometimes String.
    mgr.observe_state_types(&[SpecType::Int, SpecType::Bool]);
    mgr.observe_state_types(&[SpecType::String, SpecType::Bool]);
    mgr.observe_state_types(&[SpecType::Int, SpecType::Bool]);
    mgr.observe_state_types(&[SpecType::String, SpecType::Bool]);
    assert!(mgr.type_profile_stable());

    // Promote through to Tier 2.
    let _ = mgr.promotion_check(&[profile(5, 1.0, true)]);
    let promotions = mgr.promotion_check(&[profile(10, 2.0, true)]);
    assert_eq!(promotions.len(), 1);
    assert_eq!(promotions[0].new_tier, CompilationTier::Tier2);

    // Only var 1 (Bool) is monomorphic — plan should exist.
    let plan = promotions[0]
        .specialization_plan
        .as_ref()
        .expect("should have plan for Bool var");
    assert_eq!(plan.bool_var_count(), 1);
    assert_eq!(plan.int_var_count(), 0);
    assert_eq!(plan.specialized_var_count(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier2_no_plan_when_no_scalar_fast_paths() {
    let cfg = TierConfig::new(5, 10);
    let mut mgr = TierManager::with_config(1, cfg);
    mgr.set_eligible(0);
    mgr.enable_type_profiling_with_config(2, 3, 1);

    // Feed monomorphic but non-scalar types (Record, Seq).
    for _ in 0..3 {
        mgr.observe_state_types(&[SpecType::Record, SpecType::Seq]);
    }
    assert!(mgr.type_profile_stable());

    // Promote through to Tier 2.
    let _ = mgr.promotion_check(&[profile(5, 1.0, true)]);
    let promotions = mgr.promotion_check(&[profile(10, 2.0, true)]);
    assert_eq!(promotions.len(), 1);
    assert_eq!(promotions[0].new_tier, CompilationTier::Tier2);
    // No Int or Bool = no scalar fast paths = no plan.
    assert!(
        promotions[0].specialization_plan.is_none(),
        "should not have plan without scalar fast paths"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_promote_all_actions_tier2_with_specialization() {
    let cfg = TierConfig::new(5, 10);
    let mut mgr = TierManager::with_config(2, cfg);
    mgr.set_eligible(0);
    mgr.set_eligible(1);
    mgr.enable_type_profiling_with_config(3, 3, 1);

    // Feed monomorphic types.
    for _ in 0..3 {
        mgr.observe_state_types(&[SpecType::Int, SpecType::Int, SpecType::Bool]);
    }
    assert!(mgr.type_profile_stable());

    // Promote to Tier 1 first.
    let promos = mgr.promote_all_actions(CompilationTier::Tier1, 100, 2.0);
    assert_eq!(promos.len(), 2);
    for p in &promos {
        assert!(
            p.specialization_plan.is_none(),
            "Tier 1 should not have plan"
        );
    }

    // Promote to Tier 2.
    let promos = mgr.promote_all_actions(CompilationTier::Tier2, 1000, 3.0);
    assert_eq!(promos.len(), 2);
    for p in &promos {
        assert_eq!(p.new_tier, CompilationTier::Tier2);
        let plan = p
            .specialization_plan
            .as_ref()
            .expect("Tier 2 should have plan");
        assert_eq!(plan.int_var_count(), 2);
        assert_eq!(plan.bool_var_count(), 1);
        assert_eq!(plan.specialized_var_count(), 3);
    }
}
