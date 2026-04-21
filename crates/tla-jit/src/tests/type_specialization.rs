// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for JIT V2 Phase 6: speculative type specialization.
//!
//! These tests exercise the full pipeline:
//!   TypeProfiler -> TypeProfile -> SpecializationPlan -> SpeculativeState
//!     -> RecompilationController -> DeoptimizationTracker
//!
//! Verifies that the orchestrator correctly sequences profiling, plan
//! construction, recompilation triggering, and deoptimization tracking.
//!
//! Part of #3989: JIT V2 Phase 6 speculative type specialization.

use crate::deoptimization::DeoptAction;
use crate::speculative::{SpeculativeEvent, SpeculativePhase, SpeculativeState};
use crate::tiered::{ActionProfile, CompilationTier, TierConfig, TierManager};
use crate::type_profile::{classify_value, SpecType, TypeProfile, TypeProfiler};
use crate::type_specializer::SpecializationPlan;
use tla_value::Value;

// ---------------------------------------------------------------------------
// End-to-end: profiling through Value classification to plan
// ---------------------------------------------------------------------------

/// Verify that `classify_value` produces the expected SpecType for common
/// Value variants, and that a profile built from classified values produces
/// a viable specialization plan.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_classify_values_to_specialization_plan() {
    // Simulate state variables: [counter: Int, flag: Bool, name: String]
    let states: Vec<Vec<Value>> = vec![
        vec![Value::SmallInt(0), Value::Bool(true), Value::string("a")],
        vec![Value::SmallInt(1), Value::Bool(false), Value::string("b")],
        vec![Value::SmallInt(2), Value::Bool(true), Value::string("c")],
        vec![Value::SmallInt(42), Value::Bool(false), Value::string("d")],
    ];

    let mut profiler = TypeProfiler::with_config(3, 4, 1);
    for state in &states {
        let types: Vec<SpecType> = state.iter().map(|v| classify_value(v)).collect();
        assert_eq!(types.len(), 3);
        profiler.observe_state(&types);
    }

    assert!(profiler.is_stable());
    let profile = profiler.profile();

    // All three variables should be monomorphic.
    assert!(profile.is_fully_monomorphic());
    assert_eq!(
        profile.monomorphic_types(),
        vec![Some(SpecType::Int), Some(SpecType::Bool), Some(SpecType::String)]
    );

    // Build specialization plan.
    let plan = SpecializationPlan::from_profile(profile);
    assert!(plan.guard_needed);
    // Int and Bool are specializable scalar fast paths; String is monomorphic
    // but not a scalar fast path.
    assert!(plan.has_specializable_vars());
    assert_eq!(plan.int_var_count(), 1);
    assert_eq!(plan.bool_var_count(), 1);
    assert_eq!(plan.specialized_var_count(), 3); // Int + Bool + String
    assert!(plan.expected_speedup_factor > 1.0);
}

// ---------------------------------------------------------------------------
// End-to-end: speculative orchestrator lifecycle
// ---------------------------------------------------------------------------

/// Full lifecycle test: profiling -> plan ready -> recompiling -> active -> deopt.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_speculative_orchestrator_full_lifecycle_with_values() {
    // 2 state variables, warmup=3, sampling_rate=1, enabled.
    let mut state = SpeculativeState::with_test_config(
        2,
        3,
        1,
        crate::speculative::SpeculativeConfig {
            min_speedup_threshold: 1.01,
            enabled: true,
        },
    );

    assert_eq!(state.phase(), &SpeculativePhase::Profiling);

    // Feed 2 observations (not enough to stabilize).
    assert!(state
        .observe_state(&[SpecType::Int, SpecType::Bool])
        .is_none());
    assert!(state
        .observe_state(&[SpecType::Int, SpecType::Bool])
        .is_none());
    assert_eq!(state.phase(), &SpeculativePhase::Profiling);

    // 3rd observation stabilizes the profile.
    let event = state.observe_state(&[SpecType::Int, SpecType::Bool]);
    match event {
        Some(SpeculativeEvent::ProfileStabilized { ref plan }) => {
            assert!(plan.has_specializable_vars());
            assert_eq!(plan.int_var_count(), 1);
            assert_eq!(plan.bool_var_count(), 1);
        }
        other => panic!("expected ProfileStabilized, got: {other:?}"),
    }
    assert_eq!(state.phase(), &SpeculativePhase::PlanReady);

    // Transition to recompiling.
    assert!(state.pending_plan().is_some());
    state.mark_recompiling();
    assert_eq!(state.phase(), &SpeculativePhase::Recompiling);

    // Transition to active.
    state.mark_active();
    assert_eq!(state.phase(), &SpeculativePhase::Active);

    // Record some specialized states.
    state.record_specialized_state();
    state.record_specialized_state();
    state.record_specialized_state();

    let stats = state.stats();
    assert_eq!(stats.phase, "active");
    assert_eq!(stats.profile_states_sampled, 3);
    assert!(stats.plan_speedup.is_some());
    let deopt = stats.deopt.expect("active state should expose deopt stats");
    assert_eq!(deopt.deopt_count, 0);
    assert_eq!(deopt.states_since_specialization, 3);

    // Trigger deopt (type assumption violated).
    let action = state.record_deopt();
    assert_eq!(action, DeoptAction::Abandon);
    assert_eq!(state.phase(), &SpeculativePhase::Abandoned);
}

// ---------------------------------------------------------------------------
// End-to-end: TierManager type profiling -> Tier 2 promotion with plan
// ---------------------------------------------------------------------------

/// Verify that the TierManager correctly propagates type profiling results
/// into Tier 2 promotion events with specialization plans.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tier_manager_type_profiling_produces_plan_on_tier2() {
    let cfg = TierConfig::new(5, 15);
    let mut mgr = TierManager::with_config(2, cfg);
    mgr.set_eligible(0);
    mgr.set_eligible(1);

    // Enable type profiling for 3 state variables with warmup=4.
    mgr.enable_type_profiling_with_config(3, 4, 1);

    // Feed monomorphic observations (Int, Int, Bool).
    for _ in 0..4 {
        let stabilized = mgr.observe_state_types(&[SpecType::Int, SpecType::Int, SpecType::Bool]);
        if stabilized {
            break;
        }
    }
    assert!(mgr.type_profile_stable());

    // Verify the profile contents.
    let profile = mgr.type_profile().expect("profiler should be active");
    assert!(profile.is_fully_monomorphic());
    assert_eq!(
        profile.monomorphic_types(),
        vec![Some(SpecType::Int), Some(SpecType::Int), Some(SpecType::Bool)]
    );

    // Promote to Tier 1 (no plan expected).
    let profiles = vec![
        ActionProfile {
            times_evaluated: 5,
            branching_factor: 1.0,
            jit_eligible: true,
        },
        ActionProfile {
            times_evaluated: 5,
            branching_factor: 1.0,
            jit_eligible: true,
        },
    ];
    let promotions = mgr.promotion_check(&profiles);
    assert_eq!(promotions.len(), 2);
    for p in &promotions {
        assert_eq!(p.new_tier, CompilationTier::Tier1);
        assert!(
            p.specialization_plan.is_none(),
            "Tier 1 should not carry a specialization plan"
        );
    }

    // Promote to Tier 2 (plan expected).
    let profiles = vec![
        ActionProfile {
            times_evaluated: 15,
            branching_factor: 2.0,
            jit_eligible: true,
        },
        ActionProfile {
            times_evaluated: 15,
            branching_factor: 2.0,
            jit_eligible: true,
        },
    ];
    let promotions = mgr.promotion_check(&profiles);
    assert_eq!(promotions.len(), 2);
    for p in &promotions {
        assert_eq!(p.new_tier, CompilationTier::Tier2);
        let plan = p
            .specialization_plan
            .as_ref()
            .expect("Tier 2 promotion should carry specialization plan");
        assert!(plan.has_specializable_vars());
        assert_eq!(plan.int_var_count(), 2);
        assert_eq!(plan.bool_var_count(), 1);
        assert_eq!(plan.specialized_var_count(), 3);
        assert!(plan.expected_speedup_factor > 1.0);
    }
}

// ---------------------------------------------------------------------------
// Polymorphic state variables: no specialization plan
// ---------------------------------------------------------------------------

/// When state variables have mixed types across states, the plan should
/// reflect only the monomorphic subset.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_polymorphic_variables_produce_partial_plan() {
    let mut profiler = TypeProfiler::with_config(3, 4, 1);

    // var 0: always Int (monomorphic)
    // var 1: sometimes Bool, sometimes Int (polymorphic)
    // var 2: always Bool (monomorphic)
    profiler.observe_state(&[SpecType::Int, SpecType::Bool, SpecType::Bool]);
    profiler.observe_state(&[SpecType::Int, SpecType::Int, SpecType::Bool]);
    profiler.observe_state(&[SpecType::Int, SpecType::Bool, SpecType::Bool]);
    profiler.observe_state(&[SpecType::Int, SpecType::Int, SpecType::Bool]);

    assert!(profiler.is_stable());
    let profile = profiler.profile();

    assert!(!profile.is_fully_monomorphic());
    assert_eq!(
        profile.monomorphic_types(),
        vec![Some(SpecType::Int), None, Some(SpecType::Bool)]
    );

    let plan = SpecializationPlan::from_profile(profile);
    // var 0 (Int) and var 2 (Bool) are specializable; var 1 is polymorphic.
    assert_eq!(plan.specialized_var_count(), 2);
    assert_eq!(plan.int_var_count(), 1);
    assert_eq!(plan.bool_var_count(), 1);
    assert!(plan.has_specializable_vars());
    assert!(plan.guard_needed);
}

// ---------------------------------------------------------------------------
// Sampling rate: verify correct sub-sampling behavior
// ---------------------------------------------------------------------------

/// With sampling_rate=3, only every 3rd state should be recorded.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_profiler_sampling_rate_filters_observations() {
    let mut profiler = TypeProfiler::with_config(1, 2, 3);

    // States 1, 2, 3: only state 1 and state 4 are sampled (rate=3).
    assert!(!profiler.observe_state(&[SpecType::Int])); // sampled (1st)
    assert!(!profiler.observe_state(&[SpecType::Bool])); // skipped (2nd)
    assert!(!profiler.observe_state(&[SpecType::String])); // skipped (3rd)
    assert!(profiler.observe_state(&[SpecType::Int])); // sampled (4th = 2nd sample, stabilizes)

    assert!(profiler.is_stable());
    let profile = profiler.profile();
    assert_eq!(profile.total_states(), 2);
    // Only Int was sampled (states 1 and 4 both had Int).
    assert!(profile.is_fully_monomorphic());
    assert_eq!(profile.monomorphic_types(), vec![Some(SpecType::Int)]);
}

// ---------------------------------------------------------------------------
// Disabled speculation: verify no profiling or plan generation
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_disabled_speculation_skips_all_phases() {
    let mut state = SpeculativeState::disabled();

    assert_eq!(state.phase(), &SpeculativePhase::Disabled);

    // Observations are ignored.
    assert!(state
        .observe_state(&[SpecType::Int, SpecType::Bool])
        .is_none());
    assert_eq!(state.phase(), &SpeculativePhase::Disabled);

    // No pending plan.
    assert!(state.pending_plan().is_none());

    // Deopt is a no-op.
    assert_eq!(state.record_deopt(), DeoptAction::Continue);

    let stats = state.stats();
    assert_eq!(stats.phase, "disabled");
    assert_eq!(stats.profile_states_sampled, 0);
    assert!(stats.plan_speedup.is_none());
    assert!(stats.deopt.is_none());
}

// ---------------------------------------------------------------------------
// Value classification coverage
// ---------------------------------------------------------------------------

/// Verify classify_value maps all major Value variants correctly.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_classify_value_complete_coverage() {
    use std::sync::Arc;
    use tla_value::{FuncBuilder, IntIntervalFunc};

    assert_eq!(classify_value(&Value::SmallInt(0)), SpecType::Int);
    assert_eq!(classify_value(&Value::SmallInt(-1)), SpecType::Int);
    assert_eq!(classify_value(&Value::SmallInt(i64::MAX)), SpecType::Int);
    assert_eq!(classify_value(&Value::Bool(true)), SpecType::Bool);
    assert_eq!(classify_value(&Value::Bool(false)), SpecType::Bool);
    assert_eq!(classify_value(&Value::string("")), SpecType::String);
    assert_eq!(
        classify_value(&Value::string("hello world")),
        SpecType::String
    );
    assert_eq!(
        classify_value(&Value::set([Value::SmallInt(1)])),
        SpecType::FiniteSet
    );
    assert_eq!(
        classify_value(&Value::record([("x", Value::SmallInt(1))])),
        SpecType::Record
    );
    assert_eq!(
        classify_value(&Value::seq([Value::SmallInt(1)])),
        SpecType::Seq
    );
    assert_eq!(
        classify_value(&Value::tuple([Value::SmallInt(1), Value::Bool(false)])),
        SpecType::Tuple
    );

    let mut fb = FuncBuilder::new();
    fb.insert(Value::SmallInt(1), Value::SmallInt(2));
    assert_eq!(classify_value(&Value::Func(Arc::new(fb.build()))), SpecType::Func);

    let ifunc = IntIntervalFunc::new(1, 3, vec![Value::SmallInt(10), Value::SmallInt(20), Value::SmallInt(30)]);
    assert_eq!(
        classify_value(&Value::IntFunc(Arc::new(ifunc))),
        SpecType::Func
    );
}
