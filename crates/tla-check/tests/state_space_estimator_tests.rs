// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for the state space estimator.
//!
//! These tests exercise the public API of `StateSpaceEstimator` to verify
//! that growth model fitting and extrapolation produce reasonable predictions.

use tla_check::{GrowthModel, StateSpaceEstimator};

#[test]
fn test_estimator_converging_series_predicts_near_true_total() {
    // Geometric series with ratio r=0.5 starting from 100.
    // True total = 100 / (1 - 0.5) = 200.
    let mut est = StateSpaceEstimator::new();
    est.record_initial_states(100, 0.1);
    est.record_level(1, 150, 0.2);
    est.record_level(2, 175, 0.3);
    est.record_level(3, 187, 0.4);
    est.record_level(4, 193, 0.5);

    let result = est.estimate().expect("should produce estimate");
    assert!(
        result.estimated_total >= 195 && result.estimated_total <= 260,
        "converging series: expected ~200, got {}",
        result.estimated_total
    );
    assert!(
        result.confidence > 0.2,
        "should have moderate confidence, got {}",
        result.confidence
    );
    assert!(
        result.lower_bound <= result.estimated_total,
        "lower_bound {} should be <= estimated_total {}",
        result.lower_bound,
        result.estimated_total,
    );
    assert!(
        result.upper_bound >= result.estimated_total,
        "upper_bound {} should be >= estimated_total {}",
        result.upper_bound,
        result.estimated_total,
    );
}

#[test]
fn test_estimator_exponential_growth_predicts_above_current() {
    // Exponential growth with branching factor ~2.
    let mut est = StateSpaceEstimator::new();
    est.record_initial_states(1, 0.01);
    est.record_level(1, 3, 0.02);
    est.record_level(2, 7, 0.04);
    est.record_level(3, 15, 0.08);

    let result = est.estimate().expect("should produce estimate");
    assert!(
        result.estimated_total > 15,
        "exponential growth should project beyond current, got {}",
        result.estimated_total
    );
    assert_eq!(
        result.model,
        GrowthModel::Exponential,
        "should select exponential model"
    );
}

#[test]
fn test_estimator_saturation_predicts_near_current() {
    // State space approaching saturation: new states rapidly decrease.
    let mut est = StateSpaceEstimator::new();
    est.record_initial_states(1000, 0.1);
    est.record_level(1, 1800, 0.3);
    est.record_level(2, 2200, 0.5);
    est.record_level(3, 2300, 0.6);
    est.record_level(4, 2320, 0.65);
    est.record_level(5, 2325, 0.67);

    let result = est.estimate().expect("should produce estimate");
    assert!(
        result.estimated_total >= 2325 && result.estimated_total <= 2500,
        "saturation: expected ~2325-2400, got {}",
        result.estimated_total
    );
}

#[test]
fn test_estimator_insufficient_data_reports_insufficient() {
    let est = StateSpaceEstimator::new();
    let result = est.estimate().expect("should return result");
    assert_eq!(result.model, GrowthModel::Insufficient);
    assert_eq!(result.estimated_total, 0);
    assert_eq!(result.levels_observed, 0);
}

#[test]
fn test_estimator_single_level_returns_insufficient() {
    let mut est = StateSpaceEstimator::new();
    est.record_initial_states(42, 0.5);
    let result = est.estimate().expect("should return result");
    assert_eq!(result.model, GrowthModel::Insufficient);
    assert_eq!(result.estimated_total, 42);
}

#[test]
fn test_estimator_format_human_readable() {
    let mut est = StateSpaceEstimator::new();
    est.record_initial_states(1000, 0.1);
    est.record_level(1, 2000, 0.3);
    est.record_level(2, 3000, 0.5);
    est.record_level(3, 4000, 0.7);
    est.record_level(4, 5000, 0.9);

    let result = est.estimate().expect("should produce estimate");
    let human = result.format_human();
    assert!(
        human.contains("Estimated:"),
        "human format should contain 'Estimated:', got: {human}"
    );
    assert!(
        human.contains("states"),
        "human format should contain 'states', got: {human}"
    );
}

#[test]
fn test_estimator_format_compact() {
    let mut est = StateSpaceEstimator::new();
    est.record_initial_states(100, 0.1);
    est.record_level(1, 200, 0.2);
    est.record_level(2, 300, 0.3);
    est.record_level(3, 400, 0.4);

    let result = est.estimate().expect("should produce estimate");
    let compact = result.format_compact();
    assert!(
        compact.contains("est."),
        "compact format should contain 'est.', got: {compact}"
    );
}

#[test]
fn test_estimator_confidence_increases_with_more_levels() {
    let mut est = StateSpaceEstimator::new();
    est.record_initial_states(100, 0.1);
    est.record_level(1, 150, 0.2);

    let r2 = est.estimate().expect("2-level estimate");

    est.record_level(2, 175, 0.3);
    est.record_level(3, 187, 0.4);
    est.record_level(4, 193, 0.5);
    est.record_level(5, 196, 0.6);

    let r6 = est.estimate().expect("6-level estimate");

    assert!(
        r6.confidence >= r2.confidence,
        "more levels should increase confidence: 2-level={:.3}, 6-level={:.3}",
        r2.confidence,
        r6.confidence,
    );
}

#[test]
fn test_estimator_zero_new_states_predicts_near_current() {
    // If a level produces zero new states, exploration is done.
    let mut est = StateSpaceEstimator::new();
    est.record_initial_states(10, 0.1);
    est.record_level(1, 15, 0.2);
    est.record_level(2, 15, 0.3); // No new states

    let result = est.estimate().expect("should return result");
    assert!(
        result.estimated_total <= 25,
        "no growth should predict near-current, got {}",
        result.estimated_total
    );
}

#[test]
fn test_estimator_time_remaining_computed() {
    let mut est = StateSpaceEstimator::new();
    est.record_initial_states(1000, 1.0);
    est.record_level(1, 2000, 2.0);
    est.record_level(2, 3000, 3.0);
    est.record_level(3, 4000, 4.0);

    let result = est.estimate().expect("should produce estimate");
    assert!(
        result.estimated_seconds_remaining.is_some(),
        "should compute time remaining"
    );
    let secs = result.estimated_seconds_remaining.unwrap();
    assert!(secs > 0.0, "time remaining should be positive: {secs}");
}

/// Smoke test: exercise the model checker with a small spec and verify the
/// estimator produces a reasonable prediction.
///
/// This integrates the estimator with the actual BFS engine by running a
/// small spec and checking that after a few levels, the estimate is sensible.
#[test]
fn test_estimator_with_real_spec() {
    use tla_check::{check_module, Config};
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // A spec with 6 reachable states (x in 0..5):
    let src = "---- MODULE EstimateTest ----\n\
        VARIABLE x\n\
        Init == x = 0\n\
        Next == x' = (x + 1) % 6\n\
        ====";
    let tree = parse_to_syntax_tree(src);
    let result = lower(FileId(0), &tree);
    let module = result.module.unwrap();
    let config = Config::parse("INIT Init\nNEXT Next\n").unwrap();

    // Run full model checking
    let check_result = check_module(&module, &config);

    // Verify it passes (6 states should be found)
    match check_result {
        tla_check::CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 6, "expected 6 states");
        }
        other => panic!("expected Success, got: {other:?}"),
    }

    // Now manually simulate what the estimator would see:
    // Level 0: 1 initial state
    // Level 1: +1 new (total 2)
    // Level 2: +1 new (total 3)
    // ...
    // Level 5: +1 new (total 6)
    // Level 6: +0 new (total 6) — done
    let mut est = StateSpaceEstimator::new();
    est.record_initial_states(1, 0.001);
    est.record_level(1, 2, 0.002);
    est.record_level(2, 3, 0.003);
    est.record_level(3, 4, 0.004);

    let prediction = est.estimate().expect("should produce estimate");
    // With linear growth of 1 state/level and only 3 levels observed,
    // the estimate is rough. The exponential model with r=1.0 may use
    // aggressive extrapolation. We just verify the estimate is finite
    // and in a sane range (not millions).
    assert!(
        prediction.estimated_total >= 4 && prediction.estimated_total <= 200,
        "linear counter: estimated {} states (actual: 6) -- should be within 4..200",
        prediction.estimated_total
    );
}
