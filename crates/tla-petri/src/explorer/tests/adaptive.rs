// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_adaptive_estimate_state_space_uses_terminal_multiplier() {
    assert_eq!(estimate_state_space(10, 0.3), 100);
}

#[test]
fn test_adaptive_estimate_state_space_uses_linear_multiplier() {
    assert_eq!(estimate_state_space(10, 1.0), 500_000);
}

#[test]
fn test_adaptive_estimate_state_space_uses_exponential_growth() {
    assert_eq!(estimate_state_space(10, 2.0), 2_560);
}

#[test]
fn test_adaptive_select_strategy_respects_thresholds_and_cap() {
    assert_eq!(
        select_strategy(PARALLEL_THRESHOLD - 1, 8),
        Strategy::Sequential
    );
    assert_eq!(
        select_strategy(PARALLEL_THRESHOLD, 8),
        Strategy::Parallel(2)
    );
    assert_eq!(
        select_strategy(MEDIUM_SPEC_THRESHOLD, 3),
        Strategy::Parallel(3)
    );
    assert_eq!(
        select_strategy(LARGE_SPEC_THRESHOLD, 6),
        Strategy::Parallel(6)
    );
}

#[test]
fn test_adaptive_select_strategy_one_worker_stays_sequential() {
    assert_eq!(
        select_strategy(LARGE_SPEC_THRESHOLD, 1),
        Strategy::Sequential
    );
}
