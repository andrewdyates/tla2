// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core sequential/parallel parity regression tests.

use super::*;

/// Regression guard for #1283: parallel/sequential parity on basic success spec.
/// Split from suite to isolate ParityTestScope per sub-case — prevents stale
/// thread-local state from cascading between ParallelChecker invocations (#3384).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_sequential_success_parity() {
    let _scope = ParityTestScope::begin();
    let success_spec = r#"
---- MODULE ParitySuccess ----
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
TypeOK == x \in 0..3
====
"#;

    let success_config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        check_deadlock: false,
        ..Default::default()
    };
    assert_parallel_sequential_parity("success", success_spec, success_config, 4, Some((4, 1)));
}

/// Regression guard for #1283: parallel/sequential parity on invariant violation.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_sequential_invariant_violation_parity() {
    let _scope = ParityTestScope::begin();
    let invariant_violation_spec = r#"
---- MODULE ParityInvariantViolation ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safe == x < 2
====
"#;

    let invariant_violation_config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safe".to_string()],
        check_deadlock: false,
        ..Default::default()
    };
    assert_parallel_sequential_parity(
        "invariant_violation",
        invariant_violation_spec,
        invariant_violation_config,
        4,
        None,
    );
}

/// Regression guard for #1281: TLCGet/View off-by-one in parallel checker.
/// Uses action constraints and view expressions which exercise distinct
/// ParallelChecker code paths.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_sequential_view_level_parity() {
    let _scope = ParityTestScope::begin();
    let level_view_spec = r#"
---- MODULE ParityViewLevel ----
EXTENDS TLC, Naturals

VARIABLES x, y

Init == x \in {1, 2, 3} /\ y = 0
Next == /\ x' \in {1, 2, 3}
        /\ y' = y + 1

DepthBound == TLCGet("level") <= 4
LevelView == <<x, y, TLCGet("level")>>
====
"#;

    let level_view_config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        action_constraints: vec!["DepthBound".to_string()],
        view: Some("LevelView".to_string()),
        check_deadlock: false,
        ..Default::default()
    };
    assert_parallel_sequential_parity(
        "view_level_regression_1281",
        level_view_spec,
        level_view_config,
        4,
        Some((15, 3)),
    );
}

/// Regression test for #1906: parallel checker reported inflated states_found
/// after violations because workers continued inserting states between
/// stop_flag being set and their loops checking it.
///
/// This spec has 3 initial states and branching successors, creating enough
/// parallelism for post-violation state insertion. The invariant triggers at
/// depth 2, while other workers may still be exploring depth 1 branches.
///
/// Prior to #1906 fix, the parallel checker could report states_found > serial
/// because finalize_check read states_count() after all workers terminated,
/// including states inserted after the first violation was detected.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_1906_parallel_violation_state_count_parity() {
    let _scope = ParityTestScope::begin();
    // Branching spec: 3 initial states, each can transition to 3 values.
    // x ∈ {0,1,2} initially; Next picks any value in {0,1,2,3}.
    // Invariant fails when x = 3.
    // State space: {0,1,2,3} = 4 states, violation at x=3.
    // The branching ensures multiple workers explore concurrently.
    let spec = r#"
---- MODULE Parity1906 ----
EXTENDS Naturals
VARIABLE x
Init == x \in {0, 1, 2}
Next == x' \in {0, 1, 2, 3}
Safe == x # 3
====
"#;

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safe".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    // Run with increasing worker counts to stress the race window.
    // With the #1906 fix (states_at_stop snapshot), all worker counts
    // should report the same states_found as sequential.
    for workers in [2, 4, 8] {
        assert_parallel_sequential_parity(
            &format!("1906_violation_parity_{workers}w"),
            spec,
            config.clone(),
            workers,
            None,
        );
    }
}
