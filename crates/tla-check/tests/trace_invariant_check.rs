// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for Apalache-style `--trace-inv` trace invariant checking.
//!
//! Trace invariants are operators that take a `Seq(Record)` argument representing
//! the execution history up to the current state. The checker calls them at each
//! BFS state via `eval_op_with_args`. Part of #3780.

mod common;

use tla_check::{CheckResult, Config, ModelChecker};

/// Test that a passing trace invariant (monotonically increasing x) succeeds.
///
/// Spec: x starts at 0, increments by 1 each step, up to 4.
/// Trace invariant: for all consecutive pairs in the history, x is non-decreasing.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_invariant_monotonic_pass() {
    let src = r#"
---- MODULE TraceInvMonotonicPass ----
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = 0
Next == x < 4 /\ x' = x + 1
MonotonicTrace(history) ==
    \A i \in 1..(Len(history) - 1) :
        history[i + 1].x >= history[i].x
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        trace_invariants: vec!["MonotonicTrace".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            // x goes from 0 to 4, so 5 states.
            assert_eq!(
                stats.states_found, 5,
                "Expected 5 states (x=0..4), got {}",
                stats.states_found
            );
        }
        other => panic!("Expected Success, got: {other:?}"),
    }
}

/// Test that a failing trace invariant (x should be strictly decreasing) reports a violation.
///
/// Spec: x starts at 0, increments by 1 each step, up to 4.
/// Trace invariant: x must be strictly decreasing (which is violated immediately on
/// the second state, since x goes from 0 to 1).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_invariant_violation_detected() {
    let src = r#"
---- MODULE TraceInvDecreasingFail ----
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = 0
Next == x < 4 /\ x' = x + 1
DecreasingTrace(history) ==
    \A i \in 1..(Len(history) - 1) :
        history[i + 1].x < history[i].x
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        trace_invariants: vec!["DecreasingTrace".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::InvariantViolation {
            invariant, trace, ..
        } => {
            assert_eq!(
                invariant, "DecreasingTrace",
                "Expected DecreasingTrace violation, got: {invariant}"
            );
            // The trace should have at least 2 states (init + first step where violation occurs).
            assert!(
                trace.states.len() >= 2,
                "Expected trace with >= 2 states, got {}",
                trace.states.len()
            );
        }
        other => panic!("Expected InvariantViolation, got: {other:?}"),
    }
}

/// Test trace invariant checking with multiple variables.
///
/// Spec: x counts up, y counts down. Trace invariant checks that x + y is constant
/// across the history (conservation law).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_invariant_multi_variable_conservation() {
    let src = r#"
---- MODULE TraceInvConservation ----
EXTENDS Naturals, Sequences
VARIABLES x, y
Init == x = 0 /\ y = 5
Next == x < 5 /\ x' = x + 1 /\ y' = y - 1
\* Conservation: x + y should be constant (5) across all states in the trace.
ConservedTrace(history) ==
    \A i \in 1..Len(history) :
        history[i].x + history[i].y = 5
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        trace_invariants: vec!["ConservedTrace".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 6,
                "Expected 6 states (x=0..5, y=5..0), got {}",
                stats.states_found
            );
        }
        other => panic!("Expected Success, got: {other:?}"),
    }
}

/// Test a "no repeated state" trace invariant (all values of x in the trace are distinct).
///
/// Spec: x starts at 0, increments by 1 each step up to 3.
/// Trace invariant: no two entries in the history have the same value of x.
/// Since x is strictly increasing, this should pass.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_invariant_no_repeated_state_pass() {
    let src = r#"
---- MODULE TraceInvNoRepeatPass ----
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
\* All x values in the history are distinct.
NoRepeatTrace(history) ==
    \A i \in 1..Len(history) :
        \A j \in 1..Len(history) :
            (i /= j) => (history[i].x /= history[j].x)
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        trace_invariants: vec!["NoRepeatTrace".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 4,
                "Expected 4 states (x=0..3), got {}",
                stats.states_found
            );
        }
        other => panic!("Expected Success, got: {other:?}"),
    }
}

/// Test a "no repeated state" trace invariant detects a violation.
///
/// Spec: x oscillates between 0 and 1 (x' = 1 - x), with a turn counter y
/// that increments each step to ensure distinct BFS states.
/// Trace invariant: no two entries in the history have the same value of x.
/// This must fail when x returns to 0 on the third state (y=2, x=0).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_invariant_no_repeated_state_violation() {
    let src = r#"
---- MODULE TraceInvNoRepeatFail ----
EXTENDS Naturals, Sequences
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = 1 - x /\ y' = y + 1 /\ y < 3
\* x values must be distinct across the trace -- violated at step 2 when x returns to 0.
NoRepeatX(history) ==
    \A i \in 1..Len(history) :
        \A j \in 1..Len(history) :
            (i /= j) => (history[i].x /= history[j].x)
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        trace_invariants: vec!["NoRepeatX".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::InvariantViolation {
            invariant, trace, ..
        } => {
            assert_eq!(
                invariant, "NoRepeatX",
                "Expected NoRepeatX violation, got: {invariant}"
            );
            // The violation happens at the third state (y=2, x=0 repeats x=0 from init).
            // Trace must have at least 3 states: init + step1 + step2.
            assert!(
                trace.states.len() >= 3,
                "Expected trace with >= 3 states for repeated-x detection, got {}",
                trace.states.len()
            );
        }
        other => panic!("Expected InvariantViolation, got: {other:?}"),
    }
}

/// Test that a trace invariant checking history length works correctly.
///
/// The history at depth d should have exactly d+1 elements (init + d steps).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_trace_invariant_history_length() {
    let src = r#"
---- MODULE TraceInvHistLen ----
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
\* History length should always be x + 1 (since x starts at 0 and increments by 1).
HistLenInv(history) == Len(history) = history[Len(history)].x + 1
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        trace_invariants: vec!["HistLenInv".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 4,
                "Expected 4 states (x=0..3), got {}",
                stats.states_found
            );
        }
        other => panic!("Expected Success, got: {other:?}"),
    }
}
