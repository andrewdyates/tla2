// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for #2789: ExitRequested during sequential initial state
//! processing must produce `LimitReached(Exit)`, not `Error`.
//!
//! Before the fix, `run_bfs_full.rs` constructed `CheckResult::Error` directly
//! at 5 sites in constrained_initial_states, check_init_state, and
//! init_states_full_state, bypassing the `check_error_to_result` mapping that
//! converts `ExitRequested` to `LimitReached(Exit)` (established by #254).
//!
//! The notrace-mode tests (with `set_store_states(false)`) exercise the
//! corresponding code path in `run_bfs_notrace.rs`, where the same bug class
//! existed at the `generate_initial_states_to_bulk` error site (line 83-86).
//!
//! These are the sequential counterparts to the parallel tests in
//! `parallel_exit_requested_init.rs` (which cover #2777).

mod common;

use tla_check::{CheckResult, LimitType};
use tla_check::{Config, ModelChecker};

// ---------------------------------------------------------------------------
// Full-trace (sequential) mode: exercises run_bfs_full.rs
// ---------------------------------------------------------------------------

/// Regression test for #2789 bug site (invariant check in check_init_state).
///
/// An invariant that calls `TLCSet("exit", TRUE)` raises `ExitRequested`
/// during initial state invariant evaluation. The sequential checker must
/// convert this to `LimitReached(Exit)` via `check_error_to_result`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sequential_exit_requested_during_init_invariant_is_limit_reached() {
    let src = r#"
---- MODULE SeqExitDuringInitInvariant ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = x
\* Invariant triggers ExitRequested on every state check
Inv == TLCSet("exit", TRUE)
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();
    match result {
        CheckResult::LimitReached { limit_type, .. } => {
            assert_eq!(
                limit_type,
                LimitType::Exit,
                "sequential: expected Exit limit"
            );
        }
        other => panic!("sequential: expected LimitReached(Exit), got: {other:?}"),
    }
}

/// Regression test for #2789 bug site (constraint check in constrained_initial_states).
///
/// A CONSTRAINT that calls `TLCSet("exit", TRUE)` raises `ExitRequested`
/// during initial state constraint evaluation. The sequential checker must
/// convert this to `LimitReached(Exit)` via `check_error_to_result`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sequential_exit_requested_during_init_constraint_is_limit_reached() {
    let src = r#"
---- MODULE SeqExitDuringInitConstraint ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = x
ExitConstraint == TLCSet("exit", TRUE)
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constraints: vec!["ExitConstraint".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();
    match result {
        CheckResult::LimitReached { limit_type, .. } => {
            assert_eq!(
                limit_type,
                LimitType::Exit,
                "sequential: expected Exit limit"
            );
        }
        other => panic!("sequential: expected LimitReached(Exit), got: {other:?}"),
    }
}

/// Regression test for #2789 bug site (generate_initial_states error in
/// constrained_initial_states and generate_initial_states_to_bulk in
/// init_states_full_state).
///
/// Init that calls `TLCSet("exit", TRUE)` raises `ExitRequested` during
/// initial state generation. The sequential checker must convert this to
/// `LimitReached(Exit)`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sequential_exit_requested_during_init_generation_is_limit_reached() {
    let src = r#"
---- MODULE SeqExitDuringInitGeneration ----
EXTENDS TLC
VARIABLE x
\* Init triggers ExitRequested during state generation
Init == x = 0 /\ TLCSet("exit", TRUE)
Next == x' = x
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();
    match result {
        CheckResult::LimitReached { limit_type, .. } => {
            assert_eq!(
                limit_type,
                LimitType::Exit,
                "sequential: expected Exit limit from init generation"
            );
        }
        other => panic!("sequential: expected LimitReached(Exit), got: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Notrace (fingerprint-only) mode: exercises run_bfs_notrace.rs
//
// These tests verify that the same ExitRequested → LimitReached(Exit)
// mapping works in the fingerprint-only BFS loop, which uses a separate
// code path from the full-trace sequential mode.
// ---------------------------------------------------------------------------

/// Notrace-mode counterpart: invariant triggering ExitRequested.
///
/// Exercises `run_bfs_notrace.rs` init state processing via
/// `set_store_states(false)`. Before commit cc2f17fd, ExitRequested was
/// misreported as Error in the fingerprint-only BFS loop.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_notrace_exit_requested_during_init_invariant_is_limit_reached() {
    let src = r#"
---- MODULE NoTraceExitDuringInitInvariant ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = x
\* Invariant triggers ExitRequested on every state check
Inv == TLCSet("exit", TRUE)
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(false); // notrace mode → run_bfs_notrace.rs
    checker.set_deadlock_check(false);
    let result = checker.check();
    match result {
        CheckResult::LimitReached { limit_type, .. } => {
            assert_eq!(
                limit_type,
                LimitType::Exit,
                "notrace: expected Exit limit from init invariant"
            );
        }
        other => panic!("notrace: expected LimitReached(Exit), got: {other:?}"),
    }
}

/// Notrace-mode counterpart: constraint triggering ExitRequested.
///
/// Exercises `run_bfs_notrace.rs` constraint path via `set_store_states(false)`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_notrace_exit_requested_during_init_constraint_is_limit_reached() {
    let src = r#"
---- MODULE NoTraceExitDuringInitConstraint ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = x
ExitConstraint == TLCSet("exit", TRUE)
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constraints: vec!["ExitConstraint".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(false); // notrace mode → run_bfs_notrace.rs
    checker.set_deadlock_check(false);
    let result = checker.check();
    match result {
        CheckResult::LimitReached { limit_type, .. } => {
            assert_eq!(
                limit_type,
                LimitType::Exit,
                "notrace: expected Exit limit from init constraint"
            );
        }
        other => panic!("notrace: expected LimitReached(Exit), got: {other:?}"),
    }
}

/// Notrace-mode counterpart: init generation triggering ExitRequested.
///
/// Exercises `run_bfs_notrace.rs` `generate_initial_states_to_bulk` error
/// path (line 83-86) via `set_store_states(false)`. This is the primary
/// site that W5 fixed in commit cc2f17fd.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_notrace_exit_requested_during_init_generation_is_limit_reached() {
    let src = r#"
---- MODULE NoTraceExitDuringInitGeneration ----
EXTENDS TLC
VARIABLE x
\* Init triggers ExitRequested during state generation
Init == x = 0 /\ TLCSet("exit", TRUE)
Next == x' = x
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(false); // notrace mode → run_bfs_notrace.rs
    checker.set_deadlock_check(false);
    let result = checker.check();
    match result {
        CheckResult::LimitReached { limit_type, .. } => {
            assert_eq!(
                limit_type,
                LimitType::Exit,
                "notrace: expected Exit limit from init generation"
            );
        }
        other => panic!("notrace: expected LimitReached(Exit), got: {other:?}"),
    }
}
