// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression tests for ExitRequested during BFS successor processing.
//!
//! The existing `*_exit_requested_init.rs` tests cover only init-time
//! propagation. These tests cover successor-time action execution,
//! successor-time invariant checking, and VIEW fingerprint evaluation.

mod common;

use tla_check::{CheckResult, Config, LimitType, ModelChecker, ParallelChecker};

/// Sequential BFS: ExitRequested during Next action should stop with
/// LimitReached(Exit), not a hard error.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sequential_exit_requested_during_next_action_is_limit_reached() {
    let src = r#"
---- MODULE SeqExitDuringNext ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = x + 1 /\ TLCSet("exit", TRUE)
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
            assert_eq!(limit_type, LimitType::Exit);
        }
        other => panic!("sequential: expected LimitReached(Exit) from Next action, got: {other:?}"),
    }
}

/// Full-state sequential BFS: ExitRequested during Next action should stop with
/// LimitReached(Exit), not a hard error.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_full_state_exit_requested_during_next_action_is_limit_reached() {
    let src = r#"
---- MODULE FullStateExitDuringNext ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = x + 1 /\ TLCSet("exit", TRUE)
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    checker.set_deadlock_check(false);
    let result = checker.check();
    match result {
        CheckResult::LimitReached { limit_type, .. } => {
            assert_eq!(limit_type, LimitType::Exit);
        }
        other => panic!("full-state: expected LimitReached(Exit) from Next action, got: {other:?}"),
    }
}

/// Parallel BFS: worker-side ExitRequested during successor generation should
/// be surfaced as LimitReached(Exit).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_exit_requested_during_next_action_is_limit_reached() {
    let src = r#"
---- MODULE ParExitDuringNext ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = x + 1 /\ TLCSet("exit", TRUE)
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    let result = checker.check();
    match result {
        CheckResult::LimitReached { limit_type, .. } => {
            assert_eq!(limit_type, LimitType::Exit);
        }
        other => panic!("parallel: expected LimitReached(Exit) from Next action, got: {other:?}"),
    }
}

/// Sequential BFS: ExitRequested raised by an invariant on a successor state
/// should stop with LimitReached(Exit).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sequential_exit_requested_during_successor_invariant_is_limit_reached() {
    let src = r#"
---- MODULE SeqExitDuringSuccInvariant ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == IF x > 0 THEN TLCSet("exit", TRUE) ELSE TRUE
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
            assert_eq!(limit_type, LimitType::Exit);
        }
        other => panic!(
            "sequential: expected LimitReached(Exit) from successor invariant, got: {other:?}"
        ),
    }
}

/// Sequential full-state BFS: ExitRequested raised while evaluating VIEW for
/// fingerprinting should also stop with LimitReached(Exit).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exit_requested_during_view_fingerprint_is_limit_reached() {
    let src = r#"
---- MODULE ExitDuringView ----
EXTENDS TLC
VARIABLE x
Init == x = 0
Next == x' = x + 1
ExitView == TLCSet("exit", TRUE)
====
"#;
    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        view: Some("ExitView".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(true);
    checker.set_deadlock_check(false);
    let result = checker.check();
    match result {
        CheckResult::LimitReached { limit_type, .. } => {
            assert_eq!(limit_type, LimitType::Exit);
        }
        other => {
            panic!("view fingerprint: expected LimitReached(Exit) from VIEW eval, got: {other:?}")
        }
    }
}
