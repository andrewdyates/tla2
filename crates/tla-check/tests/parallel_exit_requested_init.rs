// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #2777: ExitRequested during parallel initial state
//! processing must produce `LimitReached(Exit)`, not `Error`.
//!
//! Before the fix, `process_initial_state` constructed `CheckResult::Error`
//! directly at 4 sites, bypassing the `check_error_to_result` mapping that
//! converts `ExitRequested` to `LimitReached(Exit)` (established by #254).

mod common;

use tla_check::Config;
use tla_check::ParallelChecker;
use tla_check::{CheckResult, LimitType};

/// Regression test for #2777 bug site #4 (invariant check).
///
/// An invariant that calls `TLCSet("exit", TRUE)` raises `ExitRequested`
/// during initial state invariant evaluation. The parallel checker must
/// convert this to `LimitReached(Exit)` via `check_error_to_result`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_exit_requested_during_init_invariant_is_limit_reached() {
    let src = r#"
---- MODULE ExitDuringInitInvariant ----
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

    // Parallel checker: this is the path that was broken before #2777 fix.
    // ExitRequested during init invariant check must map to LimitReached(Exit).
    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    let result = checker.check();
    match result {
        CheckResult::LimitReached { limit_type, .. } => {
            assert_eq!(limit_type, LimitType::Exit, "parallel: expected Exit limit");
        }
        other => panic!("parallel: expected LimitReached(Exit), got: {other:?}"),
    }
}

/// Regression test for #2777 bug site #1 (state constraint check).
///
/// A CONSTRAINT that calls `TLCSet("exit", TRUE)` raises `ExitRequested`
/// during initial state constraint evaluation. The parallel checker must
/// convert this to `LimitReached(Exit)` via `check_error_to_result`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_exit_requested_during_init_constraint_is_limit_reached() {
    let src = r#"
---- MODULE ExitDuringInitConstraint ----
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

    // Parallel checker: exercises bug site #1 from #2777.
    // ExitRequested during init constraint check must map to LimitReached(Exit).
    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    let result = checker.check();
    match result {
        CheckResult::LimitReached { limit_type, .. } => {
            assert_eq!(limit_type, LimitType::Exit, "parallel: expected Exit limit");
        }
        other => panic!("parallel: expected LimitReached(Exit), got: {other:?}"),
    }
}
