// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::{CheckResult, Config};

// Bug #595: HandleState-mode parallel checker initial invariant violation with continue_on_error.
//
// Part of #3318: HandleState is now the default parallel mode. This test exercises the default
// path and must match TLC `-continue` parity.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_bug_595_handle_state_parallel_initial_violation_continue_on_error() {
    // HandleState is the default — no env var guard needed.

    let spec = r#"
---- MODULE InitialViolationContinueParallelHandleState ----
EXTENDS Naturals

VARIABLE x

\* Initial state violates invariant
Init == x = 5

Next == x' = x - 1 /\ x > 0

\* Invariant: x < 5 (violated by initial state)
SafeInvariant == x < 5

====
"#;

    let module = common::parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SafeInvariant".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ParallelChecker::new(&module, &config, 2);
    checker.set_continue_on_error(true);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match &result {
        CheckResult::InvariantViolation { stats, .. } => {
            assert_eq!(stats.states_found, 6);
        }
        other => panic!("Expected InvariantViolation, got: {other:?}"),
    }
}
