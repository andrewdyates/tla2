// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for #2751: memory-limit-triggered `LimitReached(Memory)`.
//!
//! Sets a 1-byte memory limit so that the process RSS always exceeds the
//! critical threshold (95%). The sequential checker checks memory at each
//! progress interval (default: every 1000 states), so the unbounded counter
//! spec will explore ~1000 states before the first progress-interval check
//! detects critical pressure and returns `LimitReached(Memory)`.

mod common;

use tla_check::{CheckResult, LimitType};
use tla_check::{Config, ModelChecker};

/// Sequential full-trace mode: a 1-byte memory limit triggers
/// `LimitReached(Memory)` after the first progress-interval check.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_sequential_memory_limit_triggers_limit_reached() {
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
    let module = common::parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    // 1 byte: any process exceeds this — triggers Critical on first progress check.
    checker.set_memory_limit(1);

    let result = checker.check();

    match result {
        CheckResult::LimitReached { limit_type, stats } => {
            assert_eq!(limit_type, LimitType::Memory, "expected Memory limit type");
            // The progress interval is 1000 by default, so ~1000 states
            // are explored before the first memory check fires.
            assert!(
                stats.states_found > 0,
                "should have explored at least 1 state before memory stop"
            );
        }
        other => panic!("expected LimitReached(Memory), got: {other:?}"),
    }
}

/// Sequential notrace mode: same memory limit test using fingerprint-only BFS.
///
/// Exercises the `run_bfs_notrace.rs` code path with memory monitoring
/// to ensure both sequential BFS modes handle memory pressure correctly.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_sequential_notrace_memory_limit_triggers_limit_reached() {
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
    let module = common::parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_store_states(false); // notrace mode → run_bfs_notrace.rs
    checker.set_deadlock_check(false);
    checker.set_memory_limit(1);

    let result = checker.check();

    match result {
        CheckResult::LimitReached { limit_type, stats } => {
            assert_eq!(
                limit_type,
                LimitType::Memory,
                "notrace: expected Memory limit type"
            );
            assert!(
                stats.states_found > 0,
                "notrace: should have explored at least 1 state before memory stop"
            );
        }
        other => panic!("notrace: expected LimitReached(Memory), got: {other:?}"),
    }
}
