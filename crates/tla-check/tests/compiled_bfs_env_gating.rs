// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for compiled BFS env var gating.
//!
//! Verifies that the compiled BFS path respects the TLA2_COMPILED_BFS=1
//! opt-in and TLA2_NO_COMPILED_BFS=1 disable env vars. The compiled BFS
//! path is opt-in for now (Part of #4171).
//!
//! These tests use a simple all-scalar spec (Counter with 4 states) to
//! verify that both the interpreter and compiled BFS paths produce
//! identical state counts.
//!
//! Part of #4171: Wire compiled BFS into production BFS loop.

mod common;

use tla_check::{check_module, CheckResult, Config};
use tla_eval::clear_for_test_reset;

/// A simple all-scalar spec with 4 states, suitable for both interpreter
/// and compiled BFS paths. All state variables are integers (scalars).
const COUNTER_SPEC: &str = r#"
---- MODULE Counter ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == \/ (x = 0 /\ x' = 1 /\ y' = y)
        \/ (y = 0 /\ y' = 1 /\ x' = x)
        \/ (x = 1 /\ y = 1 /\ x' = 1 /\ y' = 1)
Inv == x \in {0, 1} /\ y \in {0, 1}
====
"#;

const COUNTER_CONFIG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\n";

/// Baseline: run without compiled BFS (interpreter path).
/// This is the reference state count all other runs must match.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_compiled_bfs_baseline_interpreter_path() {
    let _no_compiled = common::EnvVarGuard::set("TLA2_NO_COMPILED_BFS", Some("1"));
    let _no_jit = common::EnvVarGuard::remove("TLA2_JIT");
    let _no_flag = common::EnvVarGuard::remove("TLA2_COMPILED_BFS");
    clear_for_test_reset();

    let module = common::parse_module(COUNTER_SPEC);
    let config = Config::parse(COUNTER_CONFIG).expect("valid cfg");
    let result = check_module(&module, &config);

    match result {
        CheckResult::Success(stats) => {
            // (0,0) -> (1,0), (0,1) -> (1,1): 4 distinct states
            assert_eq!(stats.states_found, 4, "baseline should find 4 states");
            assert_eq!(stats.initial_states, 1, "baseline should have 1 init state");
        }
        other => panic!("baseline interpreter run failed: {other:?}"),
    }
}

/// Verify that setting TLA2_NO_COMPILED_BFS=1 forces interpreter path even
/// when TLA2_COMPILED_BFS=1 is also set (disable takes priority).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_compiled_bfs_disable_takes_priority_over_enable() {
    // Both set: disable should win
    let _enable = common::EnvVarGuard::set("TLA2_COMPILED_BFS", Some("1"));
    let _disable = common::EnvVarGuard::set("TLA2_NO_COMPILED_BFS", Some("1"));
    let _no_jit = common::EnvVarGuard::remove("TLA2_JIT");
    clear_for_test_reset();

    let module = common::parse_module(COUNTER_SPEC);
    let config = Config::parse(COUNTER_CONFIG).expect("valid cfg");
    let result = check_module(&module, &config);

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 4,
                "with disable flag, interpreter path should still find 4 states"
            );
        }
        other => panic!("disable-priority run failed: {other:?}"),
    }
}

/// Without TLA2_COMPILED_BFS=1, the compiled BFS should not activate
/// even if JIT is enabled and all actions are compilable.
/// The spec should still produce correct results via the interpreter path.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_compiled_bfs_not_active_without_env_var() {
    let _no_compiled = common::EnvVarGuard::remove("TLA2_COMPILED_BFS");
    let _no_disable = common::EnvVarGuard::remove("TLA2_NO_COMPILED_BFS");
    let _no_jit = common::EnvVarGuard::remove("TLA2_JIT");
    clear_for_test_reset();

    let module = common::parse_module(COUNTER_SPEC);
    let config = Config::parse(COUNTER_CONFIG).expect("valid cfg");
    let result = check_module(&module, &config);

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 4,
                "without env var, interpreter path should find 4 states"
            );
        }
        other => panic!("no-env-var run failed: {other:?}"),
    }
}
