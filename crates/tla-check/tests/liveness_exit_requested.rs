// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #2815: ExitRequested during liveness checking must
//! produce `LimitReached(Exit)`, not `Error`.
//!
//! Before Phase B of #2815, `TLCSet("exit", TRUE)` inside a temporal property
//! would be stringified through `LivenessResult::RuntimeFailure { reason: String }`,
//! losing the typed `EvalError::ExitRequested`. The fix adds `LivenessResult::EvalFailure`
//! to preserve the typed error, which is then routed through `check_error_to_result`
//! to produce `LimitReached(Exit)`.
//!
//! This is the liveness counterpart to `sequential_exit_requested_init.rs` (#2789)
//! and `parallel_exit_requested_init.rs` (#2777).

use tla_check::Config;
use tla_check::ParallelChecker;
use tla_check::{CheckResult, LimitType};

mod common;

// ---------------------------------------------------------------------------
// Sequential liveness: ExitRequested in temporal property
// ---------------------------------------------------------------------------

/// Regression test for #2815: `TLCSet("exit", TRUE)` inside a liveness property.
///
/// The spec has a simple 3-state cycle (x ∈ {0, 1, 2}). The property
/// `<>(TLCSet("exit", TRUE))` is evaluated during liveness check mask
/// population — when the liveness checker evaluates the sub-formula on each
/// state, `TLCSet("exit", TRUE)` raises `ExitRequested`.
///
/// Before the fix: ExitRequested was stringified to RuntimeFailure, then to
/// CheckResult::Error (LivenessRuntimeFailure).
///
/// After the fix: ExitRequested propagates through LivenessResult::EvalFailure,
/// is caught by the match arm in liveness.rs, and routed through
/// `check_error_to_result` to produce `LimitReached(Exit)`.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_liveness_exit_requested_in_property_is_limit_reached() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let src = r#"
---- MODULE LivenessExitProperty ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
ExitProp == <>(TLCSet("exit", TRUE))
====
"#;
    let module = common::parse_module_strict(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["ExitProp".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true); // Required for liveness checking
    let result = checker.check();

    match result {
        CheckResult::LimitReached { limit_type, .. } => {
            assert_eq!(
                limit_type,
                LimitType::Exit,
                "expected Exit limit type from TLCSet(\"exit\", TRUE) in liveness property"
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "#2815 regression: ExitRequested in liveness property produced Error \
                 instead of LimitReached(Exit). Error: {error:?}"
            );
        }
        other => panic!(
            "expected LimitReached(Exit) from TLCSet(\"exit\", TRUE) in liveness property, \
             got: {other:?}"
        ),
    }
}

/// Variant: `[]<>(TLCSet("exit", TRUE))` temporal property.
///
/// Uses `[]<>` form (always eventually) instead of `<>` (eventually).
/// The liveness checker decomposes this into check masks and evaluates
/// `TLCSet("exit", TRUE)` on each state during population, triggering
/// ExitRequested through a different temporal decomposition path.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_liveness_exit_requested_in_box_diamond_property_is_limit_reached() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let src = r#"
---- MODULE LivenessExitBoxDiamond ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
\* []<> form: TLCSet triggers during check mask population
ExitProp == []<>(TLCSet("exit", TRUE))
====
"#;
    let module = common::parse_module_strict(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["ExitProp".to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::LimitReached { limit_type, .. } => {
            assert_eq!(
                limit_type,
                LimitType::Exit,
                "expected Exit limit type from TLCSet(\"exit\", TRUE) in []<> property"
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "#2815 regression: ExitRequested in []<> property produced Error \
                 instead of LimitReached(Exit). Error: {error:?}"
            );
        }
        other => panic!(
            "expected LimitReached(Exit) from TLCSet(\"exit\", TRUE) in []<> property, \
             got: {other:?}"
        ),
    }
}

// ---------------------------------------------------------------------------
// Parallel liveness: ExitRequested in temporal property
// ---------------------------------------------------------------------------

/// Parallel counterpart to `test_liveness_exit_requested_in_property_is_limit_reached`.
///
/// Exercises the `EvalFailure` handling in `parallel/checker/liveness.rs:437-438`,
/// ensuring the parallel liveness checker also routes ExitRequested through
/// `check_error_to_result` to produce `LimitReached(Exit)`.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_parallel_liveness_exit_requested_in_property_is_limit_reached() {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let src = r#"
---- MODULE ParallelLivenessExitProperty ----
EXTENDS Integers, TLC
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
ExitProp == <>(TLCSet("exit", TRUE))
====
"#;
    let module = common::parse_module_strict(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["ExitProp".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    let result = checker.check();

    match result {
        CheckResult::LimitReached { limit_type, .. } => {
            assert_eq!(
                limit_type,
                LimitType::Exit,
                "parallel: expected Exit limit type from TLCSet(\"exit\", TRUE) in liveness property"
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "#2815 regression (parallel): ExitRequested in liveness property produced Error \
                 instead of LimitReached(Exit). Error: {error:?}"
            );
        }
        other => panic!(
            "parallel: expected LimitReached(Exit) from TLCSet(\"exit\", TRUE) in liveness property, \
             got: {other:?}"
        ),
    }
}
