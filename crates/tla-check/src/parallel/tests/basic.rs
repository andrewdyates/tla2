// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Basic parallel checker functionality tests

use super::parse_module;
use super::*;
use crate::Value;
use std::ffi::OsString;
use std::sync::{Mutex, MutexGuard};

static PARALLEL_PROFILING_ENV_LOCK: Mutex<()> = Mutex::new(());

struct ParallelProfilingEnvGuard {
    previous: Option<OsString>,
    lock: Option<MutexGuard<'static, ()>>,
}

impl ParallelProfilingEnvGuard {
    fn set(value: &str) -> Self {
        let lock = PARALLEL_PROFILING_ENV_LOCK
            .lock()
            .expect("parallel profiling env lock must not be poisoned");
        let previous = std::env::var_os(super::super::PARALLEL_PROFILING_ENV);
        std::env::set_var(super::super::PARALLEL_PROFILING_ENV, value);
        Self {
            previous,
            lock: Some(lock),
        }
    }
}

impl Drop for ParallelProfilingEnvGuard {
    fn drop(&mut self) {
        match self.previous.take() {
            Some(value) => std::env::set_var(super::super::PARALLEL_PROFILING_ENV, value),
            None => std::env::remove_var(super::super::PARALLEL_PROFILING_ENV),
        }
        self.lock.take();
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_profiling_flag_reads_release_env_value() {
    let _guard = ParallelProfilingEnvGuard::set("1");

    let enabled_cache = std::sync::OnceLock::new();
    assert!(
        super::super::parallel_profiling_from_env(&enabled_cache),
        "release profiling must honor TLA2_PARALLEL_PROFILING=1"
    );

    std::env::set_var(super::super::PARALLEL_PROFILING_ENV, "0");
    let disabled_cache = std::sync::OnceLock::new();
    assert!(
        !super::super::parallel_profiling_from_env(&disabled_cache),
        "profiling must stay off for non-opt-in values"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_handle_state_override_restores_previous_mode() {
    let base = super::super::use_handle_state();
    {
        let _override = super::super::set_use_handle_state_override(!base);
        assert_eq!(
            super::super::use_handle_state(),
            !base,
            "override must bypass the cached env-backed default"
        );
    }
    assert_eq!(
        super::super::use_handle_state(),
        base,
        "dropping the guard must restore the prior mode"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_simple_counter() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
InRange == x >= 0 /\ x <= 2
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InRange".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3);
            assert_eq!(stats.initial_states, 1);
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_no_trace_mode_success() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
InRange == x >= 0 /\ x <= 2
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InRange".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    checker.set_store_states(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3);
            assert_eq!(stats.initial_states, 1);
        }
        other => panic!("Expected success, got: {:?}", other),
    }

    // Verify internal state: seen_fps should be populated, seen should be empty
    assert!(!checker.store_full_states);
    assert!(
        checker.seen.is_empty(),
        "seen map should be empty in no-trace mode"
    );
    assert_eq!(checker.seen_fps.len(), 3, "seen_fps should have 3 entries");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_invariant_violation() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
SmallValue == x < 3
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SmallValue".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    // Part of #3233: store_full_states defaults to false; enable for trace reconstruction.
    checker.set_store_states(true);

    let result = checker.check();

    match result {
        CheckResult::InvariantViolation {
            invariant,
            trace,
            stats,
        } => {
            assert_eq!(invariant, "SmallValue");
            assert_eq!(trace.len(), 4); // x=0, x=1, x=2, x=3
            assert!(stats.states_found >= 3);
        }
        other => panic!("Expected invariant violation, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_no_trace_mode_violation_empty_trace() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
SmallValue == x < 3
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["SmallValue".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    checker.set_store_states(false);

    let result = checker.check();

    match result {
        CheckResult::InvariantViolation {
            invariant,
            trace,
            stats,
        } => {
            assert_eq!(invariant, "SmallValue");
            assert!(trace.is_empty(), "Trace should be empty in no-trace mode");
            assert_eq!(stats.states_found, 4);
        }
        other => panic!("Expected invariant violation, got: {:?}", other),
    }

    assert!(!checker.store_full_states);
    assert!(
        checker.seen.is_empty(),
        "seen map should be empty in no-trace mode"
    );
    assert_eq!(checker.seen_fps.len(), 4, "seen_fps should have 4 entries");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_multiple_initial_states() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE Multi ----
VARIABLE x
Init == x \in {0, 1}
Next == x < 3 /\ x' = x + 1
InRange == x >= 0 /\ x <= 3
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InRange".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.initial_states, 2);
            assert_eq!(stats.states_found, 4); // x=0,1,2,3
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_two_variables() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE TwoVars ----
VARIABLE x, y
Init == x = 0 /\ y = 5
Next == x' = x + 1 /\ UNCHANGED y
Bounded == x < 2
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Bounded".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    // Part of #3233: store_full_states defaults to false; enable for trace reconstruction.
    checker.set_store_states(true);

    let result = checker.check();

    match result {
        CheckResult::InvariantViolation {
            invariant,
            trace,
            stats: _,
        } => {
            assert_eq!(invariant, "Bounded");
            assert!(trace.len() >= 3);

            // Verify y stayed unchanged
            for state in &trace.states {
                let y_val = state.vars().find(|(n, _)| n.as_ref() == "y");
                assert!(y_val.is_some());
                assert_eq!(y_val.unwrap().1, &Value::int(5));
            }
        }
        other => panic!("Expected invariant violation, got: {:?}", other),
    }
}

/// Part of #3233: Safety-only fp-only parallel run leaves `depths` map empty.
/// When neither checkpointing nor fp-only liveness is active, the `track_depths`
/// gate suppresses both init-state and successor depth writes, so the DashMap
/// stays empty. This is the core assertion for the depth-gate correctness.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_safety_only_depths_empty() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x < 5 /\ x' = x + 1
TypeOK == x \in 0..5
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    checker.set_store_states(false);
    // No checkpoint, no liveness properties → track_depths = false.

    let result = checker.check();
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 6, "Counter should explore 6 states");
        }
        other => panic!("Expected Success, got: {other:?}"),
    }

    assert!(
        checker.depths.is_empty(),
        "depths map must be empty for safety-only fp-only run without checkpoint, got {} entries",
        checker.depths.len()
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_action_constraint_tlcget_level_uses_current_state_level() {
    let _serial = super::acquire_interner_lock();
    // Regression for #1102: ACTION_CONSTRAINT must see curState level, not successor level.
    let src = r#"
---- MODULE ParallelActionConstraintLevel ----
EXTENDS TLC, Naturals
VARIABLE depth
Init == depth = 1
Next == depth < 3 /\ depth' = depth + 1
LevelMatchesCurrent == TLCGet("level") = depth
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        action_constraints: vec!["LevelMatchesCurrent".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);

    let result = checker.check();
    match result {
        CheckResult::Success(stats) => {
            // Expected path: depth 1 -> 2 -> 3 (3 states total).
            assert_eq!(stats.states_found, 3);
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}
