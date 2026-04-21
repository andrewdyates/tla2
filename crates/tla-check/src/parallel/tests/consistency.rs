// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sequential vs parallel consistency, error handling, and work distribution tests

use super::parse_module;
use super::*;
use crate::{CheckError, ConfigCheckError};
use std::ffi::OsString;
use std::sync::{Mutex, MutexGuard};

static FORCE_BATCH_ENV_LOCK: Mutex<()> = Mutex::new(());

struct ForceBatchEnvGuard {
    previous: Option<OsString>,
    lock: Option<MutexGuard<'static, ()>>,
}

impl ForceBatchEnvGuard {
    fn set(value: Option<&str>) -> Self {
        let lock = FORCE_BATCH_ENV_LOCK
            .lock()
            .expect("force-batch env lock must not be poisoned");
        let previous = std::env::var_os("TLA2_FORCE_BATCH");
        match value {
            Some(value) => std::env::set_var("TLA2_FORCE_BATCH", value),
            None => std::env::remove_var("TLA2_FORCE_BATCH"),
        }
        Self {
            previous,
            lock: Some(lock),
        }
    }
}

impl Drop for ForceBatchEnvGuard {
    fn drop(&mut self) {
        match self.previous.take() {
            Some(value) => std::env::set_var("TLA2_FORCE_BATCH", value),
            None => std::env::remove_var("TLA2_FORCE_BATCH"),
        }
        self.lock.take();
    }
}

fn run_parallel_with_force_batch(
    module: &Module,
    config: &Config,
    workers: usize,
    force_batch: bool,
    store_states: bool,
    max_states: Option<usize>,
) -> CheckResult {
    let _guard = ForceBatchEnvGuard::set(force_batch.then_some("1"));
    let mut checker = ParallelChecker::new(module, config, workers);
    checker.set_deadlock_check(false);
    checker.set_store_states(store_states);
    if let Some(limit) = max_states {
        checker.set_max_states(limit);
    }
    checker.check()
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_vs_sequential_consistency() {
    let _serial = super::acquire_interner_lock();
    // Verify that parallel and sequential checkers produce the same result
    let src = r#"
---- MODULE Consistency ----
VARIABLE x, y
Init == x \in {0, 1} /\ y \in {0, 1}
Next == x' \in {0, 1} /\ y' \in {0, 1}
Valid == x + y < 3
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Valid".to_string()],
        ..Default::default()
    };

    // Run sequential checker
    let mut seq_checker = crate::check::ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    let seq_result = seq_checker.check();

    // Run parallel checker
    let mut par_checker = ParallelChecker::new(&module, &config, 4);
    par_checker.set_deadlock_check(false);
    let par_result = par_checker.check();

    // Both should succeed with same state count and transition count
    // Part of #982: transition counts must match between sequential and parallel
    match (seq_result, par_result) {
        (CheckResult::Success(seq_stats), CheckResult::Success(par_stats)) => {
            assert_eq!(seq_stats.states_found, par_stats.states_found);
            assert_eq!(seq_stats.initial_states, par_stats.initial_states);
            assert_eq!(
                seq_stats.transitions, par_stats.transitions,
                "Transition count differs between sequential ({}) and parallel ({})",
                seq_stats.transitions, par_stats.transitions
            );
        }
        (seq, par) => panic!("Results differ: seq={:?}, par={:?}", seq, par),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_continue_on_error_states_found_parity_with_sequential() {
    let _serial = super::acquire_interner_lock();
    // Regression for #2068: violating states inserted into seen storage must
    // count toward states_found in both sequential and parallel checkers.
    let src = r#"
---- MODULE ContinueOnErrorParity ----
VARIABLE x
Init == x = 0
Next == x < 4 /\ x' = x + 1
Small == x < 2
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Small".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    for (mode_label, store_states) in [("full-trace", true), ("no-trace", false)] {
        let mut seq_checker = crate::check::ModelChecker::new(&module, &config);
        seq_checker.set_deadlock_check(false);
        seq_checker.set_continue_on_error(true);
        seq_checker.set_store_states(store_states);
        let seq_stats = match seq_checker.check() {
            CheckResult::InvariantViolation { stats, .. } => stats,
            other => panic!(
                "Expected sequential continue_on_error invariant violation in {} mode, got {:?}",
                mode_label, other
            ),
        };

        let mut par_checker_single = ParallelChecker::new(&module, &config, 1);
        par_checker_single.set_deadlock_check(false);
        par_checker_single.set_continue_on_error(true);
        par_checker_single.set_store_states(store_states);
        let par_single_stats = match par_checker_single.check() {
            CheckResult::InvariantViolation { stats, .. } => stats,
            other => panic!(
                "Expected parallel continue_on_error invariant violation (1 worker) in {} mode, got {:?}",
                mode_label, other
            ),
        };

        let mut par_checker_multi = ParallelChecker::new(&module, &config, 4);
        par_checker_multi.set_deadlock_check(false);
        par_checker_multi.set_continue_on_error(true);
        par_checker_multi.set_store_states(store_states);
        let par_multi_stats = match par_checker_multi.check() {
            CheckResult::InvariantViolation { stats, .. } => stats,
            other => panic!(
                "Expected parallel continue_on_error invariant violation (4 workers) in {} mode, got {:?}",
                mode_label, other
            ),
        };

        // Distinct states are x = 0..4 (5 total), including violating states x = 2..4.
        assert_eq!(seq_stats.states_found, 5, "mode={}", mode_label);
        assert_eq!(par_single_stats.states_found, 5, "mode={}", mode_label);
        assert_eq!(par_multi_stats.states_found, 5, "mode={}", mode_label);
        assert_eq!(
            seq_stats.states_found, par_single_stats.states_found,
            "mode={}",
            mode_label
        );
        assert_eq!(
            seq_stats.states_found, par_multi_stats.states_found,
            "mode={}",
            mode_label
        );
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_does_not_drop_work_items() {
    let _serial = super::acquire_interner_lock();
    // Regression test: parallel exploration must not silently miss states.
    //
    // This is a self-contained "Majority-like" spec with a known, moderate-sized
    // state space (2733 states). We compare sequential vs parallel results.
    let src = r#"
---- MODULE ParMajority ----
CONSTANTS A, B, C

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. 5 }

VARIABLES seq, i, cand, cnt

Init ==
    /\ seq \in BoundedSeq(Value)
    /\ i = 1
    /\ cand \in Value
    /\ cnt = 0

Next ==
    /\ i <= Len(seq)
    /\ i' = i + 1
    /\ seq' = seq
    /\ \/ /\ cnt = 0
          /\ cand' = seq[i]
          /\ cnt' = 1
       \/ /\ cnt # 0 /\ cand = seq[i]
          /\ cand' = cand
          /\ cnt' = cnt + 1
       \/ /\ cnt # 0 /\ cand # seq[i]
          /\ cand' = cand
          /\ cnt' = cnt - 1
====
"#;
    let module = parse_module(src);

    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        ..Default::default()
    };
    config.constants.insert(
        "A".to_string(),
        crate::config::ConstantValue::Value("A".to_string()),
    );
    config.constants.insert(
        "B".to_string(),
        crate::config::ConstantValue::Value("B".to_string()),
    );
    config.constants.insert(
        "C".to_string(),
        crate::config::ConstantValue::Value("C".to_string()),
    );

    // Run sequential checker
    let mut seq_checker = crate::check::ModelChecker::new(&module, &config);
    let seq_result = seq_checker.check();

    // Run parallel checker
    let par_checker = ParallelChecker::new(&module, &config, 8);
    let par_result = par_checker.check();

    match (seq_result, par_result) {
        (CheckResult::Success(seq_stats), CheckResult::Success(par_stats)) => {
            assert_eq!(seq_stats.initial_states, 1092);
            assert_eq!(seq_stats.states_found, 2733);
            assert_eq!(seq_stats.transitions, 2367);

            assert_eq!(par_stats.initial_states, 1092);
            assert_eq!(par_stats.states_found, 2733);
            assert_eq!(par_stats.transitions, 2367);
        }
        (seq, par) => panic!("Results differ: seq={:?}, par={:?}", seq, par),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_single_worker() {
    let _serial = super::acquire_interner_lock();
    // Test with single worker (should behave like sequential)
    let src = r#"
---- MODULE Single ----
VARIABLE x
Init == x = 0
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

    let mut checker = ParallelChecker::new(&module, &config, 1);
    checker.set_deadlock_check(false);

    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 4);
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_store_states_mode_matches_force_batch_when_preadmit_disabled() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE StoreStatesBoundary ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next ==
    \/ /\ x < 3
       /\ x' = x + 1
       /\ y' = y
    \/ /\ x < 3
       /\ x' = x + 1
       /\ y' = y
    \/ /\ y < 2
       /\ x' = x
       /\ y' = y + 1
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    let default_result = run_parallel_with_force_batch(&module, &config, 1, false, true, None);
    let forced_result = run_parallel_with_force_batch(&module, &config, 1, true, true, None);

    match (default_result, forced_result) {
        (CheckResult::Success(default_stats), CheckResult::Success(forced_stats)) => {
            assert_eq!(default_stats.states_found, 12);
            assert_eq!(default_stats.transitions, 26);
            assert_eq!(forced_stats.states_found, 12);
            assert_eq!(forced_stats.transitions, 26);
            assert_eq!(default_stats.states_found, forced_stats.states_found);
            assert_eq!(default_stats.transitions, forced_stats.transitions);
        }
        (default, forced) => panic!(
            "store-full-states boundary must match forced batch: default={default:?}, forced={forced:?}"
        ),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_max_states_limit_matches_force_batch_when_preadmit_disabled() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE StateLimitBoundary ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next ==
    \/ /\ x < 3
       /\ x' = x + 1
       /\ y' = y
    \/ /\ x < 3
       /\ x' = x + 1
       /\ y' = y
    \/ /\ y < 2
       /\ x' = x
       /\ y' = y + 1
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    let default_result = run_parallel_with_force_batch(&module, &config, 1, false, false, Some(5));
    let forced_result = run_parallel_with_force_batch(&module, &config, 1, true, false, Some(5));

    match (default_result, forced_result) {
        (
            CheckResult::LimitReached {
                limit_type: default_limit,
                stats: default_stats,
            },
            CheckResult::LimitReached {
                limit_type: forced_limit,
                stats: forced_stats,
            },
        ) => {
            assert_eq!(default_limit, crate::check::LimitType::States);
            assert_eq!(forced_limit, crate::check::LimitType::States);
            assert_eq!(default_stats.states_found, 5);
            assert_eq!(forced_stats.states_found, 5);
            assert_eq!(default_stats.states_found, forced_stats.states_found);
            assert!(
                default_stats.transitions > 0 && forced_stats.transitions > 0,
                "state-limit boundary should still explore at least one transition before stopping"
            );
        }
        (default, forced) => panic!(
            "max-states boundary must match forced batch: default={default:?}, forced={forced:?}"
        ),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_missing_init() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE Test ----
VARIABLE x
Next == x' = x + 1
====
"#;
    let module = parse_module(src);

    let config = Config {
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    let result = checker.check();

    assert!(matches!(
        result,
        CheckResult::Error {
            error: CheckError::Config(ConfigCheckError::MissingInit),
            ..
        }
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_missing_next() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        ..Default::default()
    };

    let checker = ParallelChecker::new(&module, &config, 2);
    let result = checker.check();

    assert!(matches!(
        result,
        CheckResult::Error {
            error: CheckError::Config(ConfigCheckError::MissingNext),
            ..
        }
    ));
}
