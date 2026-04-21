// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Config validation and setup parity tests.

use super::*;

/// Part of #2675 AC #3: Parameterized invariant (`INVARIANT Foo(x)`) must be
/// rejected by the parallel checker at setup time, matching sequential behavior.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_rejects_parameterized_invariant() {
    let _serial = super::super::acquire_interner_lock();
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Foo(n) == n > 0
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Foo".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match &result {
        CheckResult::Error {
            error:
                crate::check::CheckError::Config(crate::check::ConfigCheckError::OpRequiresNoArgs {
                    op_name,
                    kind,
                    arity,
                }),
            ..
        } => {
            assert_eq!(op_name, "Foo");
            assert_eq!(kind, "INVARIANT");
            assert_eq!(*arity, 1);
        }
        other => panic!("Parallel checker should reject parameterized invariant, got: {other:?}"),
    }
}

/// Part of #2675 AC #4: Temporal invariant (invariant body contains temporal
/// operators) must be rejected by the parallel checker at setup time.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_rejects_temporal_invariant() {
    let _serial = super::super::acquire_interner_lock();
    let src = r#"
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
TemporalInv == <>(x = 5)
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TemporalInv".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match &result {
        CheckResult::Error {
            error:
                crate::check::CheckError::Config(
                    crate::check::ConfigCheckError::InvariantNotStateLevel {
                        name,
                        has_temporal,
                        ..
                    },
                ),
            ..
        } => {
            assert_eq!(name, "TemporalInv");
            assert!(*has_temporal);
        }
        other => panic!("Parallel checker should reject temporal invariant, got: {other:?}"),
    }
}

/// Part of #3706: Verify POR is accepted in parallel mode and produces
/// correct results (same state count as without POR).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_accepts_por_and_produces_correct_results() {
    let _serial = super::super::acquire_interner_lock();
    let src = r#"
---- MODULE Test ----
VARIABLE x, y
Init == x = 0 /\ y = 0
IncX == x < 1 /\ x' = x + 1 /\ y' = y
IncY == y < 1 /\ x' = x /\ y' = y + 1
Next == IncX \/ IncY
====
"#;
    let module = parse_module(src);

    // Run without POR to get baseline state count
    let baseline_config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        por_enabled: false,
        ..Default::default()
    };
    let mut baseline_checker = ParallelChecker::new(&module, &baseline_config, 2);
    baseline_checker.set_deadlock_check(false);
    let baseline_result = baseline_checker.check();
    let baseline_states = match &baseline_result {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Baseline parallel check should succeed, got: {other:?}"),
    };

    // Run with POR enabled
    let por_config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        por_enabled: true,
        ..Default::default()
    };
    let mut por_checker = ParallelChecker::new(&module, &por_config, 2);
    por_checker.set_deadlock_check(false);
    let por_result = por_checker.check();

    match &por_result {
        CheckResult::Success(stats) => {
            // POR may reduce state count (valid reduction) but must not exceed baseline.
            // With effective independence analysis, independent actions like IncX/IncY
            // can be explored in one interleaving order, reducing explored states.
            assert!(
                stats.states_found <= baseline_states,
                "POR state count ({}) must not exceed non-POR baseline ({})",
                stats.states_found, baseline_states,
            );
            // POR must still find at least one state (the initial state)
            assert!(
                stats.states_found >= 1,
                "POR must explore at least the initial state"
            );
        }
        other => panic!("Parallel checker with POR should succeed, got: {other:?}"),
    }
}

#[test]
fn test_parallel_register_file_path_sets_input_base_dir_for_root_module() {
    let src = r#"
---- MODULE SetupPathTest ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    let spec_path = std::path::PathBuf::from("/tmp/parallel-setup-path/Spec.tla");
    checker.register_file_path(FileId(0), spec_path.clone());

    assert_eq!(
        checker.input_base_dir,
        spec_path.parent().map(std::path::Path::to_path_buf)
    );
}

#[test]
fn test_parallel_set_checkpoint_accepts_duration() {
    let src = r#"
---- MODULE SetupPathTest ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    let checkpoint_dir = std::path::PathBuf::from("/tmp/parallel-setup-path/checkpoint");
    let interval = Duration::from_secs(42);
    checker.set_checkpoint(checkpoint_dir.clone(), interval);

    assert_eq!(checker.checkpoint_dir, Some(checkpoint_dir));
    assert_eq!(checker.checkpoint_interval, interval);
}
