// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for POSTCONDITION evaluation and guard error suppression in finalize_check.

use super::*;
use crate::{ConfigCheckError, EvalCheckError, RuntimeCheckError};

fn test_runtime(
    result_rx: crossbeam_channel::Receiver<WorkerResult>,
    num_initial: usize,
) -> CheckRuntime {
    CheckRuntime {
        result_rx,
        handles: vec![],
        num_initial,
        start_time: std::time::Instant::now(),
        jit_compiled_invariants: 0,
    }
}

/// Regression test for #1875: ExitRequested errors must be converted to
/// LimitReached(Exit) in the parallel path, matching the sequential checker's
/// check_error_to_result() behavior.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_exit_requested_becomes_limit_reached() {
    let src = r#"
---- MODULE Minimal ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
    let module = parse_module(src);
    let config = crate::config::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let checker = crate::parallel::ParallelChecker::new(&module, &config, 1);
    let mut ctx = EvalCtx::new();

    let (tx, rx) = bounded::<WorkerResult>(10);
    let stats = WorkerStats::default();

    // Send ExitRequested wrapped as a WorkerResult::Error
    tx.send(WorkerResult::Error(
        EvalCheckError::Eval(tla_value::error::EvalError::ExitRequested { span: None }).into(),
        stats.clone(),
    ))
    .expect("test channel send");

    tx.send(WorkerResult::Done(stats))
        .expect("test channel send");
    drop(tx);

    let runtime = test_runtime(rx, 1);

    let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);

    // ExitRequested should become LimitReached(Exit), not Error
    assert!(
        matches!(
            result,
            CheckResult::LimitReached {
                limit_type: LimitType::Exit,
                ..
            }
        ),
        "Expected CheckResult::LimitReached(Exit), got: {:?}",
        result
    );
}

/// Regression test for #2056: parallel finalize must surface depth overflow
/// as a SetupError when converting max_depth to TLC diameter for POSTCONDITION.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_postcondition_depth_overflow_returns_setup_error() {
    let src = r#"
---- MODULE Minimal ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Post == TRUE
====
"#;
    let module = parse_module(src);
    let config = crate::config::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        postcondition: Some("Post".to_string()),
        ..Default::default()
    };

    let checker = crate::parallel::ParallelChecker::new(&module, &config, 1);
    let mut ctx = EvalCtx::new();

    // Simulate pathological depth so `depth_to_tlc_level` must fail instead of truncating.
    checker.max_depth.store(usize::MAX, Ordering::SeqCst);

    let (tx, rx) = bounded::<WorkerResult>(10);
    tx.send(WorkerResult::Done(WorkerStats::default()))
        .expect("test channel send");
    drop(tx);

    let runtime = test_runtime(rx, 1);

    let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);

    match result {
        CheckResult::Error {
            error: CheckError::Config(ConfigCheckError::Setup(msg)),
            ..
        } => {
            assert!(
                msg.contains("exceeds TLC level range"),
                "expected depth-overflow message, got: {msg}"
            );
        }
        other => panic!("expected SetupError from overflow conversion, got: {other:?}"),
    }
}

/// Regression test for #2187: parallel finalize must carry suppressed guard
/// error count into CheckStats instead of hardcoding 0.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_carries_suppressed_guard_errors() {
    crate::guard_error_stats::with_test_lock(|| {
        let src = r#"
---- MODULE Minimal ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
        let module = parse_module(src);
        let config = crate::config::Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        };

        let checker = crate::parallel::ParallelChecker::new(&module, &config, 1);
        let mut ctx = EvalCtx::new();

        // Simulate guard suppression that occurred during parallel BFS.
        // In production, workers call record_suppressed_action_level_error()
        // during successor enumeration. Here we directly inject the count.
        crate::guard_error_stats::reset();
        crate::guard_error_stats::record_suppressed_action_level_error();
        crate::guard_error_stats::record_suppressed_action_level_error();
        crate::guard_error_stats::record_suppressed_action_level_error();

        let (tx, rx) = bounded::<WorkerResult>(10);
        tx.send(WorkerResult::Done(WorkerStats::default()))
            .expect("test channel send");
        drop(tx);

        let runtime = test_runtime(rx, 1);

        let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);

        let stats = match result {
            CheckResult::Success(stats) => stats,
            other => panic!("Expected CheckResult::Success, got: {other:?}"),
        };

        assert_eq!(
            stats.suppressed_guard_errors, 3,
            "finalize_check must carry suppressed guard errors into CheckStats, not hardcode 0"
        );
    });
}

/// Test that WorkerResult::LimitReached with LimitType::States produces
/// CheckResult::LimitReached(States) when no higher-precedence result exists.
/// This path (finalize.rs lines 384-389) had no dedicated test.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_limit_reached_states() {
    let src = r#"
---- MODULE Minimal ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
    let module = parse_module(src);
    let config = crate::config::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let checker = crate::parallel::ParallelChecker::new(&module, &config, 1);
    let mut ctx = EvalCtx::new();

    let (tx, rx) = bounded::<WorkerResult>(10);
    let stats = WorkerStats::default();

    tx.send(WorkerResult::LimitReached {
        limit_type: LimitType::States,
        stats: stats.clone(),
    })
    .expect("test channel send");

    tx.send(WorkerResult::Done(stats))
        .expect("test channel send");
    drop(tx);

    let runtime = test_runtime(rx, 1);

    let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);

    assert!(
        matches!(
            result,
            CheckResult::LimitReached {
                limit_type: LimitType::States,
                ..
            }
        ),
        "Expected CheckResult::LimitReached(States), got: {:?}",
        result
    );
}

/// Test that POSTCONDITION evaluating to FALSE returns PostconditionFalse error
/// in the parallel path (finalize.rs lines 411-417). The existing test only
/// covers the depth-overflow path; this tests the normal false-evaluation path.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_postcondition_false_returns_postcondition_error() {
    let src = r#"
---- MODULE PostFalse ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Post == FALSE
====
"#;
    let module = parse_module(src);
    let config = crate::config::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        postcondition: Some("Post".to_string()),
        ..Default::default()
    };

    let checker = crate::parallel::ParallelChecker::new(&module, &config, 1);
    let mut ctx = EvalCtx::new();

    // Bind constants and set up context so postcondition can be evaluated
    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            ctx.define_op(def.name.node.clone(), def.clone());
        }
    }

    let (tx, rx) = bounded::<WorkerResult>(10);
    tx.send(WorkerResult::Done(WorkerStats::default()))
        .expect("test channel send");
    drop(tx);

    let runtime = test_runtime(rx, 1);

    let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);

    match result {
        CheckResult::Error {
            error: CheckError::Runtime(RuntimeCheckError::PostconditionFalse { operator }),
            ..
        } => {
            assert_eq!(
                operator, "Post",
                "PostconditionFalse must name the failing operator"
            );
        }
        other => panic!("Expected PostconditionFalse error, got: {other:?}"),
    }
}
