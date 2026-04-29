// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Result precedence tests for finalize_check (#1850).
//! Error > Violation > Deadlock ordering.

use super::*;
use crate::ConfigCheckError;

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

/// Regression test for #1850: errors must take precedence over violations.
///
/// Before the fix, finalize_check had an early-exit guard
///   `if first_error.is_none() && first_violation.is_none() && first_deadlock.is_none()`
/// which prevented errors from being recorded after a violation arrived.
/// The return logic gives errors precedence (line 335), so errors must always
/// be retained regardless of other results.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_error_precedence_over_violation() {
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

    // Create channel with violation arriving before error
    let (tx, rx) = bounded::<WorkerResult>(10);
    let stats = WorkerStats::default();

    tx.send(WorkerResult::Violation {
        invariant: "TestInv".to_string(),
        state_fp: Fingerprint(42),
        stats: stats.clone(),
    })
    .expect("test channel send");

    tx.send(WorkerResult::Error(
        ConfigCheckError::MissingNext.into(),
        stats.clone(),
    ))
    .expect("test channel send");

    tx.send(WorkerResult::Done(stats))
        .expect("test channel send");
    drop(tx);

    let runtime = test_runtime(rx, 1);

    let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);

    // Error must take precedence over violation
    assert!(
        matches!(result, CheckResult::Error { .. }),
        "Expected CheckResult::Error (error precedence over violation), got: {:?}",
        result
    );
}

/// Regression test for #1850: errors must take precedence over deadlocks too.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_error_precedence_over_deadlock() {
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

    // Create channel with deadlock arriving before error
    let (tx, rx) = bounded::<WorkerResult>(10);
    let stats = WorkerStats::default();

    tx.send(WorkerResult::Deadlock {
        state_fp: Fingerprint(99),
        stats: stats.clone(),
    })
    .expect("test channel send");

    tx.send(WorkerResult::Error(
        ConfigCheckError::MissingNext.into(),
        stats.clone(),
    ))
    .expect("test channel send");

    tx.send(WorkerResult::Done(stats))
        .expect("test channel send");
    drop(tx);

    let runtime = test_runtime(rx, 1);

    let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);

    assert!(
        matches!(result, CheckResult::Error { .. }),
        "Expected CheckResult::Error (error precedence over deadlock), got: {:?}",
        result
    );
}

/// Test that a violation arriving before a deadlock causes the deadlock to be
/// dropped (finalize.rs line 120: `first_deadlock.is_none() && first_violation.is_none()`).
/// The deadlock should NOT appear in the final result.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_violation_drops_later_deadlock() {
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

    // Violation first, then deadlock
    tx.send(WorkerResult::Violation {
        invariant: "TestInv".to_string(),
        state_fp: Fingerprint(42),
        stats: stats.clone(),
    })
    .expect("test channel send");

    tx.send(WorkerResult::Deadlock {
        state_fp: Fingerprint(99),
        stats: stats.clone(),
    })
    .expect("test channel send");

    tx.send(WorkerResult::Done(stats))
        .expect("test channel send");
    drop(tx);

    let runtime = test_runtime(rx, 1);

    let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);

    // Violation takes precedence over deadlock
    match result {
        CheckResult::InvariantViolation { invariant, .. } => {
            assert_eq!(invariant, "TestInv", "violation invariant must match");
        }
        other => panic!("Expected InvariantViolation, got: {other:?}"),
    }
}

/// Test the continue_on_error path: when a violation is stored in the
/// first_violation OnceLock (as happens in continue_on_error mode) rather
/// than arriving on the channel, finalize_check must still return it.
/// This exercises finalize.rs lines 364-365.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_continue_on_error_violation_from_oncelock() {
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

    // Simulate continue_on_error: store violation in OnceLock, not channel
    let _ = checker
        .first_violation
        .set(("ContinueInv".to_string(), Fingerprint(77)));

    let (tx, rx) = bounded::<WorkerResult>(10);
    tx.send(WorkerResult::Done(WorkerStats::default()))
        .expect("test channel send");
    drop(tx);

    let runtime = test_runtime(rx, 1);

    let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);

    match result {
        CheckResult::InvariantViolation { invariant, .. } => {
            assert_eq!(
                invariant, "ContinueInv",
                "continue_on_error violation must be surfaced from OnceLock"
            );
        }
        other => panic!("Expected InvariantViolation from OnceLock, got: {other:?}"),
    }
}
