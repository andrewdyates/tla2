// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Finalize error precedence, panic dominance, and one-shot guard tests.

use super::super::*;
use crate::storage::{FingerprintSet, LookupOutcome};
use crate::test_support::parse_module;
use crate::{EvalCheckError, InfraCheckError};
use crossbeam_channel::bounded;
use std::collections::HashSet;
use std::sync::{atomic::Ordering, Arc, Mutex};

fn checker_for_finalize_tests() -> ParallelChecker {
    let src = r#"
---- MODULE FinalizeJoinPanic ----
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
    ParallelChecker::new(&module, &config, 2)
}

fn test_runtime(
    result_rx: crossbeam_channel::Receiver<WorkerResult>,
    handles: Vec<thread::JoinHandle<()>>,
    num_initial: usize,
) -> CheckRuntime {
    CheckRuntime {
        result_rx,
        handles,
        num_initial,
        start_time: std::time::Instant::now(),
        jit_compiled_invariants: 0,
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_check_worker_join_panic_returns_error() {
    let checker = checker_for_finalize_tests();

    let (tx, result_rx) = bounded::<WorkerResult>(1);
    drop(tx);

    let handles = vec![thread::spawn(|| panic!("synthetic worker panic"))];
    let runtime = test_runtime(result_rx, handles, 1);

    let mut ctx = EvalCtx::new();
    let result = checker.finalize_check(
        runtime,
        Vec::new(),
        Vec::new(),
        &mut ctx,
        Vec::new(),
        Vec::new(),
    );

    match result {
        CheckResult::Error {
            error: CheckError::Infra(InfraCheckError::WorkerThreadPanicked { worker_id, message }),
            ..
        } => {
            assert_eq!(worker_id, 0);
            assert!(message.contains("synthetic worker panic"));
        }
        other => panic!("Expected WorkerThreadPanicked error, got {:?}", other),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_check_progress_join_panic_returns_error() {
    let mut checker = checker_for_finalize_tests();
    checker.progress_interval_ms = 1;
    checker.set_progress_callback(Box::new(|_| panic!("synthetic progress panic")));

    let (tx, result_rx) = bounded::<WorkerResult>(1);
    drop(tx);

    // Keep finalize_check in worker-join long enough for the progress thread
    // to wake up and execute the panic-ing callback.
    let handles = vec![thread::spawn(|| {
        thread::sleep(Duration::from_millis(20));
    })];
    let runtime = test_runtime(result_rx, handles, 1);

    let mut ctx = EvalCtx::new();
    let result = checker.finalize_check(
        runtime,
        Vec::new(),
        Vec::new(),
        &mut ctx,
        Vec::new(),
        Vec::new(),
    );

    match result {
        CheckResult::Error {
            error: CheckError::Infra(InfraCheckError::ProgressThreadPanicked { message }),
            ..
        } => {
            assert!(message.contains("synthetic progress panic"));
        }
        other => panic!("Expected ProgressThreadPanicked error, got {:?}", other),
    }
}

// ============= Fingerprint storage error precedence tests =============
//
// Part of #1800: Verify that fingerprint-storage errors take absolute
// precedence over all other outcomes in the parallel finalize_check path,
// matching the serial path's finalize_terminal_result pattern (#1785).

/// A FingerprintSet that works correctly but always reports errors.
/// Mirrors the serial path's ErrorInjectingFingerprintSet in invariants.rs.
struct ErrorInjectingFingerprintSet {
    seen: Mutex<HashSet<Fingerprint>>,
    dropped: usize,
}

impl ErrorInjectingFingerprintSet {
    fn new(dropped: usize) -> Self {
        Self {
            seen: Mutex::new(HashSet::new()),
            dropped,
        }
    }
}

impl tla_mc_core::FingerprintSet<Fingerprint> for ErrorInjectingFingerprintSet {
    fn insert_checked(&self, fp: Fingerprint) -> InsertOutcome {
        if self.seen.lock().expect("lock poisoned").insert(fp) {
            InsertOutcome::Inserted
        } else {
            InsertOutcome::AlreadyPresent
        }
    }

    fn contains_checked(&self, fp: Fingerprint) -> LookupOutcome {
        if self.seen.lock().expect("lock poisoned").contains(&fp) {
            LookupOutcome::Present
        } else {
            LookupOutcome::Absent
        }
    }

    fn len(&self) -> usize {
        self.seen.lock().expect("lock poisoned").len()
    }

    fn has_errors(&self) -> bool {
        true
    }

    fn dropped_count(&self) -> usize {
        self.dropped
    }
}

impl FingerprintSet for ErrorInjectingFingerprintSet {}

fn checker_with_storage_errors(dropped: usize) -> ParallelChecker {
    let mut checker = checker_for_finalize_tests();
    let storage = Arc::new(ErrorInjectingFingerprintSet::new(dropped)) as Arc<dyn FingerprintSet>;
    checker.set_fingerprint_storage(storage);
    checker
}

fn assert_fingerprint_overflow(result: &CheckResult, expected_dropped: usize) {
    match result {
        CheckResult::Error {
            error: CheckError::Infra(InfraCheckError::FingerprintOverflow { dropped, .. }),
            ..
        } => {
            assert_eq!(
                *dropped, expected_dropped,
                "storage error should preserve injected dropped count"
            );
        }
        other => {
            panic!(
                "expected FingerprintStorageOverflow with dropped={expected_dropped}, got {other:?}"
            );
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_storage_error_precedence_over_violation() {
    let checker = checker_with_storage_errors(42);

    let (tx, result_rx) = bounded::<WorkerResult>(4);
    tx.send(WorkerResult::Violation {
        invariant: "SomeInv".to_string(),
        state_fp: Fingerprint(999),
        stats: WorkerStats::default(),
    })
    .unwrap();
    drop(tx);

    let handles: Vec<thread::JoinHandle<()>> = vec![];
    let runtime = test_runtime(result_rx, handles, 1);

    let mut ctx = EvalCtx::new();
    let result = checker.finalize_check(
        runtime,
        Vec::new(),
        Vec::new(),
        &mut ctx,
        Vec::new(),
        Vec::new(),
    );
    assert_fingerprint_overflow(&result, 42);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_storage_error_precedence_over_deadlock() {
    let checker = checker_with_storage_errors(7);

    let (tx, result_rx) = bounded::<WorkerResult>(4);
    tx.send(WorkerResult::Deadlock {
        state_fp: Fingerprint(123),
        stats: WorkerStats::default(),
    })
    .unwrap();
    drop(tx);

    let handles: Vec<thread::JoinHandle<()>> = vec![];
    let runtime = test_runtime(result_rx, handles, 1);

    let mut ctx = EvalCtx::new();
    let result = checker.finalize_check(
        runtime,
        Vec::new(),
        Vec::new(),
        &mut ctx,
        Vec::new(),
        Vec::new(),
    );
    assert_fingerprint_overflow(&result, 7);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_storage_error_precedence_over_limit() {
    let checker = checker_with_storage_errors(3);

    let (tx, result_rx) = bounded::<WorkerResult>(4);
    tx.send(WorkerResult::LimitReached {
        limit_type: LimitType::States,
        stats: WorkerStats::default(),
    })
    .unwrap();
    drop(tx);

    let handles: Vec<thread::JoinHandle<()>> = vec![];
    let runtime = test_runtime(result_rx, handles, 1);

    let mut ctx = EvalCtx::new();
    let result = checker.finalize_check(
        runtime,
        Vec::new(),
        Vec::new(),
        &mut ctx,
        Vec::new(),
        Vec::new(),
    );
    assert_fingerprint_overflow(&result, 3);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_storage_error_precedence_over_worker_error() {
    let checker = checker_with_storage_errors(15);

    let (tx, result_rx) = bounded::<WorkerResult>(4);
    tx.send(WorkerResult::Error(
        EvalCheckError::Eval(crate::EvalError::DivisionByZero { span: None }).into(),
        WorkerStats::default(),
    ))
    .unwrap();
    drop(tx);

    let handles: Vec<thread::JoinHandle<()>> = vec![];
    let runtime = test_runtime(result_rx, handles, 1);

    let mut ctx = EvalCtx::new();
    let result = checker.finalize_check(
        runtime,
        Vec::new(),
        Vec::new(),
        &mut ctx,
        Vec::new(),
        Vec::new(),
    );
    assert_fingerprint_overflow(&result, 15);
}

// ============= One-shot guard regression test (Part of #1433 Step 6) =============
//
// Validates that ParallelChecker::check() panics on second invocation,
// preventing stale run-state reuse (#1851).

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[should_panic(expected = "called more than once")]
fn test_one_shot_guard_panics_on_second_check() {
    let checker = checker_for_finalize_tests();
    // First call: panics internally because there are no real workers,
    // but the has_run flag is set before anything else. We need to catch
    // the first call's panic (if any) and then verify the second call
    // panics with the one-shot message.
    //
    // However, check() sets has_run first (line 437), then proceeds.
    // A simpler approach: just set has_run directly and call check().
    checker.has_run.store(true, Ordering::SeqCst);
    // This call should see has_run==true and panic immediately.
    let _result = checker.check();
}

// ============= Join-panic Error dominates channel Violation (Part of #1433 Step 6) =============
//
// Validates that when a worker sends a Violation on the channel AND a worker
// thread panics, the final result is Error (from the panic), not the Violation.
// This exercises the merge_worker_outcome path at finalize.rs:226-229.

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_join_panic_dominates_channel_violation() {
    let checker = checker_for_finalize_tests();

    let (tx, result_rx) = bounded::<WorkerResult>(4);
    // Worker sends a Violation through the channel
    tx.send(WorkerResult::Violation {
        invariant: "SomeInv".to_string(),
        state_fp: Fingerprint(999),
        stats: WorkerStats::default(),
    })
    .unwrap();
    drop(tx);

    // Worker thread panics (join error)
    let handles = vec![thread::spawn(|| panic!("worker panic after violation"))];
    let runtime = test_runtime(result_rx, handles, 1);

    let mut ctx = EvalCtx::new();
    let result = checker.finalize_check(
        runtime,
        Vec::new(),
        Vec::new(),
        &mut ctx,
        Vec::new(),
        Vec::new(),
    );

    // Error (from join panic) must dominate the channel-collected Violation
    match result {
        CheckResult::Error {
            error: CheckError::Infra(InfraCheckError::WorkerThreadPanicked { worker_id, message }),
            ..
        } => {
            assert_eq!(worker_id, 0);
            assert!(
                message.contains("worker panic after violation"),
                "panic message should be preserved, got: {message}"
            );
        }
        other => panic!(
            "Expected WorkerThreadPanicked error to dominate Violation, got: {:?}",
            other
        ),
    }
}

// Same test but with Deadlock instead of Violation, for completeness.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_join_panic_dominates_channel_deadlock() {
    let checker = checker_for_finalize_tests();

    let (tx, result_rx) = bounded::<WorkerResult>(4);
    tx.send(WorkerResult::Deadlock {
        state_fp: Fingerprint(123),
        stats: WorkerStats::default(),
    })
    .unwrap();
    drop(tx);

    let handles = vec![thread::spawn(|| panic!("worker panic after deadlock"))];
    let runtime = test_runtime(result_rx, handles, 1);

    let mut ctx = EvalCtx::new();
    let result = checker.finalize_check(
        runtime,
        Vec::new(),
        Vec::new(),
        &mut ctx,
        Vec::new(),
        Vec::new(),
    );

    match result {
        CheckResult::Error {
            error: CheckError::Infra(InfraCheckError::WorkerThreadPanicked { worker_id, message }),
            ..
        } => {
            assert_eq!(worker_id, 0);
            assert!(message.contains("worker panic after deadlock"));
        }
        other => panic!(
            "Expected WorkerThreadPanicked error to dominate Deadlock, got: {:?}",
            other
        ),
    }
}
