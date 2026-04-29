// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parity tests — send_result regression (#1443), depth-limit parity (#2216),
//! storage error precedence (#1801)

use super::parse_module;
use super::*;
use crate::check::CheckError;
use crate::CheckStats;
use crate::LimitType;

fn depth_bounded_stats(result: &CheckResult, label: &str) -> CheckStats {
    match result {
        CheckResult::LimitReached {
            limit_type: LimitType::Depth,
            stats,
        } => stats.clone(),
        CheckResult::Success(stats) => stats.clone(),
        other => panic!("{label}: unexpected bounded-check result: {other:?}"),
    }
}

// ==========================================
// Regression test for #1443: send_result
// ==========================================

/// Verify send_result does not panic when channel is disconnected.
///
/// Part of #1443: Previously, `let _ = result_tx.send(...)` silently discarded
/// send failures. Now `send_result()` logs a warning instead of panicking.
/// This test verifies the non-panic guarantee for all WorkerResult variants.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_send_result_disconnected_channel_does_not_panic() {
    use crossbeam_channel::bounded;
    use worker::send_result;

    let (tx, rx) = bounded::<WorkerResult>(1);
    // Drop receiver to disconnect the channel
    drop(rx);

    let stats = WorkerStats::default();

    // Each of these should log a warning, not panic.
    // Verify all 6 variants complete without panicking on disconnected channel.
    let mut sent_count = 0u32;

    send_result(
        &tx,
        WorkerResult::Violation {
            invariant: "TestInv".to_string(),
            state_fp: Fingerprint(0),
            stats: stats.clone(),
        },
    );
    sent_count += 1;

    send_result(
        &tx,
        WorkerResult::Deadlock {
            state_fp: Fingerprint(0),
            stats: stats.clone(),
        },
    );
    sent_count += 1;

    send_result(
        &tx,
        WorkerResult::PropertyActionViolation {
            property: "Prop".to_string(),
            state_fp: Fingerprint(0),
            stats: stats.clone(),
        },
    );
    sent_count += 1;

    send_result(
        &tx,
        WorkerResult::Error(ConfigCheckError::MissingNext.into(), stats.clone()),
    );
    sent_count += 1;

    send_result(&tx, WorkerResult::Done(stats.clone()));
    sent_count += 1;

    send_result(
        &tx,
        WorkerResult::LimitReached {
            limit_type: LimitType::States,
            stats,
        },
    );
    sent_count += 1;

    assert_eq!(
        sent_count, 6,
        "all 6 WorkerResult variants should be tested on disconnected channel"
    );
}

/// Verify send_result delivers results on healthy channel.
///
/// Part of #1443: Ensure the refactoring from `let _ =` to `send_result()`
/// doesn't break normal result delivery.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_send_result_delivers_on_healthy_channel() {
    use crossbeam_channel::bounded;
    use worker::send_result;

    let (tx, rx) = bounded::<WorkerResult>(5);

    send_result(
        &tx,
        WorkerResult::Violation {
            invariant: "Inv1".to_string(),
            state_fp: Fingerprint(42),
            stats: WorkerStats::default(),
        },
    );
    send_result(
        &tx,
        WorkerResult::PropertyActionViolation {
            property: "Prop1".to_string(),
            state_fp: Fingerprint(24),
            stats: WorkerStats::default(),
        },
    );
    send_result(&tx, WorkerResult::Done(WorkerStats::default()));

    // Verify all results were received
    let r1 = rx.recv().expect("Should receive Violation");
    assert!(matches!(r1, WorkerResult::Violation { .. }));

    let r2 = rx.recv().expect("Should receive PropertyActionViolation");
    assert!(matches!(r2, WorkerResult::PropertyActionViolation { .. }));

    let r3 = rx.recv().expect("Should receive Done");
    assert!(matches!(r3, WorkerResult::Done(_)));
}

// Part of #2216: Parity tests for depth-limit semantics.

/// Test 1 from design doc "Required Tests":
/// Compare serial vs parallel `states_found` exactly on a branching spec under `--max-depth`.
/// Uses a spec with multiple successors per state to exercise non-trivial BFS depth behavior.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_depth_limit_serial_vs_parallel_states_found_parity() {
    let _serial = super::acquire_interner_lock();
    // Branching spec: each state has two successors (x+1, x+2), creating a tree
    // where multiple states exist at the same depth. This is more interesting than
    // a linear counter for verifying depth-limit state counting.
    let src = r#"
---- MODULE BranchDepth ----
VARIABLE x
Init == x \in {0, 1}
Next == x' \in {x + 1, x + 2}
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        check_deadlock: false,
        ..Default::default()
    };

    for max_depth in [1, 2, 3, 5] {
        let mut seq_checker = crate::check::ModelChecker::new(&module, &config);
        seq_checker.set_deadlock_check(false);
        seq_checker.set_max_depth(max_depth);
        let seq_result = seq_checker.check();
        let seq_stats = depth_bounded_stats(&seq_result, &format!("serial depth={max_depth}"));

        for workers in [1, 2, 4] {
            let mut par_checker = ParallelChecker::new(&module, &config, workers);
            par_checker.set_deadlock_check(false);
            par_checker.set_max_depth(max_depth);
            let par_result = par_checker.check();
            let par_stats = depth_bounded_stats(
                &par_result,
                &format!("parallel workers={workers} depth={max_depth}"),
            );

            assert_eq!(
                seq_stats.states_found, par_stats.states_found,
                "workers={workers} depth={max_depth}: serial states_found ({}) != parallel states_found ({})",
                seq_stats.states_found, par_stats.states_found,
            );

            assert_eq!(
                std::mem::discriminant(&seq_result),
                std::mem::discriminant(&par_result),
                "workers={workers} depth={max_depth}: result types differ: serial={:?}, parallel={:?}",
                seq_result,
                par_result,
            );
        }
    }
}

/// Test 2 from design doc "Required Tests":
/// Continue-on-error + depth-limit precedence parity: serial and parallel must return
/// the same terminal result type and state count when both an invariant violation
/// and depth limit are present.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_depth_limit_continue_on_error_precedence_parity() {
    let _serial = super::acquire_interner_lock();
    // Invariant Small fails at x=2. With max_depth=5, the depth limit is hit
    // while continue_on_error is still exploring. Serial finalize_bfs checks
    // depth_limit_reached BEFORE deferred violations (run_helpers.rs:355-360),
    // so depth limit takes precedence. Parallel must match this.
    let src = r#"
---- MODULE DepthContinue ----
VARIABLE x
Init == x = 0
Next == x < 10 /\ x' = x + 1
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

    // Serial
    let mut seq_checker = crate::check::ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    seq_checker.set_continue_on_error(true);
    seq_checker.set_max_depth(5);
    let seq_result = seq_checker.check();

    // Parallel (2 workers exercises the bounded shared-frontier path).
    let mut par_checker = ParallelChecker::new(&module, &config, 2);
    par_checker.set_deadlock_check(false);
    par_checker.set_continue_on_error(true);
    par_checker.set_max_depth(5);
    let par_result = par_checker.check();

    // Both should report depth limit (takes precedence over deferred violations).
    // Serial finalize_bfs: depth_limit_reached checked at line 355 before
    // first_violation at line 364. Parallel finalize_check matches this order.
    let seq_stats = match &seq_result {
        CheckResult::LimitReached {
            limit_type: LimitType::Depth,
            stats,
        } => stats.clone(),
        other => panic!("Expected serial LimitReached(Depth), got: {:?}", other),
    };

    let par_stats = match &par_result {
        CheckResult::LimitReached {
            limit_type: LimitType::Depth,
            stats,
        } => stats.clone(),
        other => panic!("Expected parallel LimitReached(Depth), got: {:?}", other),
    };

    // State counts must match
    assert_eq!(
        seq_stats.states_found, par_stats.states_found,
        "continue_on_error+depth: serial states_found ({}) != parallel states_found ({})",
        seq_stats.states_found, par_stats.states_found,
    );
}

/// Test 3 from design doc "Required Tests":
/// Regression assertion that depth limit alone does not trigger global stop_flag.
/// This verifies the core semantic change: depth_limit_reached is a separate signal.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_depth_limit_does_not_set_stop_flag() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE Counter ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 2);
    checker.set_deadlock_check(false);
    checker.set_max_depth(3);

    let result = checker.check();

    // Should reach depth limit
    assert!(
        matches!(
            result,
            CheckResult::LimitReached {
                limit_type: LimitType::Depth,
                ..
            }
        ),
        "Expected LimitReached(Depth), got: {:?}",
        result
    );

    // The stop_flag must NOT have been set by the depth limit.
    // This is the core regression assertion: in the old code, depth limit
    // called snapshot_stop_and_send which set stop_flag. Now it only sets
    // depth_limit_reached.
    assert!(
        !checker.stop_flag.load(std::sync::atomic::Ordering::Relaxed),
        "stop_flag must not be set by depth limit alone — \
         depth_limit_reached is the separate signal"
    );
}

/// Part of #3266: exact parity regression for a state reachable from both a
/// shallow and a deeper path. If the deeper winner is admitted first, `x = 3`
/// is pruned at `max_depth = 2` and the state count falls below the sequential
/// BFS result.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_depth_limit_parallel_prefers_shallow_discovery_depth() {
    let _serial = super::acquire_interner_lock();
    let src = r#"
---- MODULE MultiWorkerDepth ----
VARIABLE x
Init == x \in {0, 9}
Next ==
    \/ x = 0 /\ x' = 1
    \/ x = 9 /\ x' = 2
    \/ x = 2 /\ x' = 1
    \/ x = 1 /\ x' = 3
====
"#;
    let module = parse_module(src);

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        check_deadlock: false,
        ..Default::default()
    };

    let max_depth = 2;

    let mut seq_checker = crate::check::ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    seq_checker.set_max_depth(max_depth);
    let seq_result = seq_checker.check();
    let seq_stats = depth_bounded_stats(&seq_result, "serial shallow-depth regression");

    let mut par_checker = ParallelChecker::new(&module, &config, 2);
    par_checker.set_deadlock_check(false);
    par_checker.set_max_depth(max_depth);
    let par_result = par_checker.check();
    let par_stats = depth_bounded_stats(&par_result, "parallel shallow-depth regression");

    assert_eq!(
        seq_stats.states_found, 5,
        "serial BFS should keep the shallow discovery of x=1 and still reach x=3 at depth 2"
    );
    assert_eq!(
        seq_stats.states_found, par_stats.states_found,
        "parallel bounded BFS must preserve the shallow winner for duplicated fingerprints"
    );
    assert_eq!(
        std::mem::discriminant(&seq_result),
        std::mem::discriminant(&par_result),
        "serial and parallel must report the same terminal result under the depth bound"
    );
}

/// Part of #1801: Verify serial and parallel checkers apply the same
/// precedence order when both a storage error and an invariant violation
/// are present. Both must return FingerprintStorageOverflow, not InvariantViolation.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_storage_error_precedence_parity_serial_vs_parallel() {
    let _serial = super::acquire_interner_lock();
    use crate::storage::{FingerprintSet, InsertOutcome, LookupOutcome};

    /// Shared FingerprintSet that reports `dropped` lost inserts.
    struct SharedErrorFpSet {
        dropped: usize,
    }
    impl tla_mc_core::FingerprintSet<crate::Fingerprint> for SharedErrorFpSet {
        fn insert_checked(&self, _fp: crate::Fingerprint) -> InsertOutcome {
            InsertOutcome::Inserted
        }
        fn contains_checked(&self, _fp: crate::Fingerprint) -> LookupOutcome {
            LookupOutcome::Absent
        }
        fn len(&self) -> usize {
            1
        }
        fn has_errors(&self) -> bool {
            self.dropped > 0
        }
        fn dropped_count(&self) -> usize {
            self.dropped
        }
    }

    impl FingerprintSet for SharedErrorFpSet {}

    let src = r#"
---- MODULE StorageErrPrecedenceParity ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = IF x = 0 THEN 1 ELSE 0
Safe == x = 0
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safe".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let dropped = 55;

    // Serial checker
    let mut seq_checker = crate::check::ModelChecker::new(&module, &config);
    seq_checker.set_deadlock_check(false);
    let seq_storage = Arc::new(SharedErrorFpSet { dropped }) as Arc<dyn FingerprintSet>;
    seq_checker.set_fingerprint_storage(seq_storage);
    let seq_result = seq_checker.check();

    // Parallel checker (1 worker for determinism)
    let mut par_checker = ParallelChecker::new(&module, &config, 1);
    par_checker.set_deadlock_check(false);
    let par_storage = Arc::new(SharedErrorFpSet { dropped }) as Arc<dyn FingerprintSet>;
    par_checker.set_fingerprint_storage(par_storage);
    let par_result = par_checker.check();

    // Both must return FingerprintStorageOverflow, not InvariantViolation
    match &seq_result {
        CheckResult::Error {
            error:
                CheckError::Infra(crate::check::InfraCheckError::FingerprintOverflow {
                    dropped: d, ..
                }),
            ..
        } => {
            assert_eq!(*d, dropped, "serial: wrong dropped count");
        }
        other => {
            panic!(
                "Serial: expected FingerprintStorageOverflow(dropped={dropped}), got: {other:?}"
            );
        }
    }

    match &par_result {
        CheckResult::Error {
            error:
                CheckError::Infra(crate::check::InfraCheckError::FingerprintOverflow {
                    dropped: d, ..
                }),
            ..
        } => {
            assert_eq!(*d, dropped, "parallel: wrong dropped count");
        }
        other => {
            panic!(
                "Parallel: expected FingerprintStorageOverflow(dropped={dropped}), got: {other:?}"
            );
        }
    }
}
