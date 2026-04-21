// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for OnceLock-based state snapshot accounting in finalize_check.
//! Covers ExitRequested snapshots, zero-count edge cases, and first-writer-wins.

use super::*;

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

/// Regression test for #2165: when ExitRequested is observed in finalize, it
/// must snapshot states_at_stop so final stats do not rely on fallback counts.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_exit_requested_snapshots_states_at_stop() {
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

    // Seed one known state so a successful snapshot has a deterministic value.
    let seeded_fp = Fingerprint(1);
    checker.seen.insert(seeded_fp, ArrayState::new(1));
    checker.seen_fps.insert_checked(seeded_fp);

    let (tx, rx) = bounded::<WorkerResult>(10);
    tx.send(WorkerResult::Error(
        EvalCheckError::Eval(tla_value::error::EvalError::ExitRequested { span: None }).into(),
        WorkerStats::default(),
    ))
    .expect("test channel send");
    tx.send(WorkerResult::Done(WorkerStats::default()))
        .expect("test channel send");
    drop(tx);

    let runtime = test_runtime(rx, 1);

    let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);

    let stats = match result {
        CheckResult::LimitReached {
            limit_type: LimitType::Exit,
            stats,
        } => stats,
        other => panic!("Expected CheckResult::LimitReached(Exit), got: {other:?}"),
    };

    assert_eq!(
        checker.states_at_stop.get().copied(),
        Some(1),
        "ExitRequested path should snapshot states_at_stop"
    );
    assert_eq!(
        stats.states_found, 1,
        "states_found should use the exit snapshot for accounting"
    );
}

/// Regression test for #2309: a zero-count snapshot must be treated as a real
/// snapshot, not as "unset". Before the fix, `states_at_stop` used `0` as
/// both the sentinel ("no snapshot taken") and a valid snapshot value.
/// OnceLock distinguishes `Some(0)` from `None`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_zero_count_snapshot_not_treated_as_unset() {
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

    // Do NOT seed any states — the seen set is empty (count = 0).
    // Simulate ExitRequested with zero states.
    let (tx, rx) = bounded::<WorkerResult>(10);
    tx.send(WorkerResult::Error(
        EvalCheckError::Eval(tla_value::error::EvalError::ExitRequested { span: None }).into(),
        WorkerStats::default(),
    ))
    .expect("test channel send");
    tx.send(WorkerResult::Done(WorkerStats::default()))
        .expect("test channel send");
    drop(tx);

    let runtime = test_runtime(rx, 0);

    let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);

    // Verify the snapshot was recorded as Some(0), not None
    assert_eq!(
        checker.states_at_stop.get().copied(),
        Some(0),
        "Zero-count snapshot must be recorded as Some(0), not treated as unset"
    );

    let stats = match result {
        CheckResult::LimitReached {
            limit_type: LimitType::Exit,
            stats,
        } => stats,
        other => panic!("Expected CheckResult::LimitReached(Exit), got: {other:?}"),
    };

    // The critical assertion: states_found should be 0 (from the snapshot),
    // not a fallback to states_count() which could be inflated by post-stop inserts.
    assert_eq!(
        stats.states_found, 0,
        "states_found must be 0 from the zero-count snapshot, not a fallback value"
    );
}

/// Regression test for #2309: snapshot_states_at_stop first-writer-wins with
/// count==0 followed by a non-zero attempt. The final value must remain 0.
/// This exercises the worker-path OnceLock semantics directly.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_snapshot_states_at_stop_first_writer_wins_zero() {
    use crate::state::Fingerprint;
    use crate::storage::ShardedFingerprintSet;
    use rustc_hash::FxHasher;
    use std::hash::BuildHasherDefault;

    type FxBuildHasher = BuildHasherDefault<FxHasher>;

    // Create empty shared state (0 states)
    let seen: DashMap<Fingerprint, ArrayState, FxBuildHasher> =
        DashMap::with_hasher(FxBuildHasher::default());
    let seen_fps: Arc<dyn crate::storage::FingerprintSet> = Arc::new(ShardedFingerprintSet::new(4));

    let states_at_stop = OnceLock::new();

    // First write: count = 0 (seen is empty)
    crate::parallel::snapshot_states_at_stop_for_test(&states_at_stop, &seen, &*seen_fps, true);

    assert_eq!(
        states_at_stop.get().copied(),
        Some(0),
        "First write with count=0 must set Some(0)"
    );

    // Insert a state to make count non-zero
    seen.insert(Fingerprint(42), ArrayState::new(1));

    // Second write attempt: should be a no-op (first writer wins)
    crate::parallel::snapshot_states_at_stop_for_test(&states_at_stop, &seen, &*seen_fps, true);

    assert_eq!(
        states_at_stop.get().copied(),
        Some(0),
        "Second write must be a no-op: OnceLock preserves first-writer's value of 0"
    );
}
