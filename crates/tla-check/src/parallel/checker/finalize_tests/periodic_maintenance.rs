// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::config::Config;
use crate::ConfigCheckError;
use crate::Value;

fn seed_single_state(checker: &ParallelChecker, x: i64) {
    let mut state = ArrayState::from_values(vec![Value::int(x)]);
    let fp = state.fingerprint(&checker.var_registry);
    checker.seen.insert(fp, state);
    checker.depths.insert(fp, 0);
    let _ = checker.seen_fps.insert_checked(fp);
}

fn spawn_barrier_participant(
    checker: &ParallelChecker,
    tx: crossbeam_channel::Sender<WorkerResult>,
    terminal: WorkerResult,
) -> std::thread::JoinHandle<()> {
    let barrier = Arc::clone(&checker.barrier);
    let stop_flag = Arc::clone(&checker.stop_flag);
    std::thread::spawn(move || {
        let start = Instant::now();
        while !stop_flag.load(Ordering::Relaxed) && start.elapsed() < Duration::from_secs(2) {
            barrier.worker_check();
            std::thread::sleep(Duration::from_millis(10));
        }
        let _ = tx.send(terminal);
    })
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_runs_periodic_liveness_without_checkpointing() {
    let src = r#"
---- MODULE PeriodicProperty ----
VARIABLE x
Init == x = 0
Next == x' = x
P == [](x = 1)
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["P".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 1);
    checker.periodic_liveness.check_interval_ms = 0;
    checker.periodic_liveness.growth_threshold = 0.0;
    seed_single_state(&checker, 0);

    // Simulate active BFS so the periodic maintenance idle gate
    // (work_remaining == 0 && active_workers == 0 → skip) does not
    // prevent periodic liveness from running.
    checker.work_remaining.store(1, Ordering::Release);

    let (tx, rx) = bounded::<WorkerResult>(1);
    let handle =
        spawn_barrier_participant(&checker, tx, WorkerResult::Done(WorkerStats::default()));
    let runtime = CheckRuntime {
        result_rx: rx,
        handles: vec![handle],
        num_initial: 1,
        start_time: Instant::now(),
        jit_compiled_invariants: 0,
    };

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_vars(checker.vars.iter().cloned());
    ctx.resolve_state_vars_in_loaded_ops();
    let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);

    let CheckResult::PropertyViolation {
        property,
        kind: crate::check::PropertyViolationKind::StateLevel,
        stats,
        ..
    } = result
    else {
        unreachable!("expected periodic PropertyViolation, got: {result:?}");
    };
    assert_eq!(property, "P");
    assert_eq!(stats.states_found, 1);

    assert!(
        checker.stop_flag.load(Ordering::SeqCst),
        "periodic result should request worker shutdown"
    );
    assert_eq!(
        checker.states_at_stop.get().copied(),
        Some(1),
        "periodic result should snapshot states_at_stop immediately"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_finalize_runs_periodic_liveness_in_fingerprint_only_mode() {
    let src = r#"
---- MODULE PeriodicPropertyFpOnly ----
VARIABLE x
Init == x = 0
Next == x' = x
P == [](x = 1)
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["P".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 1);
    checker.set_store_states(false);
    checker.periodic_liveness.check_interval_ms = 0;
    checker.periodic_liveness.growth_threshold = 0.0;
    seed_single_state(&checker, 0);

    checker.work_remaining.store(1, Ordering::Release);

    let (tx, rx) = bounded::<WorkerResult>(1);
    let handle =
        spawn_barrier_participant(&checker, tx, WorkerResult::Done(WorkerStats::default()));
    let runtime = CheckRuntime {
        result_rx: rx,
        handles: vec![handle],
        num_initial: 1,
        start_time: Instant::now(),
        jit_compiled_invariants: 0,
    };

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_vars(checker.vars.iter().cloned());
    ctx.resolve_state_vars_in_loaded_ops();
    let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);

    let CheckResult::PropertyViolation {
        property,
        kind: crate::check::PropertyViolationKind::StateLevel,
        stats,
        ..
    } = result
    else {
        unreachable!("expected periodic fp-only PropertyViolation, got: {result:?}");
    };
    assert_eq!(property, "P");
    assert_eq!(stats.states_found, 1);

    assert!(
        checker.stop_flag.load(Ordering::SeqCst),
        "periodic fp-only result should request worker shutdown"
    );
    assert_eq!(
        checker.states_at_stop.get().copied(),
        Some(1),
        "periodic fp-only result should snapshot states_at_stop immediately"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_worker_error_overrides_periodic_result() {
    let src = r#"
---- MODULE PeriodicProperty ----
VARIABLE x
Init == x = 0
Next == x' = x
P == [](x = 1)
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["P".to_string()],
        ..Default::default()
    };

    let mut checker = ParallelChecker::new(&module, &config, 1);
    checker.periodic_liveness.check_interval_ms = 0;
    checker.periodic_liveness.growth_threshold = 0.0;
    seed_single_state(&checker, 0);

    let (tx, rx) = bounded::<WorkerResult>(1);
    let handle = spawn_barrier_participant(
        &checker,
        tx,
        WorkerResult::Error(ConfigCheckError::MissingNext.into(), WorkerStats::default()),
    );
    let runtime = CheckRuntime {
        result_rx: rx,
        handles: vec![handle],
        num_initial: 1,
        start_time: Instant::now(),
        jit_compiled_invariants: 0,
    };

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    ctx.register_vars(checker.vars.iter().cloned());
    ctx.resolve_state_vars_in_loaded_ops();
    let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);

    let CheckResult::Error {
        error: CheckError::Config(ConfigCheckError::MissingNext),
        ..
    } = result
    else {
        unreachable!("expected worker MissingNext error to win, got: {result:?}");
    };
}
