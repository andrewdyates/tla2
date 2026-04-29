// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::super::collision_debug::{CollisionDebugConfig, ParallelCollisionDiagnostics};
use super::*;
use crate::config::Config;
use crate::Value;
use std::sync::Arc;
use std::time::Instant;

fn install_collision_diagnostics(checker: &mut ParallelChecker) {
    let diagnostics = Arc::new(ParallelCollisionDiagnostics::new(
        CollisionDebugConfig {
            track_seen_tlc_fp_dedup: true,
            seen_tlc_fp_dedup_collision_limit: 0,
            track_internal_fp_collision: true,
            internal_fp_collision_limit: 0,
        },
        4,
    ));
    diagnostics.record_state(
        Fingerprint(0x1111),
        &ArrayState::from_values(vec![Value::int(1)]),
        0,
    );
    diagnostics.record_state(
        Fingerprint(0x2222),
        &ArrayState::from_values(vec![Value::int(1)]),
        1,
    );
    diagnostics.record_state(
        Fingerprint(0x3333),
        &ArrayState::from_values(vec![Value::int(2)]),
        2,
    );
    diagnostics.record_state(
        Fingerprint(0x3333),
        &ArrayState::from_values(vec![Value::int(3)]),
        3,
    );
    checker.collision_diagnostics = Some(diagnostics);
}

fn collision_checker() -> ParallelChecker {
    let src = r#"
---- MODULE CollisionStats ----
VARIABLE x
Init == x = 0
Next == x' = x
====
"#;
    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };
    ParallelChecker::new(&module, &config, 1)
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_collision_counters_appear_in_runtime_snapshot() {
    let mut checker = collision_checker();
    install_collision_diagnostics(&mut checker);

    let stats = checker.snapshot_runtime_stats(0, &[], &[]);
    assert_eq!(stats.fp_dedup_collisions, 1);
    assert_eq!(stats.internal_fp_collisions, 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_collision_counters_appear_in_finalize_success() {
    let mut checker = collision_checker();
    install_collision_diagnostics(&mut checker);

    let (tx, rx) = bounded::<WorkerResult>(1);
    drop(tx);
    let runtime = CheckRuntime {
        result_rx: rx,
        handles: vec![],
        num_initial: 0,
        start_time: Instant::now(),
        jit_compiled_invariants: 0,
    };
    let mut ctx = EvalCtx::new();

    let result = checker.finalize_check(runtime, vec![], vec![], &mut ctx, vec![], vec![]);
    let CheckResult::Success(stats) = result else {
        unreachable!("expected Success, got {result:?}");
    };

    assert_eq!(stats.fp_dedup_collisions, 1);
    assert_eq!(stats.internal_fp_collisions, 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_parallel_action_ids_survive_runtime_snapshot_and_finalize_success() {
    let checker = collision_checker();
    let detected_actions = [String::from("Foo"), String::from("Foo")];
    let detected_action_ids = [String::from("7:10-13"), String::from("7:20-23")];

    let snapshot = checker.snapshot_runtime_stats(0, &detected_actions, &detected_action_ids);
    assert_eq!(snapshot.detected_actions, detected_actions);
    assert_eq!(snapshot.detected_action_ids, detected_action_ids);

    let (tx, rx) = bounded::<WorkerResult>(1);
    drop(tx);
    let runtime = CheckRuntime {
        result_rx: rx,
        handles: vec![],
        num_initial: 0,
        start_time: Instant::now(),
        jit_compiled_invariants: 0,
    };
    let mut ctx = EvalCtx::new();

    let result = checker.finalize_check(
        runtime,
        detected_actions.to_vec(),
        detected_action_ids.to_vec(),
        &mut ctx,
        vec![],
        vec![],
    );
    let CheckResult::Success(stats) = result else {
        unreachable!("expected Success, got {result:?}");
    };

    assert_eq!(stats.detected_actions, detected_actions);
    assert_eq!(stats.detected_action_ids, detected_action_ids);
}
