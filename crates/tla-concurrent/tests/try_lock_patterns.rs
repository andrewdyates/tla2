// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Try-lock integration tests: the classic "try-lock avoids ABBA deadlock"
//! pattern verified through ConcurrentModel -> TLA+ -> tla-check.

#![cfg(feature = "check")]

use tla_concurrent::*;

/// Build a 2-thread, 2-mutex model using try_lock to avoid ABBA deadlock.
///
/// Thread A: Lock m1, TryLockOk m2 (success path) or TryLockErr m2 (retry path).
///   Success: a0 -> Lock m1 -> a1 -> TryLockOk m2 -> a2 -> Unlock m2 -> a3 -> Unlock m1 -> done_a
///   Retry:   a1 -> TryLockErr m2 -> a4 -> Unlock m1 -> a0 (back to start)
///
/// Thread B: Lock m2, TryLockOk m1 (success path) or TryLockErr m1 (retry path).
///   Success: b0 -> Lock m2 -> b1 -> TryLockOk m1 -> b2 -> Unlock m1 -> b3 -> Unlock m2 -> done_b
///   Retry:   b1 -> TryLockErr m1 -> b4 -> Unlock m2 -> b0 (back to start)
///
/// This is the classic pattern: both threads need both mutexes but acquire them
/// in opposite order. Without try_lock this would be ABBA deadlock. With try_lock
/// the failing thread releases its held lock and retries, breaking the cycle.
fn try_lock_avoids_deadlock_model() -> ConcurrentModel {
    ConcurrentModel {
        processes: vec![
            Process {
                id: "thread_a".to_string(),
                kind: ProcessKind::Main,
                local_vars: vec![],
                transitions: vec![
                    // a0 -> a1: Lock m1
                    Transition {
                        from: "a0".to_string(),
                        to: "a1".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                    // a1 -> a2: TryLockOk m2 (success - got both locks)
                    Transition {
                        from: "a1".to_string(),
                        to: "a2".to_string(),
                        kind: TransitionKind::TryLockOk {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                    // a2 -> a3: Unlock m2
                    Transition {
                        from: "a2".to_string(),
                        to: "a3".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                    // a3 -> done_a: Unlock m1
                    Transition {
                        from: "a3".to_string(),
                        to: "done_a".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                    // a1 -> a4: TryLockErr m2 (fail - m2 held by thread_b)
                    Transition {
                        from: "a1".to_string(),
                        to: "a4".to_string(),
                        kind: TransitionKind::TryLockErr {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                    // a4 -> a0: Unlock m1 (release and retry)
                    Transition {
                        from: "a4".to_string(),
                        to: "a0".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "a0".to_string(),
                terminal_states: vec!["done_a".to_string()],
            },
            Process {
                id: "thread_b".to_string(),
                kind: ProcessKind::Spawned {
                    parent: "thread_a".to_string(),
                    join_handle_in_parent: None,
                },
                local_vars: vec![],
                transitions: vec![
                    // b0 -> b1: Lock m2
                    Transition {
                        from: "b0".to_string(),
                        to: "b1".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                    // b1 -> b2: TryLockOk m1 (success - got both locks)
                    Transition {
                        from: "b1".to_string(),
                        to: "b2".to_string(),
                        kind: TransitionKind::TryLockOk {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                    // b2 -> b3: Unlock m1
                    Transition {
                        from: "b2".to_string(),
                        to: "b3".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                    // b3 -> done_b: Unlock m2
                    Transition {
                        from: "b3".to_string(),
                        to: "done_b".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                    // b1 -> b4: TryLockErr m1 (fail - m1 held by thread_a)
                    Transition {
                        from: "b1".to_string(),
                        to: "b4".to_string(),
                        kind: TransitionKind::TryLockErr {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                    // b4 -> b0: Unlock m2 (release and retry)
                    Transition {
                        from: "b4".to_string(),
                        to: "b0".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "b0".to_string(),
                terminal_states: vec!["done_b".to_string()],
            },
        ],
        shared_vars: vec![],
        sync_primitives: vec![
            SyncPrimitive {
                id: "m1".to_string(),
                kind: SyncKind::Mutex {
                    reentrant: false,
                    poisonable: true,
                },
                name: Some("mutex_a".to_string()),
            },
            SyncPrimitive {
                id: "m2".to_string(),
                kind: SyncKind::Mutex {
                    reentrant: false,
                    poisonable: true,
                },
                name: Some("mutex_b".to_string()),
            },
        ],
        properties: vec![Property::DeadlockFreedom],
        assumptions: Assumptions {
            thread_bound: 2,
            ..Assumptions::default()
        },
        source_map: SourceMap::default(),
    }
}

/// Contrast model: the same ABBA pattern WITHOUT try_lock should deadlock.
///
/// Thread A: Lock m1 -> Lock m2 -> Unlock m2 -> Unlock m1 -> done_a
/// Thread B: Lock m2 -> Lock m1 -> Unlock m1 -> Unlock m2 -> done_b
///
/// This is the classic ABBA deadlock from checker_integration.rs, included
/// here for direct comparison with the try_lock version.
fn abba_without_try_lock_model() -> ConcurrentModel {
    ConcurrentModel {
        processes: vec![
            Process {
                id: "thread_a".to_string(),
                kind: ProcessKind::Main,
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "a0".to_string(),
                        to: "a1".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "a1".to_string(),
                        to: "a2".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "a2".to_string(),
                        to: "a3".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "a3".to_string(),
                        to: "done_a".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "a0".to_string(),
                terminal_states: vec!["done_a".to_string()],
            },
            Process {
                id: "thread_b".to_string(),
                kind: ProcessKind::Spawned {
                    parent: "thread_a".to_string(),
                    join_handle_in_parent: None,
                },
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "b0".to_string(),
                        to: "b1".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "b1".to_string(),
                        to: "b2".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "b2".to_string(),
                        to: "b3".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "b3".to_string(),
                        to: "done_b".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "b0".to_string(),
                terminal_states: vec!["done_b".to_string()],
            },
        ],
        shared_vars: vec![],
        sync_primitives: vec![
            SyncPrimitive {
                id: "m1".to_string(),
                kind: SyncKind::Mutex {
                    reentrant: false,
                    poisonable: true,
                },
                name: Some("mutex_a".to_string()),
            },
            SyncPrimitive {
                id: "m2".to_string(),
                kind: SyncKind::Mutex {
                    reentrant: false,
                    poisonable: true,
                },
                name: Some("mutex_b".to_string()),
            },
        ],
        properties: vec![Property::DeadlockFreedom],
        assumptions: Assumptions {
            thread_bound: 2,
            ..Assumptions::default()
        },
        source_map: SourceMap::default(),
    }
}

#[test]
fn test_try_lock_avoids_abba_deadlock() {
    let model = try_lock_avoids_deadlock_model();
    let result = check_concurrent_model(&model, &CheckOptions::default())
        .expect("check should not error");

    assert_eq!(
        result.report.status,
        VerificationStatus::AllPropertiesHold,
        "try-lock pattern should break ABBA deadlock cycle, got: {:?}",
        result.report.status
    );
    assert!(result.report.counterexample.is_none());
    assert_eq!(result.assumptions.thread_bound, 2);
    assert!(result.report.stats.states_found > 0, "should explore states");
}

#[test]
fn test_abba_without_try_lock_deadlocks() {
    let model = abba_without_try_lock_model();
    let result = check_concurrent_model(&model, &CheckOptions::default())
        .expect("check should not error");

    // Without try_lock, the ABBA pattern causes deadlock.
    assert!(
        matches!(
            result.report.status,
            VerificationStatus::DeadlockDetected
        ),
        "ABBA without try_lock should deadlock, got: {:?}",
        result.report.status
    );
}

#[test]
fn test_try_lock_model_explores_retry_paths() {
    let model = try_lock_avoids_deadlock_model();
    let result = check_concurrent_model(&model, &CheckOptions::default())
        .expect("check should not error");

    // The try_lock model has retry loops, so it should explore more states than
    // the simple ABBA model. The exact count depends on the state space but
    // should be non-trivial due to the interleaving of retries.
    assert!(
        result.report.stats.states_found >= 5,
        "try-lock model should explore multiple states from retry paths, got: {}",
        result.report.stats.states_found
    );
}
