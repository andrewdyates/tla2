// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dining philosophers integration tests.
//!
//! Validates that the tla-concurrent checker detects the classic circular-wait
//! deadlock in the naive dining philosophers protocol, and that the asymmetric
//! (last-philosopher-reversed) variant is deadlock-free.

#![cfg(feature = "check")]

use tla_concurrent::*;

/// Build an N-philosopher model where every philosopher picks up the left fork
/// first, then the right fork. This creates a circular wait and deadlocks.
fn dining_philosophers_deadlock(n: usize) -> ConcurrentModel {
    assert!(n >= 2, "need at least 2 philosophers");

    let processes: Vec<Process> = (0..n)
        .map(|i| {
            let id = format!("phil_{i}");
            let left_fork = format!("fork_{i}");
            let right_fork = format!("fork_{}", (i + 1) % n);

            Process {
                id: id.clone(),
                kind: if i == 0 {
                    ProcessKind::Main
                } else {
                    ProcessKind::Spawned {
                        parent: "phil_0".to_string(),
                        join_handle_in_parent: None,
                    }
                },
                local_vars: vec![],
                transitions: vec![
                    // thinking -> has_left: pick up left fork
                    Transition {
                        from: format!("thinking_{i}"),
                        to: format!("has_left_{i}"),
                        kind: TransitionKind::Lock {
                            mutex: left_fork.clone(),
                        },
                        source_map_index: None,
                    },
                    // has_left -> has_both: pick up right fork
                    Transition {
                        from: format!("has_left_{i}"),
                        to: format!("has_both_{i}"),
                        kind: TransitionKind::Lock {
                            mutex: right_fork.clone(),
                        },
                        source_map_index: None,
                    },
                    // has_both -> released: put down right fork
                    Transition {
                        from: format!("has_both_{i}"),
                        to: format!("released_{i}"),
                        kind: TransitionKind::Unlock {
                            mutex: right_fork,
                        },
                        source_map_index: None,
                    },
                    // released -> done: put down left fork
                    Transition {
                        from: format!("released_{i}"),
                        to: format!("done_phil_{i}"),
                        kind: TransitionKind::Unlock {
                            mutex: left_fork,
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: format!("thinking_{i}"),
                terminal_states: vec![format!("done_phil_{i}")],
            }
        })
        .collect();

    let sync_primitives: Vec<SyncPrimitive> = (0..n)
        .map(|i| SyncPrimitive {
            id: format!("fork_{i}"),
            kind: SyncKind::Mutex {
                reentrant: false,
                poisonable: true,
            },
            name: Some(format!("fork_{i}")),
        })
        .collect();

    ConcurrentModel {
        processes,
        shared_vars: vec![],
        sync_primitives,
        properties: vec![Property::DeadlockFreedom],
        assumptions: Assumptions {
            thread_bound: n,
            ..Assumptions::default()
        },
        source_map: SourceMap::default(),
    }
}

/// Build an N-philosopher model where the last philosopher picks up forks in
/// reverse order (right first, then left). This breaks the circular wait and
/// prevents deadlock.
fn dining_philosophers_correct(n: usize) -> ConcurrentModel {
    assert!(n >= 2, "need at least 2 philosophers");

    let processes: Vec<Process> = (0..n)
        .map(|i| {
            let id = format!("phil_{i}");
            let left_fork = format!("fork_{i}");
            let right_fork = format!("fork_{}", (i + 1) % n);

            // Last philosopher reverses fork acquisition order to break the cycle.
            let (first_fork, second_fork) = if i == n - 1 {
                (right_fork.clone(), left_fork.clone())
            } else {
                (left_fork.clone(), right_fork.clone())
            };

            Process {
                id: id.clone(),
                kind: if i == 0 {
                    ProcessKind::Main
                } else {
                    ProcessKind::Spawned {
                        parent: "phil_0".to_string(),
                        join_handle_in_parent: None,
                    }
                },
                local_vars: vec![],
                transitions: vec![
                    // thinking -> has_left: pick up first fork
                    Transition {
                        from: format!("thinking_{i}"),
                        to: format!("has_left_{i}"),
                        kind: TransitionKind::Lock {
                            mutex: first_fork.clone(),
                        },
                        source_map_index: None,
                    },
                    // has_left -> has_both: pick up second fork
                    Transition {
                        from: format!("has_left_{i}"),
                        to: format!("has_both_{i}"),
                        kind: TransitionKind::Lock {
                            mutex: second_fork.clone(),
                        },
                        source_map_index: None,
                    },
                    // has_both -> released: put down second fork
                    Transition {
                        from: format!("has_both_{i}"),
                        to: format!("released_{i}"),
                        kind: TransitionKind::Unlock {
                            mutex: second_fork,
                        },
                        source_map_index: None,
                    },
                    // released -> done: put down first fork
                    Transition {
                        from: format!("released_{i}"),
                        to: format!("done_phil_{i}"),
                        kind: TransitionKind::Unlock {
                            mutex: first_fork,
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: format!("thinking_{i}"),
                terminal_states: vec![format!("done_phil_{i}")],
            }
        })
        .collect();

    let sync_primitives: Vec<SyncPrimitive> = (0..n)
        .map(|i| SyncPrimitive {
            id: format!("fork_{i}"),
            kind: SyncKind::Mutex {
                reentrant: false,
                poisonable: true,
            },
            name: Some(format!("fork_{i}")),
        })
        .collect();

    ConcurrentModel {
        processes,
        shared_vars: vec![],
        sync_primitives,
        properties: vec![Property::DeadlockFreedom],
        assumptions: Assumptions {
            thread_bound: n,
            ..Assumptions::default()
        },
        source_map: SourceMap::default(),
    }
}

// --- Deadlock tests ---

#[test]
fn dining_philosophers_2_deadlock() {
    // N=2 is structurally the same as ABBA — should deadlock.
    let model = dining_philosophers_deadlock(2);
    let result = check_concurrent_model(&model, &CheckOptions::default())
        .expect("check should not error");
    assert!(
        matches!(
            result.report.status,
            VerificationStatus::DeadlockDetected
        ),
        "2 philosophers with uniform left-first ordering should deadlock, got: {:?}",
        result.report.status
    );
}

#[test]
fn dining_philosophers_3_deadlock() {
    let model = dining_philosophers_deadlock(3);
    let result = check_concurrent_model(&model, &CheckOptions::default())
        .expect("check should not error");
    assert!(
        matches!(
            result.report.status,
            VerificationStatus::DeadlockDetected
        ),
        "3 philosophers with uniform left-first ordering should deadlock, got: {:?}",
        result.report.status
    );
}

#[test]
fn dining_philosophers_5_deadlock() {
    let model = dining_philosophers_deadlock(5);
    let result = check_concurrent_model(&model, &CheckOptions::default())
        .expect("check should not error");
    assert!(
        matches!(
            result.report.status,
            VerificationStatus::DeadlockDetected
        ),
        "5 philosophers with uniform left-first ordering should deadlock, got: {:?}",
        result.report.status
    );
}

// --- Correct (asymmetric) tests ---

#[test]
fn dining_philosophers_3_correct() {
    let model = dining_philosophers_correct(3);
    let result = check_concurrent_model(&model, &CheckOptions::default())
        .expect("check should not error");
    assert_eq!(
        result.report.status,
        VerificationStatus::AllPropertiesHold,
        "3 philosophers with last-reversed ordering should be deadlock-free, got: {:?}",
        result.report.status
    );
}

#[test]
fn dining_philosophers_5_correct() {
    let model = dining_philosophers_correct(5);
    let result = check_concurrent_model(&model, &CheckOptions::default())
        .expect("check should not error");
    assert_eq!(
        result.report.status,
        VerificationStatus::AllPropertiesHold,
        "5 philosophers with last-reversed ordering should be deadlock-free, got: {:?}",
        result.report.status
    );
}
