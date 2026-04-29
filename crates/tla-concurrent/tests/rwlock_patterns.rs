// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for RwLock patterns: concurrent readers, reader-writer
//! interleaving, and serialized writers.

#![cfg(feature = "check")]

use tla_concurrent::*;

/// Build a model with 3 processes all doing read-lock on the same RwLock.
/// Concurrent reads should not deadlock.
fn concurrent_readers_model() -> ConcurrentModel {
    ConcurrentModel {
        processes: vec![
            Process {
                id: "main".to_string(),
                kind: ProcessKind::Main,
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "s0".to_string(),
                        to: "s1".to_string(),
                        kind: TransitionKind::ReadLock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "s1".to_string(),
                        to: "done_main".to_string(),
                        kind: TransitionKind::ReadUnlock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "s0".to_string(),
                terminal_states: vec!["done_main".to_string()],
            },
            Process {
                id: "t1".to_string(),
                kind: ProcessKind::Spawned {
                    parent: "main".to_string(),
                    join_handle_in_parent: None,
                },
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "u0".to_string(),
                        to: "u1".to_string(),
                        kind: TransitionKind::ReadLock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "u1".to_string(),
                        to: "done_t1".to_string(),
                        kind: TransitionKind::ReadUnlock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "u0".to_string(),
                terminal_states: vec!["done_t1".to_string()],
            },
            Process {
                id: "t2".to_string(),
                kind: ProcessKind::Spawned {
                    parent: "main".to_string(),
                    join_handle_in_parent: None,
                },
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "v0".to_string(),
                        to: "v1".to_string(),
                        kind: TransitionKind::ReadLock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "v1".to_string(),
                        to: "done_t2".to_string(),
                        kind: TransitionKind::ReadUnlock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "v0".to_string(),
                terminal_states: vec!["done_t2".to_string()],
            },
        ],
        shared_vars: vec![],
        sync_primitives: vec![SyncPrimitive {
            id: "rw0".to_string(),
            kind: SyncKind::RwLock { poisonable: false },
            name: Some("data_rwlock".to_string()),
        }],
        properties: vec![Property::DeadlockFreedom],
        assumptions: Assumptions {
            thread_bound: 3,
            ..Assumptions::default()
        },
        source_map: SourceMap::default(),
    }
}

/// Build a model with 1 writer + 2 readers on the same RwLock.
/// The writer holds exclusive access; readers share access. No deadlock.
fn reader_writer_interleaving_model() -> ConcurrentModel {
    ConcurrentModel {
        processes: vec![
            // Writer (main process)
            Process {
                id: "main".to_string(),
                kind: ProcessKind::Main,
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "s0".to_string(),
                        to: "s1".to_string(),
                        kind: TransitionKind::WriteLock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "s1".to_string(),
                        to: "done_main".to_string(),
                        kind: TransitionKind::WriteUnlock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "s0".to_string(),
                terminal_states: vec!["done_main".to_string()],
            },
            // Reader 1
            Process {
                id: "r1".to_string(),
                kind: ProcessKind::Spawned {
                    parent: "main".to_string(),
                    join_handle_in_parent: None,
                },
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "u0".to_string(),
                        to: "u1".to_string(),
                        kind: TransitionKind::ReadLock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "u1".to_string(),
                        to: "done_r1".to_string(),
                        kind: TransitionKind::ReadUnlock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "u0".to_string(),
                terminal_states: vec!["done_r1".to_string()],
            },
            // Reader 2
            Process {
                id: "r2".to_string(),
                kind: ProcessKind::Spawned {
                    parent: "main".to_string(),
                    join_handle_in_parent: None,
                },
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "v0".to_string(),
                        to: "v1".to_string(),
                        kind: TransitionKind::ReadLock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "v1".to_string(),
                        to: "done_r2".to_string(),
                        kind: TransitionKind::ReadUnlock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "v0".to_string(),
                terminal_states: vec!["done_r2".to_string()],
            },
        ],
        shared_vars: vec![],
        sync_primitives: vec![SyncPrimitive {
            id: "rw0".to_string(),
            kind: SyncKind::RwLock { poisonable: false },
            name: Some("data_rwlock".to_string()),
        }],
        properties: vec![Property::DeadlockFreedom],
        assumptions: Assumptions {
            thread_bound: 3,
            ..Assumptions::default()
        },
        source_map: SourceMap::default(),
    }
}

/// Build a model with 2 writers on the same RwLock.
/// Writers serialize correctly; no deadlock with a single lock.
fn two_writers_model() -> ConcurrentModel {
    ConcurrentModel {
        processes: vec![
            // Writer 1 (main)
            Process {
                id: "main".to_string(),
                kind: ProcessKind::Main,
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "s0".to_string(),
                        to: "s1".to_string(),
                        kind: TransitionKind::WriteLock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "s1".to_string(),
                        to: "done_main".to_string(),
                        kind: TransitionKind::WriteUnlock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "s0".to_string(),
                terminal_states: vec!["done_main".to_string()],
            },
            // Writer 2
            Process {
                id: "w2".to_string(),
                kind: ProcessKind::Spawned {
                    parent: "main".to_string(),
                    join_handle_in_parent: None,
                },
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "u0".to_string(),
                        to: "u1".to_string(),
                        kind: TransitionKind::WriteLock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "u1".to_string(),
                        to: "done_w2".to_string(),
                        kind: TransitionKind::WriteUnlock {
                            rwlock: "rw0".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "u0".to_string(),
                terminal_states: vec!["done_w2".to_string()],
            },
        ],
        shared_vars: vec![],
        sync_primitives: vec![SyncPrimitive {
            id: "rw0".to_string(),
            kind: SyncKind::RwLock { poisonable: false },
            name: Some("data_rwlock".to_string()),
        }],
        properties: vec![Property::DeadlockFreedom],
        assumptions: Assumptions {
            thread_bound: 2,
            ..Assumptions::default()
        },
        source_map: SourceMap::default(),
    }
}

#[test]
fn test_rwlock_concurrent_readers_no_deadlock() {
    let model = concurrent_readers_model();
    let result =
        check_concurrent_model(&model, &CheckOptions::default()).expect("check should not error");

    assert_eq!(
        result.report.status,
        VerificationStatus::AllPropertiesHold,
        "concurrent readers should not deadlock, got: {:?}",
        result.report.status
    );
    assert!(result.report.counterexample.is_none());
    assert_eq!(result.assumptions.thread_bound, 3);
}

#[test]
fn test_rwlock_reader_writer_interleaving_no_deadlock() {
    let model = reader_writer_interleaving_model();
    let result =
        check_concurrent_model(&model, &CheckOptions::default()).expect("check should not error");

    assert_eq!(
        result.report.status,
        VerificationStatus::AllPropertiesHold,
        "reader-writer interleaving should not deadlock, got: {:?}",
        result.report.status
    );
    assert!(result.report.counterexample.is_none());
    assert_eq!(result.assumptions.thread_bound, 3);
}

#[test]
fn test_rwlock_two_writers_serialized_no_deadlock() {
    let model = two_writers_model();
    let result =
        check_concurrent_model(&model, &CheckOptions::default()).expect("check should not error");

    assert_eq!(
        result.report.status,
        VerificationStatus::AllPropertiesHold,
        "two serialized writers should not deadlock, got: {:?}",
        result.report.status
    );
    assert!(result.report.counterexample.is_none());
    assert_eq!(result.assumptions.thread_bound, 2);
}
