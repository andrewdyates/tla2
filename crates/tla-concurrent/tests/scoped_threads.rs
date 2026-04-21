// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for scoped thread patterns: `thread::scope` with
//! `Scope::spawn`, verifying deadlock freedom when scoped threads coordinate
//! through shared synchronization primitives.

#![cfg(feature = "check")]

use tla_concurrent::*;

/// Build a model where main spawns two scoped threads that each acquire and
/// release a mutex. Main waits at a ScopeEnd transition for all scoped
/// children to terminate, then proceeds to its terminal state.
///
/// Scoped threads use `ProcessKind::Scoped` with a shared `scope_id`.
/// The main process uses `TransitionKind::ScopeEnd` to represent the
/// scope exit point.
fn scoped_thread_basic_model() -> ConcurrentModel {
    ConcurrentModel {
        processes: vec![
            // Main process: enters scope, waits for scope end, then done
            Process {
                id: "main".to_string(),
                kind: ProcessKind::Main,
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "s0".to_string(),
                        to: "s1".to_string(),
                        kind: TransitionKind::ScopeEnd {
                            scope_id: "scope0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "s1".to_string(),
                        to: "done_main".to_string(),
                        kind: TransitionKind::Internal {
                            label: Some("after_scope".to_string()),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "s0".to_string(),
                terminal_states: vec!["done_main".to_string()],
            },
            // Scoped thread 1: lock mutex, unlock mutex, done
            Process {
                id: "t1".to_string(),
                kind: ProcessKind::Scoped {
                    scope_id: "scope0".to_string(),
                    borrowed_captures: vec![],
                },
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "u0".to_string(),
                        to: "u1".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "u1".to_string(),
                        to: "done_t1".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "u0".to_string(),
                terminal_states: vec!["done_t1".to_string()],
            },
            // Scoped thread 2: lock mutex, unlock mutex, done
            Process {
                id: "t2".to_string(),
                kind: ProcessKind::Scoped {
                    scope_id: "scope0".to_string(),
                    borrowed_captures: vec![],
                },
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "v0".to_string(),
                        to: "v1".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "v1".to_string(),
                        to: "done_t2".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m".to_string(),
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
            id: "m".to_string(),
            kind: SyncKind::Mutex {
                reentrant: false,
                poisonable: true,
            },
            name: Some("shared_mutex".to_string()),
        }],
        properties: vec![Property::DeadlockFreedom],
        assumptions: Assumptions {
            thread_bound: 3,
            ..Assumptions::default()
        },
        source_map: SourceMap::default(),
    }
}

#[test]
fn test_scoped_thread_basic_no_deadlock() {
    let model = scoped_thread_basic_model();
    let result = check_concurrent_model(&model, &CheckOptions::default())
        .expect("check should not error");

    assert_eq!(
        result.report.status,
        VerificationStatus::AllPropertiesHold,
        "scoped threads with mutex should not deadlock, got: {:?}",
        result.report.status
    );
    assert!(result.report.counterexample.is_none());
    assert_eq!(result.assumptions.thread_bound, 3);
}
