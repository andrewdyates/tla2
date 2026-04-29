// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end integration tests: ConcurrentModel → TLA+ Module → tla-check.

#![cfg(feature = "check")]

use tla_concurrent::*;

/// Build a simple correct mutex model: 2 threads, 1 mutex, no deadlock.
fn correct_mutex_model() -> ConcurrentModel {
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
                        kind: TransitionKind::Lock {
                            mutex: "m".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "s1".to_string(),
                        to: "done_main".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "s0".to_string(),
                terminal_states: vec!["done_main".to_string()],
            },
            Process {
                id: "t0".to_string(),
                kind: ProcessKind::Spawned {
                    parent: "main".to_string(),
                    join_handle_in_parent: None,
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
                        to: "done_t0".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "u0".to_string(),
                terminal_states: vec!["done_t0".to_string()],
            },
        ],
        shared_vars: vec![],
        sync_primitives: vec![SyncPrimitive {
            id: "m".to_string(),
            kind: SyncKind::Mutex {
                reentrant: false,
                poisonable: true,
            },
            name: Some("data_mutex".to_string()),
        }],
        properties: vec![Property::DeadlockFreedom],
        assumptions: Assumptions {
            thread_bound: 2,
            ..Assumptions::default()
        },
        source_map: SourceMap::default(),
    }
}

/// Build an ABBA deadlock model: 2 threads, 2 mutexes, opposite lock order.
fn abba_deadlock_model() -> ConcurrentModel {
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
                        kind: TransitionKind::Lock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: Some(0),
                    },
                    Transition {
                        from: "s1".to_string(),
                        to: "s2".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: Some(1),
                    },
                    Transition {
                        from: "s2".to_string(),
                        to: "s3".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "s3".to_string(),
                        to: "done_main".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "s0".to_string(),
                terminal_states: vec!["done_main".to_string()],
            },
            Process {
                id: "t0".to_string(),
                kind: ProcessKind::Spawned {
                    parent: "main".to_string(),
                    join_handle_in_parent: None,
                },
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "u0".to_string(),
                        to: "u1".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: Some(2),
                    },
                    Transition {
                        from: "u1".to_string(),
                        to: "u2".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: Some(3),
                    },
                    Transition {
                        from: "u2".to_string(),
                        to: "u3".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "u3".to_string(),
                        to: "done_t0".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "u0".to_string(),
                terminal_states: vec!["done_t0".to_string()],
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
        source_map: SourceMap {
            entries: vec![
                SourceMapEntry {
                    from_state: "s0".to_string(),
                    to_state: "s1".to_string(),
                    process: "main".to_string(),
                    transition_tag: "Lock_mutex_a".to_string(),
                    rust_file: "src/main.rs".to_string(),
                    rust_line: 10,
                    rust_col: 5,
                    rust_end_line: 10,
                    rust_end_col: 18,
                },
                SourceMapEntry {
                    from_state: "s1".to_string(),
                    to_state: "s2".to_string(),
                    process: "main".to_string(),
                    transition_tag: "Lock_mutex_b".to_string(),
                    rust_file: "src/main.rs".to_string(),
                    rust_line: 11,
                    rust_col: 5,
                    rust_end_line: 11,
                    rust_end_col: 18,
                },
                SourceMapEntry {
                    from_state: "u0".to_string(),
                    to_state: "u1".to_string(),
                    process: "t0".to_string(),
                    transition_tag: "Lock_mutex_b".to_string(),
                    rust_file: "src/main.rs".to_string(),
                    rust_line: 20,
                    rust_col: 9,
                    rust_end_line: 20,
                    rust_end_col: 22,
                },
                SourceMapEntry {
                    from_state: "u1".to_string(),
                    to_state: "u2".to_string(),
                    process: "t0".to_string(),
                    transition_tag: "Lock_mutex_a".to_string(),
                    rust_file: "src/main.rs".to_string(),
                    rust_line: 21,
                    rust_col: 9,
                    rust_end_line: 21,
                    rust_end_col: 22,
                },
            ],
        },
    }
}

#[test]
fn correct_mutex_no_deadlock() {
    let model = correct_mutex_model();
    let result =
        check_concurrent_model(&model, &CheckOptions::default()).expect("check should not error");

    assert_eq!(
        result.report.status,
        tla_concurrent::VerificationStatus::AllPropertiesHold,
        "correct mutex pattern should have no deadlock"
    );
    assert!(result.report.counterexample.is_none());
    assert_eq!(result.assumptions.thread_bound, 2);
}

#[test]
fn abba_deadlock_detected() {
    let model = abba_deadlock_model();
    let result =
        check_concurrent_model(&model, &CheckOptions::default()).expect("check should not error");

    // The ABBA pattern causes a deadlock: main holds m1, waits for m2;
    // t0 holds m2, waits for m1. The checker should detect this.
    assert!(
        matches!(
            result.report.status,
            tla_concurrent::VerificationStatus::DeadlockDetected
        ),
        "ABBA pattern should deadlock, got: {:?}",
        result.report.status
    );

    let counterexample = result
        .report
        .counterexample
        .expect("deadlock report should include a mapped counterexample");
    // Trace includes initial state + action steps (typically 3 for ABBA: init + 2 locks)
    assert!(
        counterexample.steps.len() >= 2,
        "deadlock trace should have at least 2 steps, got {}",
        counterexample.steps.len()
    );
    // Non-initial steps (action transitions) should have Rust source locations
    // when the source_map has entries for those transitions. The initial state
    // may have rust_location: None.
    assert!(
        counterexample
            .steps
            .iter()
            .any(|step| step.rust_location.is_some()),
        "at least some mapped deadlock steps should have Rust source locations"
    );
    assert!(
        counterexample
            .steps
            .iter()
            .all(|step| !step.process.is_empty() && !step.transition_tag.is_empty()),
        "mapped steps should preserve process and transition information"
    );

    let rendered = counterexample.format_human_readable();
    assert!(rendered.contains("Step 1:"));
    assert!(rendered.contains("src/main.rs:"));
}

/// Build an ABBA deadlock model with source map entries for trace mapping.
fn abba_deadlock_model_with_source_map() -> ConcurrentModel {
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
                        kind: TransitionKind::Lock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: Some(0),
                    },
                    Transition {
                        from: "s1".to_string(),
                        to: "s2".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: Some(1),
                    },
                    Transition {
                        from: "s2".to_string(),
                        to: "s3".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "s3".to_string(),
                        to: "done_main".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "s0".to_string(),
                terminal_states: vec!["done_main".to_string()],
            },
            Process {
                id: "t0".to_string(),
                kind: ProcessKind::Spawned {
                    parent: "main".to_string(),
                    join_handle_in_parent: None,
                },
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "u0".to_string(),
                        to: "u1".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: Some(2),
                    },
                    Transition {
                        from: "u1".to_string(),
                        to: "u2".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: Some(3),
                    },
                    Transition {
                        from: "u2".to_string(),
                        to: "u3".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "u3".to_string(),
                        to: "done_t0".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "u0".to_string(),
                terminal_states: vec!["done_t0".to_string()],
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
        source_map: SourceMap {
            entries: vec![
                SourceMapEntry {
                    from_state: "s0".to_string(),
                    to_state: "s1".to_string(),
                    process: "main".to_string(),
                    transition_tag: "Lock_m1".to_string(),
                    rust_file: "src/main.rs".to_string(),
                    rust_line: 10,
                    rust_col: 5,
                    rust_end_line: 10,
                    rust_end_col: 30,
                },
                SourceMapEntry {
                    from_state: "s1".to_string(),
                    to_state: "s2".to_string(),
                    process: "main".to_string(),
                    transition_tag: "Lock_m2".to_string(),
                    rust_file: "src/main.rs".to_string(),
                    rust_line: 11,
                    rust_col: 5,
                    rust_end_line: 11,
                    rust_end_col: 30,
                },
                SourceMapEntry {
                    from_state: "u0".to_string(),
                    to_state: "u1".to_string(),
                    process: "t0".to_string(),
                    transition_tag: "Lock_m2".to_string(),
                    rust_file: "src/main.rs".to_string(),
                    rust_line: 20,
                    rust_col: 9,
                    rust_end_line: 20,
                    rust_end_col: 34,
                },
                SourceMapEntry {
                    from_state: "u1".to_string(),
                    to_state: "u2".to_string(),
                    process: "t0".to_string(),
                    transition_tag: "Lock_m1".to_string(),
                    rust_file: "src/main.rs".to_string(),
                    rust_line: 21,
                    rust_col: 9,
                    rust_end_line: 21,
                    rust_end_col: 34,
                },
            ],
        },
    }
}

#[test]
fn abba_deadlock_trace_has_source_mapped_steps() {
    let model = abba_deadlock_model_with_source_map();
    let result =
        check_concurrent_model(&model, &CheckOptions::default()).expect("check should not error");

    assert_eq!(
        result.report.status,
        tla_concurrent::VerificationStatus::DeadlockDetected,
        "ABBA pattern should deadlock, got: {:?}",
        result.report.status
    );

    // The counterexample trace must be populated.
    let trace = result
        .report
        .counterexample
        .as_ref()
        .expect("deadlock should have a counterexample trace");

    // The trace should have at least 2 steps (initial + at least one action).
    assert!(
        trace.steps.len() >= 2,
        "expected at least 2 steps in deadlock trace, got {}",
        trace.steps.len()
    );

    // At least one step should have a source-mapped Rust location.
    let mapped_count = trace
        .steps
        .iter()
        .filter(|s| s.rust_location.is_some())
        .count();
    assert!(
        mapped_count > 0,
        "expected at least one source-mapped step in the trace, got 0"
    );

    // Verify that source-mapped steps reference src/main.rs.
    for step in &trace.steps {
        if let Some(loc) = &step.rust_location {
            assert_eq!(
                loc.file, "src/main.rs",
                "source-mapped step should reference src/main.rs"
            );
            assert!(loc.line > 0, "source line should be > 0");
        }
    }

    // Each step should have a non-empty state snapshot.
    for step in &trace.steps {
        assert!(
            !step.state_snapshot.is_empty(),
            "each trace step should have state variables"
        );
    }
}

#[test]
fn json_output_includes_assumptions() {
    let model = correct_mutex_model();
    let result =
        check_concurrent_model(&model, &CheckOptions::default()).expect("check should not error");

    let json = serde_json::to_string_pretty(&result).expect("serialize");
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("parse");

    assert!(parsed["assumptions"].is_object());
    assert_eq!(parsed["assumptions"]["thread_bound"], 2);
    assert_eq!(
        parsed["assumptions"]["memory_model"],
        "SequentialConsistency"
    );
    assert_eq!(parsed["assumptions"]["panic_strategy"], "Unwind");
}
