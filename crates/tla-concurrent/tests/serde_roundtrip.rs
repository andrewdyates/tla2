// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Serde round-trip tests for ConcurrentModel IR types.

use tla_concurrent::*;

/// Build a minimal 2-process, 1-mutex ABBA deadlock model.
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
                id: "thread_0".to_string(),
                kind: ProcessKind::Spawned {
                    parent: "main".to_string(),
                    join_handle_in_parent: None,
                },
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "t0".to_string(),
                        to: "t1".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: Some(2),
                    },
                    Transition {
                        from: "t1".to_string(),
                        to: "t2".to_string(),
                        kind: TransitionKind::Lock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: Some(3),
                    },
                    Transition {
                        from: "t2".to_string(),
                        to: "t3".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m1".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "t3".to_string(),
                        to: "done_thread_0".to_string(),
                        kind: TransitionKind::Unlock {
                            mutex: "m2".to_string(),
                        },
                        source_map_index: None,
                    },
                ],
                initial_state: "t0".to_string(),
                terminal_states: vec!["done_thread_0".to_string()],
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
        properties: vec![Property::DeadlockFreedom, Property::LockOrderConsistency],
        assumptions: Assumptions {
            thread_bound: 2,
            data_abstraction: DataAbstraction::Concrete,
            fairness_mode: FairnessMode::None,
            memory_model: MemoryModel::SequentialConsistency,
            reductions: vec![],
            unmodeled_primitives: vec![],
            interprocedural_depth: 3,
            panic_strategy: PanicStrategy::Unwind,
            recursion_bound: None,
            heap_bound: None,
            dynamic_dispatch: DynDispatchResolution::FullyResolved,
            opaque_externals: vec![],
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
                    from_state: "t0".to_string(),
                    to_state: "t1".to_string(),
                    process: "thread_0".to_string(),
                    transition_tag: "Lock_m2".to_string(),
                    rust_file: "src/main.rs".to_string(),
                    rust_line: 20,
                    rust_col: 9,
                    rust_end_line: 20,
                    rust_end_col: 34,
                },
                SourceMapEntry {
                    from_state: "t1".to_string(),
                    to_state: "t2".to_string(),
                    process: "thread_0".to_string(),
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
fn serde_roundtrip_concurrent_model() {
    let model = abba_deadlock_model();
    let json = serde_json::to_string_pretty(&model).expect("serialize");
    let deserialized: ConcurrentModel = serde_json::from_str(&json).expect("deserialize");

    assert_eq!(deserialized.processes.len(), 2);
    assert_eq!(deserialized.sync_primitives.len(), 2);
    assert_eq!(deserialized.properties.len(), 2);
    assert_eq!(deserialized.assumptions.thread_bound, 2);
    assert_eq!(deserialized.source_map.entries.len(), 4);
    assert_eq!(deserialized.processes[0].id, "main");
    assert_eq!(deserialized.processes[1].id, "thread_0");
    assert_eq!(deserialized.processes[0].transitions.len(), 4);
    assert_eq!(deserialized.processes[1].transitions.len(), 4);
}

#[test]
fn generate_tla_module_from_abba_model() {
    let model = abba_deadlock_model();
    let module = tla_concurrent::generate::generate_tla_module(&model);

    assert_eq!(module.name.node, "ConcurrentSpec");
    assert_eq!(module.extends.len(), 3);
    assert_eq!(module.extends[0].node, "Naturals");
    assert_eq!(module.extends[1].node, "Sequences");
    assert_eq!(module.extends[2].node, "FiniteSets");

    // Should have: 1 VARIABLE decl + helper ops + Init + 8 actions + Next + 2 properties
    assert!(
        module.units.len() > 10,
        "expected >10 units, got {}",
        module.units.len()
    );

    // Check variable declaration exists
    let has_vars = module
        .units
        .iter()
        .any(|u| matches!(&u.node, tla_core::ast::Unit::Variable(_)));
    assert!(has_vars, "should have VARIABLE declaration");

    // Check Init and Next operators exist
    let op_names: Vec<String> = module
        .units
        .iter()
        .filter_map(|u| match &u.node {
            tla_core::ast::Unit::Operator(op) => Some(op.name.node.clone()),
            _ => None,
        })
        .collect();

    assert!(
        op_names.contains(&"Init".to_string()),
        "missing Init operator"
    );
    assert!(
        op_names.contains(&"Next".to_string()),
        "missing Next operator"
    );
    assert!(
        op_names.contains(&"Processes".to_string()),
        "missing Processes helper"
    );
    assert!(
        op_names.contains(&"TerminalStates".to_string()),
        "missing TerminalStates helper"
    );
    assert!(
        op_names.contains(&"NoOwner".to_string()),
        "missing NoOwner helper"
    );
    assert!(
        op_names.contains(&"Mutexes".to_string()),
        "missing Mutexes helper"
    );
    assert!(
        op_names.contains(&"DeadlockFreedom".to_string()),
        "missing DeadlockFreedom property"
    );
    assert!(
        op_names.contains(&"LockOrderConsistency".to_string()),
        "missing LockOrderConsistency property"
    );

    // Check action operators for both processes
    assert!(
        op_names.iter().any(|n| n.starts_with("Action_main_")),
        "missing main process actions"
    );
    assert!(
        op_names.iter().any(|n| n.starts_with("Action_thread_0_")),
        "missing thread_0 process actions"
    );
}

#[test]
fn source_map_lookup() {
    let model = abba_deadlock_model();
    let entry = model.source_map.find_by_action_label("Lock_m1");
    assert!(entry.is_some());
    let entry = entry.unwrap();
    assert_eq!(entry.process, "main");
    assert_eq!(entry.rust_file, "src/main.rs");
    assert_eq!(entry.rust_line, 10);

    let thread_entries = model.source_map.entries_for_process("thread_0");
    assert_eq!(thread_entries.len(), 2);
}

#[test]
fn property_classification() {
    assert!(Property::DeadlockFreedom.is_default());
    assert!(Property::DeadlockFreedom.is_safety());
    assert!(Property::LockOrderConsistency.is_default());
    assert!(Property::DataRaceFreedom.is_default());

    assert!(!Property::JoinCompleteness.is_default());
    assert!(!Property::CondvarProgress {
        condvar: "cv0".to_string()
    }
    .is_default());

    let term = Property::Termination {
        process: "main".to_string(),
    };
    assert!(term.is_default());
    assert!(!term.is_safety()); // Termination is a liveness property
}

#[test]
fn assumptions_default() {
    let a = Assumptions::default();
    assert_eq!(a.thread_bound, 0);
    assert_eq!(a.memory_model, MemoryModel::SequentialConsistency);
    assert_eq!(a.fairness_mode, FairnessMode::None);
    assert_eq!(a.panic_strategy, PanicStrategy::Unwind);
    assert_eq!(a.dynamic_dispatch, DynDispatchResolution::FullyResolved);
    assert!(a.opaque_externals.is_empty());
}
