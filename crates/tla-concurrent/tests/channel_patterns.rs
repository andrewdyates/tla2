// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Channel-based producer-consumer integration tests.
//!
//! Tests ChannelSend, ChannelRecv, ChannelRecvDisconnected, SenderDrop,
//! ReceiverDrop, and ChannelSendErr transition kinds through the full
//! ConcurrentModel -> TLA+ -> tla-check pipeline.

#![cfg(feature = "check")]

use tla_concurrent::*;

/// Build a correct producer-consumer model with N=2 messages.
///
/// Main process (producer): sends 2 messages, drops sender, done.
///   States: send_0 -> send_1 -> send_2 -> drop_sender -> done_main
///   Transitions: ChannelSend x2, SenderDrop, Internal
///
/// Worker process (consumer): receives 2 messages, gets disconnected, done.
///   States: recv_0 -> recv_1 -> recv_2 -> disconnected -> done_worker
///   Transitions: ChannelRecv x2, ChannelRecvDisconnected, Internal
fn producer_consumer_model() -> ConcurrentModel {
    ConcurrentModel {
        processes: vec![
            Process {
                id: "main".to_string(),
                kind: ProcessKind::Main,
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "send_0".to_string(),
                        to: "send_1".to_string(),
                        kind: TransitionKind::ChannelSend {
                            channel: "ch0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "send_1".to_string(),
                        to: "send_2".to_string(),
                        kind: TransitionKind::ChannelSend {
                            channel: "ch0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "send_2".to_string(),
                        to: "drop_sender".to_string(),
                        kind: TransitionKind::SenderDrop {
                            channel: "ch0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "drop_sender".to_string(),
                        to: "done_main".to_string(),
                        kind: TransitionKind::Internal { label: None },
                        source_map_index: None,
                    },
                ],
                initial_state: "send_0".to_string(),
                terminal_states: vec!["done_main".to_string()],
            },
            Process {
                id: "worker".to_string(),
                kind: ProcessKind::Spawned {
                    parent: "main".to_string(),
                    join_handle_in_parent: None,
                },
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "recv_0".to_string(),
                        to: "recv_1".to_string(),
                        kind: TransitionKind::ChannelRecv {
                            channel: "ch0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "recv_1".to_string(),
                        to: "recv_2".to_string(),
                        kind: TransitionKind::ChannelRecv {
                            channel: "ch0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "recv_2".to_string(),
                        to: "disconnected".to_string(),
                        kind: TransitionKind::ChannelRecvDisconnected {
                            channel: "ch0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "disconnected".to_string(),
                        to: "done_worker".to_string(),
                        kind: TransitionKind::Internal { label: None },
                        source_map_index: None,
                    },
                ],
                initial_state: "recv_0".to_string(),
                terminal_states: vec!["done_worker".to_string()],
            },
        ],
        shared_vars: vec![],
        sync_primitives: vec![SyncPrimitive {
            id: "ch0".to_string(),
            kind: SyncKind::Channel {
                kind: ChannelKind::Mpsc,
                capacity: None,
            },
            name: Some("work_channel".to_string()),
        }],
        properties: vec![Property::DeadlockFreedom],
        assumptions: Assumptions {
            thread_bound: 2,
            ..Assumptions::default()
        },
        source_map: SourceMap::default(),
    }
}

/// Build a model where the receiver drops before consuming all messages.
///
/// Main process (producer): sends messages in a loop. At each step it either
///   sends successfully (if receiver alive) or gets SendErr (if receiver dropped).
///   States: send_0 -> send_1 (via ChannelSend or ChannelSendErr)
///           send_1 -> done_main (via SenderDrop + Internal)
///           send_0 -> send_err (via ChannelSendErr) -> done_main
///
/// Worker process (consumer): receives 1 message, drops receiver, done.
///   States: recv_0 -> recv_1 -> drop_recv -> done_worker
///   Transitions: ChannelRecv x1, ReceiverDrop, Internal
///
/// The key property: even when the receiver drops early, the sender eventually
/// detects it via ChannelSendErr and terminates. No deadlock.
fn receiver_drop_model() -> ConcurrentModel {
    ConcurrentModel {
        processes: vec![
            Process {
                id: "main".to_string(),
                kind: ProcessKind::Main,
                local_vars: vec![],
                transitions: vec![
                    // send_0: try to send - succeeds if receiver alive
                    Transition {
                        from: "send_0".to_string(),
                        to: "send_1".to_string(),
                        kind: TransitionKind::ChannelSend {
                            channel: "ch0".to_string(),
                        },
                        source_map_index: None,
                    },
                    // send_0: try to send - fails if receiver dropped
                    Transition {
                        from: "send_0".to_string(),
                        to: "send_err".to_string(),
                        kind: TransitionKind::ChannelSendErr {
                            channel: "ch0".to_string(),
                        },
                        source_map_index: None,
                    },
                    // send_1: drop sender and finish (happy path)
                    Transition {
                        from: "send_1".to_string(),
                        to: "drop_sender".to_string(),
                        kind: TransitionKind::SenderDrop {
                            channel: "ch0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "drop_sender".to_string(),
                        to: "done_main".to_string(),
                        kind: TransitionKind::Internal { label: None },
                        source_map_index: None,
                    },
                    // send_err: handle error and finish
                    Transition {
                        from: "send_err".to_string(),
                        to: "done_main".to_string(),
                        kind: TransitionKind::Internal { label: None },
                        source_map_index: None,
                    },
                ],
                initial_state: "send_0".to_string(),
                terminal_states: vec!["done_main".to_string()],
            },
            Process {
                id: "worker".to_string(),
                kind: ProcessKind::Spawned {
                    parent: "main".to_string(),
                    join_handle_in_parent: None,
                },
                local_vars: vec![],
                transitions: vec![
                    Transition {
                        from: "recv_0".to_string(),
                        to: "recv_1".to_string(),
                        kind: TransitionKind::ChannelRecv {
                            channel: "ch0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "recv_1".to_string(),
                        to: "drop_recv".to_string(),
                        kind: TransitionKind::ReceiverDrop {
                            channel: "ch0".to_string(),
                        },
                        source_map_index: None,
                    },
                    Transition {
                        from: "drop_recv".to_string(),
                        to: "done_worker".to_string(),
                        kind: TransitionKind::Internal { label: None },
                        source_map_index: None,
                    },
                ],
                initial_state: "recv_0".to_string(),
                terminal_states: vec!["done_worker".to_string()],
            },
        ],
        shared_vars: vec![],
        sync_primitives: vec![SyncPrimitive {
            id: "ch0".to_string(),
            kind: SyncKind::Channel {
                kind: ChannelKind::Mpsc,
                capacity: None,
            },
            name: Some("work_channel".to_string()),
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
fn test_producer_consumer_no_deadlock() {
    let model = producer_consumer_model();
    let result = check_concurrent_model(&model, &CheckOptions::default())
        .expect("check should not error");

    assert_eq!(
        result.report.status,
        VerificationStatus::AllPropertiesHold,
        "correct producer-consumer pattern should have no deadlock, got: {:?}",
        result.report.status
    );
    assert!(result.report.counterexample.is_none());
    assert_eq!(result.assumptions.thread_bound, 2);
    assert!(result.report.stats.states_found > 0, "should explore states");
}

#[test]
fn test_receiver_drop_no_deadlock() {
    let model = receiver_drop_model();
    let result = check_concurrent_model(&model, &CheckOptions::default())
        .expect("check should not error");

    // Even with early receiver drop, the sender handles it via ChannelSendErr
    // so there should be no deadlock.
    assert_eq!(
        result.report.status,
        VerificationStatus::AllPropertiesHold,
        "receiver-drop pattern should not deadlock (sender handles SendErr), got: {:?}",
        result.report.status
    );
    assert!(result.report.counterexample.is_none());
}

#[test]
fn test_producer_consumer_json_roundtrip() {
    let model = producer_consumer_model();
    let result = check_concurrent_model(&model, &CheckOptions::default())
        .expect("check should not error");

    let json = serde_json::to_string_pretty(&result).expect("serialize");
    let parsed: serde_json::Value = serde_json::from_str(&json).expect("parse");

    assert!(parsed["report"]["stats"]["states_found"].is_number());
    assert_eq!(
        parsed["report"]["status"],
        "AllPropertiesHold"
    );
}
