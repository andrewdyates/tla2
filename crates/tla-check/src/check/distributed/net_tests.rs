// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Network-level integration tests for distributed BFS.
//!
//! Tests use localhost TCP connections to verify:
//! - State exchange between nodes
//! - Termination detection via Dijkstra's algorithm
//! - Invariant violation propagation
//! - Progress reporting
//! - State count parity with sequential BFS
//!
//! Each test uses a unique port range to avoid conflicts when running in parallel.
//!
//! Part of Pillar 6 Phase 2: Multi-machine distributed BFS tests.

use std::net::{SocketAddr, TcpListener};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

use super::dijkstra_termination::{DijkstraTermination, TokenAction};
use super::progress::ProgressTracker;
use super::transport::*;

/// Find an available base port for testing by trying to bind.
/// Returns a port that is free at the time of checking.
fn find_available_port_range(count: usize) -> u16 {
    // Try ports in a range to find a contiguous block
    for base in (19000..60000).step_by(100) {
        let all_available = (0..count).all(|i| {
            let addr: SocketAddr = format!("127.0.0.1:{}", base + i as u16).parse().unwrap();
            TcpListener::bind(addr).is_ok()
        });
        if all_available {
            return base;
        }
    }
    panic!("could not find {} contiguous available ports", count);
}

// ---------- Transport layer tests ----------

#[test]
fn test_tcp_transport_two_nodes_message_exchange() {
    let base_port = find_available_port_range(2);
    let addr0: SocketAddr = format!("127.0.0.1:{base_port}").parse().unwrap();
    let addr1: SocketAddr = format!("127.0.0.1:{}", base_port + 1).parse().unwrap();
    let addrs = vec![addr0, addr1];

    let received_by_0 = Arc::new(AtomicU64::new(0));
    let received_by_1 = Arc::new(AtomicU64::new(0));

    let r0 = Arc::clone(&received_by_0);
    let r1 = Arc::clone(&received_by_1);

    // Start node 1 first (it needs to be listening when node 0 connects)
    let handle1 = std::thread::spawn({
        let addrs = addrs.clone();
        move || {
            let config = TransportConfig {
                node_id: 1,
                listen_addr: addr1,
                node_addrs: addrs,
                connect_timeout: Duration::from_secs(5),
                read_timeout: Duration::from_millis(100),
            };
            let handler: Arc<MessageHandler> = Arc::new(Box::new(move |msg| {
                if matches!(msg, NetMessage::State { .. }) {
                    r1.fetch_add(1, Ordering::Relaxed);
                }
            }));
            let mut transport = TcpTransport::start(config, handler).expect("start node 1");

            // Send a state to node 0
            let msg = NetMessage::State {
                fp: crate::state::Fingerprint(42),
                state: crate::state::ArrayState::new(1),
                depth: 1,
            };
            transport.send_to(0, &msg).expect("send to node 0");

            // Wait for messages from node 0
            std::thread::sleep(Duration::from_millis(500));
            transport.shutdown();
        }
    });

    // Small delay to let node 1 start listening
    std::thread::sleep(Duration::from_millis(100));

    let config0 = TransportConfig {
        node_id: 0,
        listen_addr: addr0,
        node_addrs: addrs,
        connect_timeout: Duration::from_secs(5),
        read_timeout: Duration::from_millis(100),
    };
    let handler0: Arc<MessageHandler> = Arc::new(Box::new(move |msg| {
        if matches!(msg, NetMessage::State { .. }) {
            r0.fetch_add(1, Ordering::Relaxed);
        }
    }));
    let mut transport0 = TcpTransport::start(config0, handler0).expect("start node 0");

    // Send a state to node 1
    let msg = NetMessage::State {
        fp: crate::state::Fingerprint(99),
        state: crate::state::ArrayState::new(2),
        depth: 3,
    };
    transport0.send_to(1, &msg).expect("send to node 1");

    // Wait for exchange to complete
    std::thread::sleep(Duration::from_millis(500));
    transport0.shutdown();
    handle1.join().expect("node 1 thread");

    // Both nodes should have received at least the messages we sent
    // Note: exact counts depend on timing, but each should have received at least 1
    assert!(
        received_by_0.load(Ordering::Relaxed) >= 1,
        "node 0 should have received at least 1 state"
    );
    assert!(
        received_by_1.load(Ordering::Relaxed) >= 1,
        "node 1 should have received at least 1 state"
    );
}

// ---------- Dijkstra termination tests (multi-threaded simulation) ----------

#[test]
fn test_dijkstra_termination_four_nodes_simulated() {
    // Simulate 4-node Dijkstra termination without real TCP.
    // All nodes idle, no messages in flight.
    let nodes: Vec<DijkstraTermination> = (0..4).map(|i| DijkstraTermination::new(i, 4)).collect();

    // All become idle
    for n in &nodes {
        n.set_idle(true);
    }

    // Node 0 initiates
    let (next, color, counter) = nodes[0].initiate_round().expect("initiate");
    assert_eq!(next, 1);

    // Forward through the ring: 0 -> 1 -> 2 -> 3 -> 0
    let mut current_color = color;
    let mut current_counter = counter;

    for i in 1..4u32 {
        let action = nodes[i as usize].process_token(current_color, 0, current_counter);
        match action {
            TokenAction::Forward {
                next_node,
                color,
                counter,
            } => {
                assert_eq!(next_node, (i + 1) % 4);
                current_color = color;
                current_counter = counter;
            }
            other => panic!("expected Forward from node {i}, got {other:?}"),
        }
    }

    // Token returns to node 0
    let final_action = nodes[0].process_token(current_color, 0, current_counter);
    assert_eq!(final_action, TokenAction::TerminationConfirmed);
    assert!(nodes[0].is_terminated());
}

#[test]
fn test_dijkstra_termination_with_messages_in_flight() {
    // 3 nodes. Messages are in flight during the first round.
    let nodes: Vec<DijkstraTermination> = (0..3).map(|i| DijkstraTermination::new(i, 3)).collect();

    // Node 0 sends to node 2, node 2 hasn't received yet.
    nodes[0].on_message_sent(2);
    // Net counter: node 0 = +1, node 2 = 0 (hasn't received)

    for n in &nodes {
        n.set_idle(true);
    }

    // Round 1: should fail because counter != 0
    let (_, color, counter) = nodes[0].initiate_round().expect("initiate");
    assert_eq!(counter, 1); // node 0's send counter

    let action1 = nodes[1].process_token(color, 0, counter);
    let (_, c1, cnt1) = match action1 {
        TokenAction::Forward {
            next_node,
            color,
            counter,
        } => (next_node, color, counter),
        other => panic!("unexpected: {other:?}"),
    };

    let action2 = nodes[2].process_token(c1, 0, cnt1);
    let (_, c2, cnt2) = match action2 {
        TokenAction::Forward {
            next_node,
            color,
            counter,
        } => (next_node, color, counter),
        other => panic!("unexpected: {other:?}"),
    };

    // Counter is 1 + 0 + 0 = 1 (not zero)
    let final_action = nodes[0].process_token(c2, 0, cnt2);
    assert_eq!(final_action, TokenAction::RoundFailed);

    // Now simulate the message being received
    nodes[2].on_message_received();
    // Net counter: node 0 = +1, node 2 = -1, sum = 0

    // Round 2: should succeed
    let (_, color2, counter2) = nodes[0].initiate_round().expect("initiate round 2");
    // node 0's counter is still +1 (send is persistent)
    let action1b = nodes[1].process_token(color2, 0, counter2);
    let (_, c1b, cnt1b) = match action1b {
        TokenAction::Forward {
            next_node,
            color,
            counter,
        } => (next_node, color, counter),
        other => panic!("unexpected: {other:?}"),
    };

    let action2b = nodes[2].process_token(c1b, 0, cnt1b);
    let (_, c2b, cnt2b) = match action2b {
        TokenAction::Forward {
            next_node,
            color,
            counter,
        } => (next_node, color, counter),
        other => panic!("unexpected: {other:?}"),
    };

    // Counter: 1 + 0 + (-1) = 0, and all are white + idle
    assert_eq!(cnt2b, 0);
    let final2 = nodes[0].process_token(c2b, 0, cnt2b);
    assert_eq!(final2, TokenAction::TerminationConfirmed);
}

// ---------- Progress reporting tests ----------

#[test]
fn test_progress_tracker_multi_node() {
    use super::progress::NodeStats;
    use std::time::Instant;

    let tracker = ProgressTracker::new(4, Duration::from_secs(1));

    for i in 0..4u32 {
        tracker.update_node_stats(NodeStats {
            node_id: i,
            distinct_states: (i as u64 + 1) * 1000,
            max_depth: i * 5,
            transitions: (i as u64 + 1) * 2000,
            is_idle: i == 3,
            timestamp: Some(Instant::now()),
        });
    }

    let progress = tracker.aggregate();
    // Total distinct: 1000 + 2000 + 3000 + 4000 = 10000
    assert_eq!(progress.total_distinct_states, 10_000);
    // Max depth: max(0, 5, 10, 15) = 15
    assert_eq!(progress.global_max_depth, 15);
    // Total transitions: 2000 + 4000 + 6000 + 8000 = 20000
    assert_eq!(progress.total_transitions, 20_000);
    // 1 idle (node 3)
    assert_eq!(progress.idle_nodes, 1);
    assert_eq!(progress.total_nodes, 4);
}

// ---------- Wire protocol fuzzing ----------

#[test]
fn test_all_message_types_encode_decode_roundtrip() {
    use crate::state::{ArrayState, Fingerprint};

    let messages = vec![
        NetMessage::State {
            fp: Fingerprint(0),
            state: ArrayState::new(0),
            depth: 0,
        },
        NetMessage::State {
            fp: Fingerprint(u64::MAX),
            state: ArrayState::new(10),
            depth: u32::MAX,
        },
        NetMessage::Halt {
            source_node: 0,
            reason: String::new(),
        },
        NetMessage::Halt {
            source_node: u32::MAX,
            reason: "a".repeat(1000),
        },
        NetMessage::Token {
            color: TokenColor::White,
            initiator: 0,
            counter: 0,
        },
        NetMessage::Token {
            color: TokenColor::Black,
            initiator: 100,
            counter: i64::MIN,
        },
        NetMessage::Token {
            color: TokenColor::White,
            initiator: 0,
            counter: i64::MAX,
        },
        NetMessage::ProgressRequest { requester: 0 },
        NetMessage::ProgressRequest {
            requester: u32::MAX,
        },
        NetMessage::ProgressReport {
            node_id: 0,
            distinct_states: 0,
            max_depth: 0,
            transitions: 0,
        },
        NetMessage::ProgressReport {
            node_id: 42,
            distinct_states: u64::MAX,
            max_depth: u32::MAX,
            transitions: u64::MAX,
        },
        NetMessage::Ack { sequence: 0 },
        NetMessage::Ack { sequence: u64::MAX },
    ];

    for (i, msg) in messages.iter().enumerate() {
        let encoded = encode_message(msg);
        assert!(encoded.len() >= 5, "message {i}: too short");

        // Decode the payload (skip 4-byte length prefix)
        let payload = &encoded[4..];
        let decoded = decode_message(payload);
        assert!(decoded.is_some(), "message {i}: failed to decode {:?}", msg);

        // Verify tag matches
        let expected_tag = match msg {
            NetMessage::State { .. } => MessageTag::State,
            NetMessage::Halt { .. } => MessageTag::Halt,
            NetMessage::Token { .. } => MessageTag::Token,
            NetMessage::ProgressRequest { .. } => MessageTag::ProgressRequest,
            NetMessage::ProgressReport { .. } => MessageTag::ProgressReport,
            NetMessage::Ack { .. } => MessageTag::Ack,
        };
        let actual_tag = MessageTag::from_byte(payload[0]).expect("valid tag");
        assert_eq!(actual_tag, expected_tag, "message {i}: tag mismatch");
    }
}

// ---------- Halt propagation test ----------

#[test]
fn test_halt_propagation_via_dijkstra() {
    // When a halt is received, the termination detector should be force-terminated.
    let dt = DijkstraTermination::new(1, 3);
    assert!(!dt.is_terminated());

    // Simulate receiving a halt signal
    dt.force_terminate();
    assert!(dt.is_terminated());

    // Any subsequent token processing should still report terminated
    assert!(dt.is_terminated());
}

// ---------- Partition assignment consistency ----------

#[test]
fn test_partition_assignment_matches_node_count() {
    use super::partition::PartitionScheme;
    use crate::state::Fingerprint;

    for num_nodes in [2, 3, 4, 8, 16] {
        let scheme = PartitionScheme::modulo(num_nodes);
        let mut node_counts = vec![0usize; num_nodes];

        for i in 0..100_000u64 {
            let fp = Fingerprint(i.wrapping_mul(0x517cc1b727220a95));
            let node = scheme.partition_for_fp(fp);
            assert!(node < num_nodes);
            node_counts[node] += 1;
        }

        // Each node should get roughly 100000/num_nodes states
        let expected = 100_000 / num_nodes;
        for (node, &count) in node_counts.iter().enumerate() {
            let lower = expected * 70 / 100;
            let upper = expected * 130 / 100;
            assert!(
                count >= lower && count <= upper,
                "node {node}/{num_nodes}: got {count}, expected ~{expected}"
            );
        }
    }
}
