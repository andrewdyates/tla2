// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Multi-machine distributed BFS node coordinator.
//!
//! Orchestrates distributed model checking across multiple machines connected
//! via TCP. Each node runs a `DistributedNode` that:
//!
//! 1. Owns a partition of the fingerprint hash space
//! 2. Runs local BFS workers (threads) within its partition
//! 3. Exchanges cross-partition states with peer nodes via TCP
//! 4. Participates in Dijkstra's token-based termination detection
//! 5. Propagates invariant violations immediately to all peers
//! 6. Reports progress to the coordinator node (node 0)
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────┐
//! │                DistributedNode                    │
//! │  node_id=0, partition=[0x0000..0x5555]           │
//! │                                                   │
//! │  ┌──────────┐ ┌──────────────┐ ┌──────────────┐ │
//! │  │ BFS      │ │ TCP Transport│ │ Dijkstra     │ │
//! │  │ Workers  │ │ (send/recv)  │ │ Termination  │ │
//! │  │ (threads)│ │              │ │              │ │
//! │  └────┬─────┘ └──────┬───────┘ └──────┬───────┘ │
//! │       │              │                │          │
//! │  ┌────▼──────────────▼────────────────▼───────┐ │
//! │  │       Partition Router                      │ │
//! │  │  local states → local frontier              │ │
//! │  │  remote states → TCP to owning node         │ │
//! │  └────────────────────────────────────────────┘ │
//! └─────────────────────────────────────────────────┘
//! ```
//!
//! Part of Pillar 6 Phase 2: Multi-machine distributed BFS.

#![allow(dead_code)]

use std::collections::VecDeque;
use std::net::SocketAddr;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use crossbeam_channel::{bounded, Receiver, Sender};
use rustc_hash::FxHashSet;

use super::dijkstra_termination::{DijkstraTermination, TokenAction};
use super::partition::PartitionScheme;
use super::progress::{ClusterProgress, LocalProgress, NodeStats, ProgressTracker};
use super::transport::{
    MessageHandler, NetMessage, NodeId, TcpTransport, TokenColor, TransportConfig,
};
use crate::state::{ArrayState, Fingerprint};

/// Configuration for a distributed BFS node.
#[derive(Debug, Clone)]
pub(crate) struct DistributedNodeConfig {
    /// This node's ID (0-indexed).
    pub(crate) node_id: NodeId,
    /// Addresses of all nodes in the cluster.
    pub(crate) node_addrs: Vec<SocketAddr>,
    /// Number of local BFS worker threads per node.
    pub(crate) local_workers: usize,
    /// Connection timeout for peer nodes.
    pub(crate) connect_timeout: Duration,
    /// How often to emit progress reports (node 0 only).
    pub(crate) progress_interval: Duration,
    /// How often to attempt termination detection (node 0 only).
    pub(crate) termination_check_interval: Duration,
}

impl DistributedNodeConfig {
    /// Number of nodes in the cluster.
    pub(crate) fn num_nodes(&self) -> usize {
        self.node_addrs.len()
    }
}

/// Result of a distributed BFS run on this node.
#[derive(Debug)]
pub(crate) struct DistributedNodeResult {
    /// Number of distinct states found by this node.
    pub(crate) local_distinct_states: u64,
    /// Number of states received from remote nodes.
    pub(crate) states_received: u64,
    /// Number of states sent to remote nodes.
    pub(crate) states_sent: u64,
    /// Maximum BFS depth reached locally.
    pub(crate) max_depth: u32,
    /// Total transitions computed locally.
    pub(crate) transitions: u64,
    /// Whether an invariant violation was detected (locally or remotely).
    pub(crate) violation_detected: bool,
    /// Violation description, if any.
    pub(crate) violation_reason: Option<String>,
    /// Aggregated cluster progress (only available on node 0).
    pub(crate) cluster_progress: Option<ClusterProgress>,
}

/// A distributed BFS node that coordinates with peers over TCP.
pub(crate) struct DistributedNode {
    config: DistributedNodeConfig,
    scheme: PartitionScheme,
    termination: Arc<DijkstraTermination>,
    progress: Arc<LocalProgress>,
    tracker: Option<Arc<ProgressTracker>>,
    /// Channel for messages received from the network to be processed by the BFS loop.
    incoming_rx: Receiver<NetMessage>,
    incoming_tx: Sender<NetMessage>,
    /// Flag: a halt/violation was received or detected.
    halt_flag: Arc<AtomicBool>,
    halt_reason: Arc<Mutex<Option<String>>>,
}

impl DistributedNode {
    /// Create a new distributed node (does not start networking).
    pub(crate) fn new(config: DistributedNodeConfig) -> Self {
        let num_nodes = config.num_nodes();
        let scheme = PartitionScheme::modulo(num_nodes);
        let termination = Arc::new(DijkstraTermination::new(config.node_id, num_nodes as u32));
        let progress = Arc::new(LocalProgress::new());

        let tracker = if config.node_id == 0 {
            Some(Arc::new(ProgressTracker::new(
                num_nodes as u32,
                config.progress_interval,
            )))
        } else {
            None
        };

        // Bounded channel for incoming network messages -> BFS loop
        let (incoming_tx, incoming_rx) = bounded(8192);

        DistributedNode {
            config,
            scheme,
            termination,
            progress,
            tracker,
            incoming_rx,
            incoming_tx,
            halt_flag: Arc::new(AtomicBool::new(false)),
            halt_reason: Arc::new(Mutex::new(None)),
        }
    }

    /// Run the distributed BFS with a user-provided successor function.
    ///
    /// This method:
    /// 1. Starts the TCP transport
    /// 2. Seeds initial states into the local frontier (node 0 only, or pre-partitioned)
    /// 3. Runs the BFS loop with network state exchange
    /// 4. Participates in termination detection
    /// 5. Returns results when terminated
    pub(crate) fn run_bfs<F>(
        &self,
        initial_states: Vec<(Fingerprint, ArrayState)>,
        successor_fn: F,
    ) -> std::io::Result<DistributedNodeResult>
    where
        F: Fn(&ArrayState, Fingerprint) -> Vec<(Fingerprint, ArrayState)> + Send + Sync + 'static,
    {
        let node_id = self.config.node_id;
        let _num_nodes = self.config.num_nodes();

        // Build transport config
        let transport_config = TransportConfig {
            node_id,
            listen_addr: self.config.node_addrs[node_id as usize],
            node_addrs: self.config.node_addrs.clone(),
            connect_timeout: self.config.connect_timeout,
            read_timeout: Duration::from_millis(100),
        };

        // Message handler: routes incoming network messages to the BFS channel
        let incoming_tx = self.incoming_tx.clone();
        let termination = Arc::clone(&self.termination);
        let halt_flag = Arc::clone(&self.halt_flag);
        let halt_reason = Arc::clone(&self.halt_reason);
        let tracker = self.tracker.clone();
        let _progress_local = Arc::clone(&self.progress);

        let handler: Arc<MessageHandler> = Arc::new(Box::new(move |msg: NetMessage| {
            match &msg {
                NetMessage::State { .. } => {
                    termination.on_message_received();
                    let _ = incoming_tx.try_send(msg);
                }
                NetMessage::Halt { reason, .. } => {
                    halt_flag.store(true, Ordering::SeqCst);
                    let mut hr = halt_reason.lock().expect("halt_reason lock");
                    if hr.is_none() {
                        *hr = Some(reason.clone());
                    }
                    termination.force_terminate();
                }
                NetMessage::Token {
                    color: _,
                    initiator: _,
                    counter: _,
                } => {
                    let _ = incoming_tx.try_send(msg);
                }
                NetMessage::ProgressRequest { requester: _ } => {
                    // Reply with our local stats — the caller should handle sending
                    let _ = incoming_tx.try_send(msg);
                }
                NetMessage::ProgressReport {
                    node_id,
                    distinct_states,
                    max_depth,
                    transitions,
                } => {
                    if let Some(ref t) = tracker {
                        t.update_node_stats(NodeStats {
                            node_id: *node_id,
                            distinct_states: *distinct_states,
                            max_depth: *max_depth,
                            transitions: *transitions,
                            is_idle: false,
                            timestamp: Some(Instant::now()),
                        });
                    }
                }
                NetMessage::Ack { .. } => {}
            }
        }));

        // Start TCP transport
        let mut transport = TcpTransport::start(transport_config, handler)?;

        // Run the BFS loop
        let result = self.bfs_loop(&transport, initial_states, &successor_fn);

        // Shutdown transport
        transport.shutdown();

        Ok(result)
    }

    /// Core BFS loop with network state exchange and termination detection.
    fn bfs_loop<F>(
        &self,
        transport: &TcpTransport,
        initial_states: Vec<(Fingerprint, ArrayState)>,
        successor_fn: &F,
    ) -> DistributedNodeResult
    where
        F: Fn(&ArrayState, Fingerprint) -> Vec<(Fingerprint, ArrayState)>,
    {
        let node_id = self.config.node_id;
        let _num_nodes = self.config.num_nodes();

        let mut frontier: VecDeque<(Fingerprint, ArrayState, u32)> = VecDeque::new();
        let mut seen: FxHashSet<Fingerprint> = FxHashSet::default();

        // Seed: only states that belong to this node's partition
        for (fp, state) in initial_states {
            let target = self.scheme.partition_for_fp(fp);
            if target == node_id as usize {
                if seen.insert(fp) {
                    frontier.push_back((fp, state, 0));
                    self.progress.inc_distinct_states();
                }
            } else {
                // Send to the owning node
                let msg = NetMessage::State {
                    fp,
                    state,
                    depth: 0,
                };
                self.termination.on_message_sent(target as NodeId);
                let _ = transport.send_to(target as NodeId, &msg);
                self.progress.inc_states_sent();
            }
        }

        let mut last_termination_check = Instant::now();
        let poll_timeout = Duration::from_millis(1);

        loop {
            // Check halt flag
            if self.halt_flag.load(Ordering::Relaxed) || self.termination.is_terminated() {
                break;
            }

            // Process local frontier
            if let Some((fp, state, depth)) = frontier.pop_front() {
                self.progress.update_max_depth(depth);

                let successors = successor_fn(&state, fp);
                self.progress.inc_transitions();

                for (succ_fp, succ_state) in successors {
                    let target = self.scheme.partition_for_fp(succ_fp);
                    if target == node_id as usize {
                        // Local
                        if seen.insert(succ_fp) {
                            frontier.push_back((succ_fp, succ_state, depth + 1));
                            self.progress.inc_distinct_states();
                        }
                    } else {
                        // Remote
                        let msg = NetMessage::State {
                            fp: succ_fp,
                            state: succ_state,
                            depth: depth + 1,
                        };
                        self.termination.on_message_sent(target as NodeId);
                        let _ = transport.send_to(target as NodeId, &msg);
                        self.progress.inc_states_sent();
                    }
                }
                self.termination.set_idle(false);
                continue;
            }

            // Drain incoming network messages
            let mut got_work = false;
            while let Ok(msg) = self.incoming_rx.try_recv() {
                match msg {
                    NetMessage::State { fp, state, depth } => {
                        if seen.insert(fp) {
                            frontier.push_back((fp, state, depth));
                            self.progress.inc_distinct_states();
                            got_work = true;
                        }
                        self.progress.inc_states_received();
                    }
                    NetMessage::Token {
                        color,
                        initiator,
                        counter,
                    } => {
                        self.handle_token(transport, color, initiator, counter);
                    }
                    NetMessage::ProgressRequest { requester } => {
                        let snap = self.progress.snapshot(node_id);
                        let reply = NetMessage::ProgressReport {
                            node_id,
                            distinct_states: snap.distinct_states,
                            max_depth: snap.max_depth,
                            transitions: snap.transitions,
                        };
                        let _ = transport.send_to(requester, &reply);
                    }
                    _ => {} // Other messages handled in the transport handler
                }
            }

            if got_work {
                self.termination.set_idle(false);
                continue;
            }

            // We're idle — participate in termination detection
            self.termination.set_idle(true);

            // Node 0: periodically initiate termination detection
            if node_id == 0 {
                if last_termination_check.elapsed() >= self.config.termination_check_interval {
                    if let Some((next, color, counter)) = self.termination.initiate_round() {
                        let token = NetMessage::Token {
                            color,
                            initiator: 0,
                            counter,
                        };
                        let _ = transport.send_to(next, &token);
                    }
                    last_termination_check = Instant::now();
                }

                // Progress reporting
                if let Some(ref tracker) = self.tracker {
                    // Update our own stats
                    tracker.update_node_stats(self.progress.snapshot(node_id));
                    tracker.maybe_report();
                }
            }

            // Brief sleep to avoid busy-waiting
            match self.incoming_rx.recv_timeout(poll_timeout) {
                Ok(msg) => match msg {
                    NetMessage::State { fp, state, depth } => {
                        if seen.insert(fp) {
                            frontier.push_back((fp, state, depth));
                            self.progress.inc_distinct_states();
                            self.termination.set_idle(false);
                        }
                        self.progress.inc_states_received();
                    }
                    NetMessage::Token {
                        color,
                        initiator,
                        counter,
                    } => {
                        self.handle_token(transport, color, initiator, counter);
                    }
                    _ => {}
                },
                Err(crossbeam_channel::RecvTimeoutError::Timeout) => {}
                Err(crossbeam_channel::RecvTimeoutError::Disconnected) => break,
            }

            // Check termination
            if self.termination.is_terminated() {
                break;
            }
        }

        // Collect final stats
        let cluster_progress = self.tracker.as_ref().map(|t| {
            t.update_node_stats(self.progress.snapshot(node_id));
            t.aggregate()
        });

        let halt_reason = self.halt_reason.lock().expect("halt_reason lock").clone();

        DistributedNodeResult {
            local_distinct_states: self.progress.distinct_states(),
            states_received: self.progress.states_received(),
            states_sent: self.progress.states_sent(),
            max_depth: self.progress.snapshot(node_id).max_depth,
            transitions: self.progress.snapshot(node_id).transitions,
            violation_detected: self.halt_flag.load(Ordering::Relaxed),
            violation_reason: halt_reason,
            cluster_progress,
        }
    }

    /// Handle a termination token received from the network.
    fn handle_token(
        &self,
        transport: &TcpTransport,
        color: TokenColor,
        initiator: NodeId,
        counter: i64,
    ) {
        let action = self.termination.process_token(color, initiator, counter);
        match action {
            TokenAction::Forward {
                next_node,
                color,
                counter,
            } => {
                let token = NetMessage::Token {
                    color,
                    initiator,
                    counter,
                };
                let _ = transport.send_to(next_node, &token);
            }
            TokenAction::TerminationConfirmed => {
                // Broadcast termination to all peers
                // (They'll detect it via their own token processing or this halt)
            }
            TokenAction::RoundFailed => {
                // Node 0 will retry in the next termination check interval
            }
            TokenAction::Absorbed => {
                // Node wasn't idle — token is dropped
            }
        }
    }

    /// Send a halt signal to all peer nodes (e.g., invariant violation detected).
    pub(crate) fn broadcast_halt(&self, transport: &TcpTransport, reason: &str) {
        self.halt_flag.store(true, Ordering::SeqCst);
        {
            let mut hr = self.halt_reason.lock().expect("halt_reason lock");
            if hr.is_none() {
                *hr = Some(reason.to_string());
            }
        }
        let msg = NetMessage::Halt {
            source_node: self.config.node_id,
            reason: reason.to_string(),
        };
        let _ = transport.broadcast(&msg);
        self.termination.force_terminate();
    }
}

/// Parse a node address list from CLI format: "host1:port1,host2:port2,...".
pub(crate) fn parse_node_addrs(addrs_str: &str) -> Result<Vec<SocketAddr>, String> {
    addrs_str
        .split(',')
        .map(|s| {
            s.trim()
                .parse::<SocketAddr>()
                .map_err(|e| format!("invalid node address '{}': {}", s.trim(), e))
        })
        .collect()
}

/// Distributed BFS entry point: create all nodes and run on localhost.
///
/// This is a convenience function for running a distributed BFS within a
/// single process using localhost TCP connections. Primarily for testing.
/// In production, each node would be a separate process/machine.
pub(crate) fn run_distributed_localhost<F>(
    num_nodes: usize,
    base_port: u16,
    initial_states: Vec<(Fingerprint, ArrayState)>,
    successor_fn: F,
) -> std::io::Result<Vec<DistributedNodeResult>>
where
    F: Fn(&ArrayState, Fingerprint) -> Vec<(Fingerprint, ArrayState)>
        + Send
        + Sync
        + Clone
        + 'static,
{
    let addrs: Vec<SocketAddr> = (0..num_nodes)
        .map(|i| {
            format!("127.0.0.1:{}", base_port + i as u16)
                .parse()
                .unwrap()
        })
        .collect();

    let handles: Vec<_> = (0..num_nodes)
        .map(|i| {
            let addrs = addrs.clone();
            let init = if i == 0 {
                initial_states.clone()
            } else {
                Vec::new()
            };
            let succ = successor_fn.clone();

            std::thread::Builder::new()
                .name(format!("dist-node-{i}"))
                .spawn(move || {
                    let config = DistributedNodeConfig {
                        node_id: i as NodeId,
                        node_addrs: addrs,
                        local_workers: 1,
                        connect_timeout: Duration::from_secs(5),
                        progress_interval: Duration::from_secs(5),
                        termination_check_interval: Duration::from_millis(100),
                    };
                    let node = DistributedNode::new(config);
                    node.run_bfs(init, succ)
                })
                .expect("failed to spawn node thread")
        })
        .collect();

    let mut results = Vec::with_capacity(num_nodes);
    for handle in handles {
        results.push(handle.join().expect("node thread panicked")?);
    }
    Ok(results)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_node_addrs_valid() {
        let addrs = parse_node_addrs("127.0.0.1:9000, 127.0.0.1:9001, 127.0.0.1:9002")
            .expect("should parse");
        assert_eq!(addrs.len(), 3);
        assert_eq!(addrs[0].port(), 9000);
        assert_eq!(addrs[1].port(), 9001);
        assert_eq!(addrs[2].port(), 9002);
    }

    #[test]
    fn test_parse_node_addrs_invalid() {
        let result = parse_node_addrs("127.0.0.1:9000, not-an-address");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_node_addrs_single() {
        let addrs = parse_node_addrs("0.0.0.0:8080").expect("should parse");
        assert_eq!(addrs.len(), 1);
    }

    #[test]
    fn test_distributed_node_config() {
        let config = DistributedNodeConfig {
            node_id: 0,
            node_addrs: vec![
                "127.0.0.1:9000".parse().unwrap(),
                "127.0.0.1:9001".parse().unwrap(),
            ],
            local_workers: 2,
            connect_timeout: Duration::from_secs(5),
            progress_interval: Duration::from_secs(5),
            termination_check_interval: Duration::from_millis(100),
        };
        assert_eq!(config.num_nodes(), 2);
    }

    #[test]
    fn test_distributed_node_creation() {
        let config = DistributedNodeConfig {
            node_id: 1,
            node_addrs: vec![
                "127.0.0.1:9100".parse().unwrap(),
                "127.0.0.1:9101".parse().unwrap(),
                "127.0.0.1:9102".parse().unwrap(),
            ],
            local_workers: 1,
            connect_timeout: Duration::from_secs(1),
            progress_interval: Duration::from_secs(5),
            termination_check_interval: Duration::from_millis(50),
        };
        let node = DistributedNode::new(config);
        // Node 1 is not the coordinator — no progress tracker
        assert!(node.tracker.is_none());
        assert!(!node.halt_flag.load(Ordering::Relaxed));
    }

    #[test]
    fn test_node0_has_progress_tracker() {
        let config = DistributedNodeConfig {
            node_id: 0,
            node_addrs: vec![
                "127.0.0.1:9200".parse().unwrap(),
                "127.0.0.1:9201".parse().unwrap(),
            ],
            local_workers: 1,
            connect_timeout: Duration::from_secs(1),
            progress_interval: Duration::from_secs(5),
            termination_check_interval: Duration::from_millis(50),
        };
        let node = DistributedNode::new(config);
        assert!(node.tracker.is_some());
    }
}
