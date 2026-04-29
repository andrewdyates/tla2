// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Distributed model checking — state partitioning prototype.
//!
//! Provides the building blocks for distributing BFS state exploration across
//! multiple independent checker processes (or machines). The core idea:
//!
//! 1. Each state fingerprint is deterministically mapped to a **partition** via
//!    `fp % num_partitions`.
//! 2. Each worker owns exactly one partition and is the sole authority for
//!    deduplicating and expanding states in that partition.
//! 3. When a worker discovers a successor state whose fingerprint maps to a
//!    different partition, it forwards the state via a message channel.
//! 4. **Dijkstra-Scholten termination detection** determines when the global
//!    BFS frontier is exhausted without a central coordinator polling workers.
//!
//! This module uses `crossbeam_channel` for local (single-process) simulation
//! of the inter-partition message passing. A future network transport can
//! replace the channels without changing the partitioning or termination logic.
//!
//! Part of #3796.

use crate::state::Fingerprint;
use crossbeam_channel::{Receiver, Sender};
use std::sync::atomic::{AtomicBool, AtomicI64, Ordering};
use std::sync::Arc;

// ---------------------------------------------------------------------------
// State partitioning
// ---------------------------------------------------------------------------

/// Maps fingerprints to partition IDs using modular hashing.
///
/// The partition function is deterministic and stateless: any worker can
/// compute the owner of a fingerprint without communication.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct StatePartitioner {
    num_partitions: u32,
}

impl StatePartitioner {
    /// Create a partitioner for `num_partitions` partitions.
    ///
    /// # Panics
    ///
    /// Panics if `num_partitions` is zero.
    #[must_use]
    pub(crate) fn new(num_partitions: u32) -> Self {
        assert!(num_partitions > 0, "num_partitions must be > 0");
        Self { num_partitions }
    }

    /// Return the partition ID that owns the given fingerprint.
    #[inline]
    #[must_use]
    pub(crate) fn partition_of(&self, fp: Fingerprint) -> u32 {
        (fp.0 % u64::from(self.num_partitions)) as u32
    }

    /// Number of partitions.
    #[must_use]
    pub(crate) fn num_partitions(&self) -> u32 {
        self.num_partitions
    }
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for a single worker in a distributed BFS run.
#[derive(Debug, Clone)]
pub(crate) struct DistributedBfsConfig {
    /// Total number of partitions (workers) in the distributed run.
    pub(crate) num_partitions: u32,
    /// Zero-based ID of this worker's partition.
    pub(crate) worker_id: u32,
}

impl DistributedBfsConfig {
    /// Create a new config. Panics if `worker_id >= num_partitions` or
    /// `num_partitions == 0`.
    #[must_use]
    pub(crate) fn new(num_partitions: u32, worker_id: u32) -> Self {
        assert!(num_partitions > 0, "num_partitions must be > 0");
        assert!(
            worker_id < num_partitions,
            "worker_id ({worker_id}) must be < num_partitions ({num_partitions})"
        );
        Self {
            num_partitions,
            worker_id,
        }
    }

    /// Build a [`StatePartitioner`] from this config.
    #[must_use]
    pub(crate) fn partitioner(&self) -> StatePartitioner {
        StatePartitioner::new(self.num_partitions)
    }
}

// ---------------------------------------------------------------------------
// Message types
// ---------------------------------------------------------------------------

/// A state forwarded from one partition to another.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StateMessage {
    /// Fingerprint of the forwarded state.
    pub(crate) fingerprint: Fingerprint,
    /// The partition that generated (sent) this state.
    pub(crate) source_partition: u32,
    /// BFS depth at which this state was discovered.
    pub(crate) depth: usize,
}

/// Termination token passed in a ring for Dijkstra-Scholten detection.
///
/// The token circulates through partitions `0 -> 1 -> ... -> N-1 -> 0`.
/// A worker that has sent more states than it has received is "active" and
/// taints the token black. When the token completes a full circuit and
/// arrives back at partition 0 while still white, all workers are idle and
/// BFS is complete.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TerminationToken {
    /// `false` = white (clean), `true` = black (tainted).
    pub(crate) is_black: bool,
    /// Running total of in-flight messages across all partitions visited.
    /// Termination requires this to be zero when the token returns to
    /// partition 0.
    pub(crate) pending_messages: i64,
}

impl TerminationToken {
    /// Create a fresh white token with zero pending messages.
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            is_black: false,
            pending_messages: 0,
        }
    }
}

impl Default for TerminationToken {
    fn default() -> Self {
        Self::new()
    }
}

/// Messages exchanged between partitions over the ring/mesh channels.
#[derive(Debug, Clone)]
pub(crate) enum DistributedMessage {
    /// A forwarded state that the receiving partition should explore.
    State(StateMessage),
    /// Termination detection token (ring protocol).
    Token(TerminationToken),
    /// Explicit shutdown signal — receiver should exit its event loop.
    Shutdown,
}

// ---------------------------------------------------------------------------
// Partitioned frontier
// ---------------------------------------------------------------------------

/// Routes discovered successor states to the correct partition's channel.
///
/// Each worker holds one `PartitionedFrontier` that contains send-halves for
/// every partition (including itself). Local states are returned directly via
/// the `local` buffer rather than sent through a channel, avoiding unnecessary
/// serialization overhead.
pub(crate) struct PartitionedFrontier {
    partitioner: StatePartitioner,
    /// This worker's partition ID.
    local_partition: u32,
    /// Send channels to each partition, indexed by partition ID.
    senders: Vec<Sender<DistributedMessage>>,
    /// Buffer for states that belong to this worker's own partition.
    local_buf: Vec<StateMessage>,
    /// Atomic counter: messages sent minus messages received.
    /// Part of Dijkstra-Scholten deficit tracking.
    deficit: Arc<AtomicI64>,
}

impl PartitionedFrontier {
    /// Create a new frontier for `local_partition`.
    ///
    /// `senders` must have exactly `partitioner.num_partitions()` entries.
    pub(crate) fn new(
        partitioner: StatePartitioner,
        local_partition: u32,
        senders: Vec<Sender<DistributedMessage>>,
        deficit: Arc<AtomicI64>,
    ) -> Self {
        assert_eq!(
            senders.len(),
            partitioner.num_partitions() as usize,
            "sender count must match partition count"
        );
        Self {
            partitioner,
            local_partition,
            senders,
            local_buf: Vec::new(),
            deficit,
        }
    }

    /// Route a successor state to the correct partition.
    ///
    /// If the state belongs to this worker, it is buffered locally.
    /// Otherwise it is sent to the owning partition's channel and the
    /// deficit counter is incremented.
    pub(crate) fn route(&mut self, msg: StateMessage) {
        let target = self.partitioner.partition_of(msg.fingerprint);
        if target == self.local_partition {
            self.local_buf.push(msg);
        } else {
            // Increment deficit BEFORE sending so that the token always
            // sees a conservative (over-) count of in-flight messages.
            self.deficit.fetch_add(1, Ordering::SeqCst);
            // Channel send can only fail if the receiver is dropped (shutdown).
            let _ = self.senders[target as usize].send(DistributedMessage::State(msg));
        }
    }

    /// Drain locally-buffered states. The caller processes these without
    /// channel overhead.
    pub(crate) fn drain_local(&mut self) -> Vec<StateMessage> {
        std::mem::take(&mut self.local_buf)
    }

    /// Send a termination token to the next partition in the ring.
    pub(crate) fn forward_token(&self, token: TerminationToken) {
        let next = (self.local_partition + 1) % self.partitioner.num_partitions();
        let _ = self.senders[next as usize].send(DistributedMessage::Token(token));
    }
}

// ---------------------------------------------------------------------------
// Dijkstra-Scholten termination detection
// ---------------------------------------------------------------------------

/// Per-worker termination state for the Dijkstra-Scholten ring protocol.
///
/// Each worker tracks its own deficit (messages sent - messages received) and
/// whether it has been active since the last token pass. The ring circulates
/// a [`TerminationToken`]; when it returns to partition 0 still white and with
/// `pending_messages == 0`, global termination is declared.
pub(crate) struct TerminationDetector {
    /// This worker's partition ID.
    partition_id: u32,
    /// Total partitions in the ring.
    num_partitions: u32,
    /// Per-worker deficit: messages sent minus messages received.
    deficit: Arc<AtomicI64>,
    /// Set to `true` when this worker has processed any state since the last
    /// token pass. Reset to `false` when the worker forwards the token.
    was_active: bool,
    /// Global termination flag shared with all workers.
    terminated: Arc<AtomicBool>,
}

impl TerminationDetector {
    /// Create a new detector for the given partition.
    pub(crate) fn new(
        partition_id: u32,
        num_partitions: u32,
        deficit: Arc<AtomicI64>,
        terminated: Arc<AtomicBool>,
    ) -> Self {
        Self {
            partition_id,
            num_partitions,
            deficit,
            was_active: false,
            terminated,
        }
    }

    /// Mark this worker as having done work (processed a state).
    pub(crate) fn mark_active(&mut self) {
        self.was_active = true;
    }

    /// Record that a message was received from another partition.
    pub(crate) fn on_message_received(&self) {
        self.deficit.fetch_sub(1, Ordering::SeqCst);
    }

    /// Process an incoming termination token and decide whether to declare
    /// global termination or forward the token to the next partition.
    ///
    /// Returns `true` if global termination has been declared.
    pub(crate) fn process_token(
        &mut self,
        mut token: TerminationToken,
        frontier: &PartitionedFrontier,
    ) -> bool {
        // Accumulate this worker's deficit into the token.
        let local_deficit = self.deficit.load(Ordering::SeqCst);
        token.pending_messages += local_deficit;

        // If this worker was active since the last pass, taint the token.
        if self.was_active {
            token.is_black = true;
            self.was_active = false;
        }

        if self.partition_id == 0 {
            // Token completed a full circuit back to the initiator.
            if !token.is_black && token.pending_messages == 0 {
                // All workers idle, no messages in flight => terminate.
                self.terminated.store(true, Ordering::SeqCst);
                return true;
            }
            // Not yet terminated — start a fresh round.
            frontier.forward_token(TerminationToken::new());
        } else {
            // Intermediate worker: forward the (possibly tainted) token.
            frontier.forward_token(token);
        }
        false
    }

    /// Check whether global termination has been declared.
    #[must_use]
    pub(crate) fn is_terminated(&self) -> bool {
        self.terminated.load(Ordering::SeqCst)
    }

    /// Number of partitions in the ring.
    #[must_use]
    pub(crate) fn num_partitions(&self) -> u32 {
        self.num_partitions
    }
}

// ---------------------------------------------------------------------------
// Channel mesh builder (local simulation)
// ---------------------------------------------------------------------------

/// Build a fully-connected mesh of crossbeam channels for `n` partitions.
///
/// Returns `(senders, receivers)` where `senders[i]` and `receivers[i]` are
/// the send/recv halves for partition `i`. Every partition gets one channel;
/// senders are cloned so that all partitions can send to all others.
pub(crate) fn build_channel_mesh(
    n: u32,
) -> (
    Vec<Vec<Sender<DistributedMessage>>>,
    Vec<Receiver<DistributedMessage>>,
) {
    let n = n as usize;
    let mut all_senders: Vec<Sender<DistributedMessage>> = Vec::with_capacity(n);
    let mut receivers: Vec<Receiver<DistributedMessage>> = Vec::with_capacity(n);

    for _ in 0..n {
        let (tx, rx) = crossbeam_channel::unbounded();
        all_senders.push(tx);
        receivers.push(rx);
    }

    // Each partition needs a clone of every partition's sender.
    let per_partition_senders: Vec<Vec<Sender<DistributedMessage>>> =
        (0..n).map(|_| all_senders.clone()).collect();

    (per_partition_senders, receivers)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- StatePartitioner ---------------------------------------------------

    #[test]
    fn test_partitioner_single_partition_always_zero() {
        let p = StatePartitioner::new(1);
        // Every fingerprint maps to partition 0.
        for i in 0..100 {
            assert_eq!(p.partition_of(Fingerprint(i)), 0);
        }
    }

    #[test]
    fn test_partitioner_modular_distribution() {
        let p = StatePartitioner::new(4);
        assert_eq!(p.partition_of(Fingerprint(0)), 0);
        assert_eq!(p.partition_of(Fingerprint(1)), 1);
        assert_eq!(p.partition_of(Fingerprint(2)), 2);
        assert_eq!(p.partition_of(Fingerprint(3)), 3);
        assert_eq!(p.partition_of(Fingerprint(4)), 0);
        assert_eq!(p.partition_of(Fingerprint(7)), 3);
        assert_eq!(p.partition_of(Fingerprint(100)), 0);
    }

    #[test]
    fn test_partitioner_deterministic() {
        let p = StatePartitioner::new(8);
        let fp = Fingerprint(0xDEAD_BEEF_CAFE_1234);
        let first = p.partition_of(fp);
        for _ in 0..100 {
            assert_eq!(p.partition_of(fp), first);
        }
    }

    #[test]
    #[should_panic(expected = "num_partitions must be > 0")]
    fn test_partitioner_zero_panics() {
        let _ = StatePartitioner::new(0);
    }

    // -- DistributedBfsConfig -----------------------------------------------

    #[test]
    fn test_config_valid() {
        let cfg = DistributedBfsConfig::new(4, 2);
        assert_eq!(cfg.num_partitions, 4);
        assert_eq!(cfg.worker_id, 2);
        let p = cfg.partitioner();
        assert_eq!(p.num_partitions(), 4);
    }

    #[test]
    #[should_panic(expected = "worker_id (4) must be < num_partitions (4)")]
    fn test_config_worker_id_out_of_range() {
        let _ = DistributedBfsConfig::new(4, 4);
    }

    // -- TerminationToken ---------------------------------------------------

    #[test]
    fn test_token_default_is_white() {
        let t = TerminationToken::new();
        assert!(!t.is_black);
        assert_eq!(t.pending_messages, 0);
    }

    // -- PartitionedFrontier routing ----------------------------------------

    #[test]
    fn test_frontier_routes_local_state_to_buffer() {
        let partitioner = StatePartitioner::new(2);
        let (senders, _receivers) = build_channel_mesh(2);
        let deficit = Arc::new(AtomicI64::new(0));
        let mut frontier =
            PartitionedFrontier::new(partitioner, 0, senders[0].clone(), deficit.clone());

        // Fingerprint 0 maps to partition 0 (local).
        frontier.route(StateMessage {
            fingerprint: Fingerprint(0),
            source_partition: 0,
            depth: 1,
        });

        let local = frontier.drain_local();
        assert_eq!(local.len(), 1);
        assert_eq!(local[0].fingerprint, Fingerprint(0));
        // No deficit change for local routing.
        assert_eq!(deficit.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn test_frontier_routes_remote_state_to_channel() {
        let partitioner = StatePartitioner::new(2);
        let (senders, receivers) = build_channel_mesh(2);
        let deficit = Arc::new(AtomicI64::new(0));
        let mut frontier =
            PartitionedFrontier::new(partitioner, 0, senders[0].clone(), deficit.clone());

        // Fingerprint 1 maps to partition 1 (remote).
        frontier.route(StateMessage {
            fingerprint: Fingerprint(1),
            source_partition: 0,
            depth: 1,
        });

        let local = frontier.drain_local();
        assert!(local.is_empty());
        assert_eq!(deficit.load(Ordering::SeqCst), 1);

        // The message should be on partition 1's channel.
        let msg = receivers[1].try_recv().unwrap();
        match msg {
            DistributedMessage::State(sm) => {
                assert_eq!(sm.fingerprint, Fingerprint(1));
                assert_eq!(sm.source_partition, 0);
            }
            other => panic!("expected State message, got {:?}", other),
        }
    }

    // -- Channel mesh -------------------------------------------------------

    #[test]
    fn test_channel_mesh_dimensions() {
        let (senders, receivers) = build_channel_mesh(3);
        assert_eq!(senders.len(), 3);
        assert_eq!(receivers.len(), 3);
        for s in &senders {
            assert_eq!(s.len(), 3);
        }
    }

    #[test]
    fn test_channel_mesh_cross_send() {
        let (senders, receivers) = build_channel_mesh(2);

        // Partition 0 sends to partition 1.
        senders[0][1]
            .send(DistributedMessage::State(StateMessage {
                fingerprint: Fingerprint(42),
                source_partition: 0,
                depth: 0,
            }))
            .unwrap();

        let msg = receivers[1].try_recv().unwrap();
        match msg {
            DistributedMessage::State(sm) => assert_eq!(sm.fingerprint, Fingerprint(42)),
            other => panic!("expected State, got {:?}", other),
        }
    }

    // -- Dijkstra-Scholten termination --------------------------------------

    #[test]
    fn test_termination_single_partition_immediate() {
        let terminated = Arc::new(AtomicBool::new(false));
        let deficit = Arc::new(AtomicI64::new(0));
        let partitioner = StatePartitioner::new(1);
        let (senders, _receivers) = build_channel_mesh(1);
        let frontier =
            PartitionedFrontier::new(partitioner, 0, senders[0].clone(), deficit.clone());
        let mut detector = TerminationDetector::new(0, 1, deficit, terminated.clone());

        // With a single idle partition, the first token should terminate.
        let token = TerminationToken::new();
        let done = detector.process_token(token, &frontier);
        assert!(done);
        assert!(detector.is_terminated());
        assert!(terminated.load(Ordering::SeqCst));
    }

    #[test]
    fn test_termination_active_worker_taints_token() {
        let terminated = Arc::new(AtomicBool::new(false));
        let deficit = Arc::new(AtomicI64::new(0));
        let partitioner = StatePartitioner::new(1);
        let (senders, _receivers) = build_channel_mesh(1);
        let frontier =
            PartitionedFrontier::new(partitioner, 0, senders[0].clone(), deficit.clone());
        let mut detector = TerminationDetector::new(0, 1, deficit, terminated.clone());

        detector.mark_active();

        let token = TerminationToken::new();
        let done = detector.process_token(token, &frontier);
        // Active worker taints token; partition 0 restarts the round.
        assert!(!done);
        assert!(!detector.is_terminated());

        // Second round with idle worker should terminate.
        let token = TerminationToken::new();
        let done = detector.process_token(token, &frontier);
        assert!(done);
    }

    #[test]
    fn test_termination_pending_messages_block_termination() {
        let terminated = Arc::new(AtomicBool::new(false));
        let deficit = Arc::new(AtomicI64::new(1)); // 1 message in flight
        let partitioner = StatePartitioner::new(1);
        let (senders, _receivers) = build_channel_mesh(1);
        let frontier =
            PartitionedFrontier::new(partitioner, 0, senders[0].clone(), deficit.clone());
        let mut detector = TerminationDetector::new(0, 1, deficit.clone(), terminated.clone());

        let token = TerminationToken::new();
        let done = detector.process_token(token, &frontier);
        // pending_messages != 0 => no termination.
        assert!(!done);

        // Simulate message delivery (decrement deficit).
        deficit.fetch_sub(1, Ordering::SeqCst);

        let token = TerminationToken::new();
        let done = detector.process_token(token, &frontier);
        assert!(done);
    }

    /// End-to-end two-partition simulation: partition 0 discovers two states,
    /// one owned by partition 1. After forwarding and processing, the ring
    /// protocol detects termination.
    #[test]
    fn test_two_partition_e2e_termination() {
        let n: u32 = 2;
        let partitioner = StatePartitioner::new(n);
        let (senders, receivers) = build_channel_mesh(n);
        let terminated = Arc::new(AtomicBool::new(false));

        let deficit0 = Arc::new(AtomicI64::new(0));
        let deficit1 = Arc::new(AtomicI64::new(0));

        let mut frontier0 =
            PartitionedFrontier::new(partitioner, 0, senders[0].clone(), deficit0.clone());
        let frontier1 =
            PartitionedFrontier::new(partitioner, 1, senders[1].clone(), deficit1.clone());

        let mut det0 = TerminationDetector::new(0, n, deficit0.clone(), terminated.clone());
        let mut det1 = TerminationDetector::new(1, n, deficit1.clone(), terminated.clone());

        // Partition 0 discovers FP=0 (local) and FP=1 (remote -> partition 1).
        frontier0.route(StateMessage {
            fingerprint: Fingerprint(0),
            source_partition: 0,
            depth: 0,
        });
        frontier0.route(StateMessage {
            fingerprint: Fingerprint(1),
            source_partition: 0,
            depth: 0,
        });

        // Process local state on partition 0.
        let local0 = frontier0.drain_local();
        assert_eq!(local0.len(), 1);
        det0.mark_active();

        // Partition 1 receives the forwarded state.
        let msg = receivers[1].try_recv().unwrap();
        match msg {
            DistributedMessage::State(_) => {
                det1.on_message_received();
                det1.mark_active();
            }
            other => panic!("expected State, got {:?}", other),
        }

        // Both partitions are now idle. Start termination detection.
        // Partition 0 initiates by sending a fresh token to partition 1.
        frontier0.forward_token(TerminationToken::new());

        // Partition 1 receives the token.
        let token_msg = receivers[1].try_recv().unwrap();
        let token = match token_msg {
            DistributedMessage::Token(t) => t,
            other => panic!("expected Token, got {:?}", other),
        };

        // Partition 1 processes the token — it was active, so taints it.
        let done = det1.process_token(token, &frontier1);
        assert!(!done); // intermediate partition, never declares termination

        // Token arrives back at partition 0.
        let token_msg = receivers[0].try_recv().unwrap();
        let token = match token_msg {
            DistributedMessage::Token(t) => t,
            other => panic!("expected Token, got {:?}", other),
        };

        // Token is black (det1 was active) => partition 0 restarts.
        assert!(token.is_black);
        let done = det0.process_token(token, &frontier0);
        assert!(!done);

        // Second round: nobody is active, deficit is balanced (1 sent, 1 received).
        let token_msg = receivers[1].try_recv().unwrap();
        let token = match token_msg {
            DistributedMessage::Token(t) => t,
            other => panic!("expected Token, got {:?}", other),
        };
        assert!(!token.is_black); // fresh token from restart

        let done = det1.process_token(token, &frontier1);
        assert!(!done);

        let token_msg = receivers[0].try_recv().unwrap();
        let token = match token_msg {
            DistributedMessage::Token(t) => t,
            other => panic!("expected Token, got {:?}", other),
        };

        // deficit0 = +1 (sent one), deficit1 = -1 (received one).
        // Sum should be 0 and token should be white.
        assert!(!token.is_black);
        let done = det0.process_token(token, &frontier0);
        assert!(done);
        assert!(terminated.load(Ordering::SeqCst));
    }

    /// Verify that drain_local returns an empty vec when called twice
    /// without new routing.
    #[test]
    fn test_frontier_drain_local_idempotent() {
        let partitioner = StatePartitioner::new(1);
        let (senders, _receivers) = build_channel_mesh(1);
        let deficit = Arc::new(AtomicI64::new(0));
        let mut frontier = PartitionedFrontier::new(partitioner, 0, senders[0].clone(), deficit);

        frontier.route(StateMessage {
            fingerprint: Fingerprint(0),
            source_partition: 0,
            depth: 0,
        });

        let first = frontier.drain_local();
        assert_eq!(first.len(), 1);

        let second = frontier.drain_local();
        assert!(second.is_empty());
    }

    /// Verify partitioner covers all partitions for sequential fingerprints.
    #[test]
    fn test_partitioner_coverage() {
        let n = 7u32;
        let p = StatePartitioner::new(n);
        let mut seen = vec![false; n as usize];
        for i in 0..n {
            let part = p.partition_of(Fingerprint(u64::from(i)));
            seen[part as usize] = true;
        }
        assert!(seen.iter().all(|&s| s), "not all partitions were covered");
    }

    /// Test the Shutdown message variant is correctly transmitted.
    #[test]
    fn test_shutdown_message() {
        let (senders, receivers) = build_channel_mesh(2);
        senders[0][1].send(DistributedMessage::Shutdown).unwrap();

        let msg = receivers[1].try_recv().unwrap();
        assert!(matches!(msg, DistributedMessage::Shutdown));
    }
}
