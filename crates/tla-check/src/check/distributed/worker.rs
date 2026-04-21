// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(dead_code)]

//! Distributed BFS worker: owns one fingerprint partition, processes local
//! states, and routes non-local successors to the correct partition via
//! exchange channels.
//!
//! Each worker:
//! 1. Pops a state from its local frontier (or receives one via exchange channel)
//! 2. Generates all successors
//! 3. For each successor, computes its fingerprint and partition
//! 4. If the successor belongs to this partition: dedup + add to local frontier
//! 5. If the successor belongs to another partition: send via exchange channel
//!
//! This mirrors TLC's distributed model checking approach where each node
//! owns a slice of the fingerprint space.

use std::collections::VecDeque;

use crossbeam_channel::{Receiver, Sender, TryRecvError};
use rustc_hash::FxHashSet;

use super::partition::PartitionScheme;
use crate::state::{ArrayState, Fingerprint};

/// A state message sent between partitions via exchange channels.
///
/// Contains the pre-computed fingerprint (to avoid recomputation at the
/// receiver) and the full state needed for successor generation.
#[derive(Debug, Clone)]
pub(crate) struct StateMessage {
    /// Pre-computed fingerprint of the state.
    pub(crate) fp: Fingerprint,
    /// The full state data (array-indexed variable values).
    pub(crate) state: ArrayState,
    /// BFS depth of this state.
    pub(crate) depth: usize,
}

/// Per-partition exchange channel endpoints.
///
/// Each partition has one receiver (reads incoming states from all other
/// partitions) and N-1 senders (one to each other partition). The senders
/// are indexed by target partition ID.
pub(crate) struct PartitionChannels {
    /// Receive states routed to this partition by other workers.
    pub(crate) rx: Receiver<StateMessage>,
    /// Send states to partition `i`. `senders[own_id]` is unused but present
    /// for index simplicity (sending to self goes through the local frontier).
    pub(crate) senders: Vec<Sender<StateMessage>>,
}

/// A distributed BFS worker that owns one partition of the fingerprint space.
///
/// The worker maintains:
/// - A local frontier (BFS queue) of states in its partition
/// - A set of seen fingerprints (deduplication) for its partition only
/// - Exchange channels for cross-partition state routing
///
/// Thread-safety: each worker runs on its own thread and owns its state.
/// The only shared data flows through crossbeam channels.
pub(crate) struct DistributedBfsWorker {
    /// This worker's partition index.
    partition_id: usize,
    /// Partitioning scheme (shared, immutable).
    scheme: PartitionScheme,
    /// Local BFS frontier queue.
    frontier: VecDeque<StateMessage>,
    /// Seen fingerprints for this partition's slice of the state space.
    seen: FxHashSet<Fingerprint>,
    /// Exchange channel endpoints for cross-partition communication.
    channels: PartitionChannels,
    /// Statistics: number of states processed by this worker.
    pub(crate) states_processed: usize,
    /// Statistics: number of states received from other partitions.
    pub(crate) states_received: usize,
    /// Statistics: number of states sent to other partitions.
    pub(crate) states_sent: usize,
    /// Statistics: maximum local frontier depth.
    pub(crate) max_frontier_depth: usize,
}

impl DistributedBfsWorker {
    /// Create a new worker for the given partition.
    pub(crate) fn new(
        partition_id: usize,
        scheme: PartitionScheme,
        channels: PartitionChannels,
    ) -> Self {
        DistributedBfsWorker {
            partition_id,
            scheme,
            frontier: VecDeque::new(),
            seen: FxHashSet::default(),
            channels,
            states_processed: 0,
            states_received: 0,
            states_sent: 0,
            max_frontier_depth: 0,
        }
    }

    /// Seed the worker's frontier with initial states that belong to this partition.
    ///
    /// Called once before the BFS loop starts. States not belonging to this
    /// partition are silently dropped (the coordinator routes them correctly).
    pub(crate) fn seed(&mut self, states: impl IntoIterator<Item = StateMessage>) {
        for msg in states {
            let target = self.scheme.partition_for_fp(msg.fp);
            if target == self.partition_id {
                if self.seen.insert(msg.fp) {
                    self.frontier.push_back(msg);
                }
            }
        }
        self.max_frontier_depth = self.max_frontier_depth.max(self.frontier.len());
    }

    /// Drain all available messages from the exchange channel into the local frontier.
    ///
    /// Non-blocking: processes all pending messages, then returns.
    /// States that have already been seen are silently dropped.
    pub(crate) fn drain_incoming(&mut self) {
        loop {
            match self.channels.rx.try_recv() {
                Ok(msg) => {
                    debug_assert_eq!(
                        self.scheme.partition_for_fp(msg.fp),
                        self.partition_id,
                        "received state for wrong partition"
                    );
                    self.states_received += 1;
                    if self.seen.insert(msg.fp) {
                        self.frontier.push_back(msg);
                    }
                }
                Err(TryRecvError::Empty) => break,
                Err(TryRecvError::Disconnected) => break,
            }
        }
        self.max_frontier_depth = self.max_frontier_depth.max(self.frontier.len());
    }

    /// Route a successor state to the correct partition.
    ///
    /// If the successor belongs to this partition, dedup and add to local frontier.
    /// Otherwise, send it to the owning partition's exchange channel.
    pub(crate) fn route_successor(&mut self, msg: StateMessage) {
        let target = self.scheme.partition_for_fp(msg.fp);
        if target == self.partition_id {
            // Local: dedup and enqueue
            if self.seen.insert(msg.fp) {
                self.frontier.push_back(msg);
                self.max_frontier_depth = self.max_frontier_depth.max(self.frontier.len());
            }
        } else {
            // Remote: send to target partition
            // Use try_send to avoid blocking; if the channel is full, this is
            // a backpressure signal. For the PoC we use bounded channels and
            // fall back to blocking send.
            let _ = self.channels.senders[target].send(msg);
            self.states_sent += 1;
        }
    }

    /// Try to get the next state to process.
    ///
    /// First checks the local frontier, then drains incoming exchange messages.
    /// Returns `None` when both the local frontier and exchange channel are empty.
    pub(crate) fn try_next(&mut self) -> Option<StateMessage> {
        // Prefer local frontier (already deduped)
        if let Some(msg) = self.frontier.pop_front() {
            self.states_processed += 1;
            return Some(msg);
        }

        // Try incoming exchange channel
        self.drain_incoming();

        if let Some(msg) = self.frontier.pop_front() {
            self.states_processed += 1;
            return Some(msg);
        }

        None
    }

    /// Number of distinct states seen by this partition.
    pub(crate) fn distinct_states(&self) -> usize {
        self.seen.len()
    }

    /// Whether the local frontier is empty AND the exchange channel has no pending messages.
    pub(crate) fn is_idle(&self) -> bool {
        self.frontier.is_empty() && self.channels.rx.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_channels(n: usize) -> Vec<PartitionChannels> {
        // Create N receivers and N*N senders
        let mut receivers = Vec::with_capacity(n);
        let _all_senders: Vec<Vec<Sender<StateMessage>>> = (0..n).map(|_| Vec::new()).collect();

        let mut txs_for_partition: Vec<Sender<StateMessage>> = Vec::new();
        let mut rxs: Vec<Receiver<StateMessage>> = Vec::new();

        for _ in 0..n {
            let (tx, rx) = crossbeam_channel::bounded(1024);
            txs_for_partition.push(tx);
            rxs.push(rx);
        }

        // Each worker gets a clone of every partition's sender
        for i in 0..n {
            let senders: Vec<Sender<StateMessage>> = txs_for_partition.clone();
            receivers.push(PartitionChannels {
                rx: rxs[i].clone(),
                senders,
            });
        }

        receivers
    }

    #[test]
    fn test_worker_seed_filters_partition() {
        let scheme = PartitionScheme::modulo(2);
        let channels = make_channels(2);
        let mut w0 =
            DistributedBfsWorker::new(0, scheme.clone(), channels.into_iter().next().unwrap());

        // Seed with states, some for partition 0, some for partition 1
        let states = (0..10u64).map(|i| StateMessage {
            fp: Fingerprint(i),
            state: ArrayState::new(1),
            depth: 0,
        });
        w0.seed(states);

        // Only even fingerprints belong to partition 0 (fp % 2 == 0)
        assert_eq!(w0.distinct_states(), 5);
    }

    #[test]
    fn test_worker_route_local() {
        let scheme = PartitionScheme::modulo(2);
        let channels = make_channels(2);
        let mut w0 =
            DistributedBfsWorker::new(0, scheme.clone(), channels.into_iter().next().unwrap());

        // Route a state that belongs to partition 0
        let msg = StateMessage {
            fp: Fingerprint(10), // 10 % 2 == 0
            state: ArrayState::new(1),
            depth: 1,
        };
        w0.route_successor(msg);

        assert_eq!(w0.distinct_states(), 1);
        assert_eq!(w0.states_sent, 0);
    }

    #[test]
    fn test_worker_route_remote() {
        let scheme = PartitionScheme::modulo(2);
        let mut channels = make_channels(2);
        let ch1 = channels.remove(1);
        let ch0 = channels.remove(0);
        let mut w0 = DistributedBfsWorker::new(0, scheme.clone(), ch0);
        let mut w1 = DistributedBfsWorker::new(1, scheme.clone(), ch1);

        // Route a state from w0 that belongs to partition 1
        let msg = StateMessage {
            fp: Fingerprint(11), // 11 % 2 == 1
            state: ArrayState::new(1),
            depth: 1,
        };
        w0.route_successor(msg);

        assert_eq!(w0.states_sent, 1);
        assert_eq!(w0.distinct_states(), 0);

        // w1 should receive it
        w1.drain_incoming();
        assert_eq!(w1.states_received, 1);
        assert_eq!(w1.distinct_states(), 1);
    }

    #[test]
    fn test_worker_dedup() {
        let scheme = PartitionScheme::modulo(1);
        let channels = make_channels(1);
        let mut w = DistributedBfsWorker::new(0, scheme, channels.into_iter().next().unwrap());

        // Route the same state twice
        for _ in 0..2 {
            let msg = StateMessage {
                fp: Fingerprint(42),
                state: ArrayState::new(1),
                depth: 0,
            };
            w.route_successor(msg);
        }

        assert_eq!(w.distinct_states(), 1, "duplicate state should be deduped");
    }

    #[test]
    fn test_worker_try_next_drains_incoming() {
        let scheme = PartitionScheme::modulo(2);
        let mut channels = make_channels(2);
        let ch1 = channels.remove(1);
        let ch0 = channels.remove(0);
        let mut w0 = DistributedBfsWorker::new(0, scheme.clone(), ch0);
        let _w1 = DistributedBfsWorker::new(1, scheme.clone(), ch1);

        // Simulate external send to w0's channel
        // w0's rx = partition 0's receiver, so we need to send to partition 0
        // The sender for partition 0 is at index 0 in any worker's senders list
        let msg = StateMessage {
            fp: Fingerprint(100), // 100 % 2 == 0
            state: ArrayState::new(1),
            depth: 2,
        };
        // Use w1's sender to partition 0
        _w1.channels.senders[0].send(msg).unwrap();

        // w0 should find it via try_next
        let got = w0.try_next();
        assert!(got.is_some());
        assert_eq!(got.unwrap().fp, Fingerprint(100));
    }
}
