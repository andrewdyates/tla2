// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(dead_code)]

//! Distributed BFS framework: fingerprint-partitioned state exploration.
//!
//! Partitions the fingerprint space across N worker threads. Each worker owns
//! 1/N of the state space and is responsible for deduplication and successor
//! processing within its partition. Cross-partition successors are routed via
//! bounded crossbeam channels.
//!
//! # Architecture
//!
//! ```text
//! ┌────────────────────────────────────────────────────────┐
//! │              Coordinator (main thread)                  │
//! │  1. Compute initial states                             │
//! │  2. Route each init state to its owning partition      │
//! │  3. Spawn N worker threads                             │
//! │  4. Join all threads, sum state counts                 │
//! └───────────┬──────────┬──────────┬──────────┬──────────┘
//!             │          │          │          │
//!        ┌────▼────┐┌────▼────┐┌────▼────┐┌────▼────┐
//!        │Worker 0 ││Worker 1 ││Worker 2 ││Worker 3 │
//!        │ fp%4==0 ││ fp%4==1 ││ fp%4==2 ││ fp%4==3 │
//!        └────┬────┘└────┬────┘└────┬────┘└────┬────┘
//!             │          │          │          │
//!             └──────────┴──────────┴──────────┘
//!                   crossbeam channels
//!                 (bounded MPMC per partition)
//! ```
//!
//! # Design Constraints
//!
//! - **Thread-based first**: same-process shared-memory channels. Network
//!   transport is a future extension (swap channel impl behind a trait).
//! - **Correctness**: total distinct states must match sequential BFS exactly.
//! - **Termination**: work-counter protocol (Mattern credit distribution) —
//!   a global atomic counter tracks pending work items. When it reaches zero,
//!   all work is done.
//!
//! # Pillar 6 Roadmap
//!
//! Phase 1: Thread-local workers with crossbeam channels.
//! Phase 2 (current): Multi-machine network transport over TCP, Dijkstra
//!   termination detection, distributed invariant violation propagation,
//!   and cross-node progress reporting.
//! Phase 3: Dynamic partition reassignment for load balancing.

pub(crate) mod partition;
pub(crate) mod worker;

// Phase 2: Multi-machine distributed BFS infrastructure
pub(crate) mod dijkstra_termination;
pub(crate) mod node;
pub(crate) mod progress;
pub(crate) mod transport;
// Phase 1 existing modules
pub(crate) mod protocol;
pub(crate) mod termination;
pub(crate) mod work_stealing;

use std::sync::atomic::{AtomicBool, AtomicIsize, AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

use crossbeam_channel::bounded;

use self::partition::PartitionScheme;
use self::worker::{PartitionChannels, StateMessage};
use crate::state::{ArrayState, Fingerprint};

/// Channel capacity per partition exchange channel.
///
/// Bounded to provide backpressure. 4096 states is ~128KB of messages,
/// large enough to absorb BFS wavefront bursts without blocking.
const EXCHANGE_CHANNEL_CAPACITY: usize = 4096;

/// State exchange channel set: one bounded MPMC channel per partition.
///
/// Workers send non-local successors to the target partition's channel.
/// Each partition's worker reads from its own channel.
pub(crate) struct StateExchangeChannels {
    /// `senders[i]` sends to partition `i`.
    senders: Vec<crossbeam_channel::Sender<StateMessage>>,
    /// `receivers[i]` receives states destined for partition `i`.
    receivers: Vec<crossbeam_channel::Receiver<StateMessage>>,
}

impl StateExchangeChannels {
    /// Create exchange channels for `n` partitions.
    pub(crate) fn new(n: usize) -> Self {
        let mut senders = Vec::with_capacity(n);
        let mut receivers = Vec::with_capacity(n);
        for _ in 0..n {
            let (tx, rx) = bounded(EXCHANGE_CHANNEL_CAPACITY);
            senders.push(tx);
            receivers.push(rx);
        }
        StateExchangeChannels { senders, receivers }
    }

    /// Build per-worker channel endpoints.
    ///
    /// Each worker gets:
    /// - Its own receiver (for incoming states)
    /// - A clone of every partition's sender (for outgoing routing)
    ///
    /// Consumes `self` to move receivers (non-cloneable) into workers.
    fn into_worker_channels(self) -> Vec<PartitionChannels> {
        let receivers = self.receivers;
        let senders = self.senders;

        receivers
            .into_iter()
            .map(|rx| PartitionChannels {
                rx,
                senders: senders.clone(),
            })
            .collect::<Vec<_>>()
    }
}

/// Distributed BFS frontier: manages all partition workers.
///
/// The coordinator creates workers, distributes initial states, runs the
/// BFS loop across all partitions, and collects results.
pub(crate) struct DistributedFrontier {
    /// Partitioning scheme.
    scheme: PartitionScheme,
    /// Number of worker threads.
    num_workers: usize,
}

/// Result of a distributed BFS run.
#[derive(Debug)]
pub(crate) struct DistributedBfsResult {
    /// Total distinct states found across all partitions.
    pub(crate) total_distinct_states: usize,
    /// Per-partition state counts (for load balance analysis).
    pub(crate) partition_states: Vec<usize>,
    /// Per-partition states received via exchange channels.
    pub(crate) partition_received: Vec<usize>,
    /// Per-partition states sent via exchange channels.
    pub(crate) partition_sent: Vec<usize>,
    /// Maximum BFS depth reached.
    pub(crate) max_depth: usize,
}

impl DistributedFrontier {
    /// Create a new distributed frontier with modulo partitioning.
    pub(crate) fn new(num_workers: usize) -> Self {
        DistributedFrontier {
            scheme: PartitionScheme::modulo(num_workers),
            num_workers,
        }
    }

    /// Create with a custom partitioning scheme.
    #[allow(dead_code)]
    pub(crate) fn with_scheme(scheme: PartitionScheme) -> Self {
        let num_workers = scheme.num_partitions();
        DistributedFrontier {
            scheme,
            num_workers,
        }
    }

    /// Run distributed BFS with a user-provided successor function.
    ///
    /// The successor function takes `(state, fingerprint)` and returns a
    /// list of `(successor_state, successor_fingerprint)` pairs. The function
    /// must be `Send + Sync + Clone` to be shared across threads.
    pub(crate) fn run_bfs<F>(
        &self,
        initial_states: Vec<(Fingerprint, ArrayState)>,
        successor_fn: F,
    ) -> DistributedBfsResult
    where
        F: Fn(&ArrayState, Fingerprint) -> Vec<(Fingerprint, ArrayState)>
            + Send
            + Sync
            + Clone
            + 'static,
    {
        let n = self.num_workers;
        let scheme = self.scheme.clone();

        // Create exchange channels
        let exchange = StateExchangeChannels::new(n);
        let worker_channels = exchange.into_worker_channels();

        // Shared termination state (work-counter protocol)
        let term = Arc::new(TerminationState::new());
        let max_depth = Arc::new(AtomicUsize::new(0));

        // Distribute initial states to per-partition seed lists
        let mut partition_seeds: Vec<Vec<StateMessage>> = (0..n).map(|_| Vec::new()).collect();
        for (fp, state) in initial_states {
            let target = scheme.partition_for_fp(fp);
            partition_seeds[target].push(StateMessage {
                fp,
                state,
                depth: 0,
            });
        }

        // Spawn worker threads
        let handles: Vec<_> = worker_channels
            .into_iter()
            .enumerate()
            .map(|(id, channels)| {
                let scheme = scheme.clone();
                let seeds = std::mem::take(&mut partition_seeds[id]);
                let successor_fn = successor_fn.clone();
                let term = Arc::clone(&term);
                let max_depth = Arc::clone(&max_depth);

                thread::Builder::new()
                    .name(format!("dist-bfs-{id}"))
                    .spawn(move || {
                        run_partition_worker(
                            id,
                            scheme,
                            channels,
                            seeds,
                            successor_fn,
                            term,
                            max_depth,
                        )
                    })
                    .expect("failed to spawn distributed BFS worker thread")
            })
            .collect();

        // Collect results
        let mut total_distinct = 0;
        let mut partition_states = Vec::with_capacity(n);
        let mut partition_received = Vec::with_capacity(n);
        let mut partition_sent = Vec::with_capacity(n);

        for handle in handles {
            let stats = handle.join().expect("distributed BFS worker panicked");
            total_distinct += stats.distinct;
            partition_states.push(stats.distinct);
            partition_received.push(stats.received);
            partition_sent.push(stats.sent);
        }

        DistributedBfsResult {
            total_distinct_states: total_distinct,
            partition_states,
            partition_received,
            partition_sent,
            max_depth: max_depth.load(Ordering::Relaxed),
        }
    }
}

/// Per-worker statistics returned after the BFS loop completes.
struct WorkerStats {
    distinct: usize,
    received: usize,
    sent: usize,
}

/// Shared termination state using work-counter (Mattern credit distribution).
///
/// A single atomic counter `work_count` tracks the number of "work items"
/// in the system -- states sitting in local frontiers plus states in-flight
/// in exchange channels that have not yet been received.
///
/// Increment when: seed is new, local successor is new, remote successor sent.
/// Decrement when: state fully processed, channel duplicate received.
/// No change when: new state received from channel, local dup.
///
/// Reaches 0 exactly when all work is done.
struct TerminationState {
    work_count: AtomicIsize,
    all_done: AtomicBool,
}

impl TerminationState {
    fn new() -> Self {
        TerminationState {
            work_count: AtomicIsize::new(0),
            all_done: AtomicBool::new(false),
        }
    }

    #[inline]
    fn add_work(&self) {
        self.work_count.fetch_add(1, Ordering::SeqCst);
    }

    #[inline]
    fn finish_work(&self) {
        let prev = self.work_count.fetch_sub(1, Ordering::SeqCst);
        if prev == 1 {
            self.all_done.store(true, Ordering::SeqCst);
        }
    }

    #[inline]
    fn is_done(&self) -> bool {
        self.all_done.load(Ordering::SeqCst)
    }
}

const POLL_TIMEOUT: std::time::Duration = std::time::Duration::from_millis(1);

/// Run one partition worker with work-counter termination detection.
fn run_partition_worker<F>(
    id: usize,
    scheme: PartitionScheme,
    channels: PartitionChannels,
    seeds: Vec<StateMessage>,
    successor_fn: F,
    term: Arc<TerminationState>,
    max_depth: Arc<AtomicUsize>,
) -> WorkerStats
where
    F: Fn(&ArrayState, Fingerprint) -> Vec<(Fingerprint, ArrayState)>,
{
    use rustc_hash::FxHashSet;
    use std::collections::VecDeque;

    let mut frontier: VecDeque<StateMessage> = VecDeque::new();
    let mut seen: FxHashSet<Fingerprint> = FxHashSet::default();
    let mut states_received: usize = 0;
    let mut states_sent: usize = 0;

    // Seed
    for msg in seeds {
        let target = scheme.partition_for_fp(msg.fp);
        if target == id && seen.insert(msg.fp) {
            frontier.push_back(msg);
            term.add_work();
        }
    }

    // BFS loop
    loop {
        while let Some(msg) = frontier.pop_front() {
            let depth = msg.depth;
            let _ = max_depth.fetch_max(depth, Ordering::Relaxed);

            let successors = successor_fn(&msg.state, msg.fp);
            for (succ_fp, succ_state) in successors {
                let succ_msg = StateMessage {
                    fp: succ_fp,
                    state: succ_state,
                    depth: depth + 1,
                };
                let target = scheme.partition_for_fp(succ_fp);
                if target == id {
                    if seen.insert(succ_fp) {
                        frontier.push_back(succ_msg);
                        term.add_work();
                    }
                } else {
                    term.add_work();
                    let _ = channels.senders[target].send(succ_msg);
                    states_sent += 1;
                }
            }
            term.finish_work();

            if term.is_done() {
                return WorkerStats {
                    distinct: seen.len(),
                    received: states_received,
                    sent: states_sent,
                };
            }
        }

        // Drain exchange channel
        let mut got_work = false;
        loop {
            match channels.rx.try_recv() {
                Ok(msg) => {
                    states_received += 1;
                    if seen.insert(msg.fp) {
                        frontier.push_back(msg);
                        got_work = true;
                    } else {
                        term.finish_work();
                    }
                }
                Err(crossbeam_channel::TryRecvError::Empty) => break,
                Err(crossbeam_channel::TryRecvError::Disconnected) => break,
            }
        }
        if got_work {
            continue;
        }

        if term.is_done() {
            return WorkerStats {
                distinct: seen.len(),
                received: states_received,
                sent: states_sent,
            };
        }

        // Block briefly on channel
        match channels.rx.recv_timeout(POLL_TIMEOUT) {
            Ok(msg) => {
                states_received += 1;
                if seen.insert(msg.fp) {
                    frontier.push_back(msg);
                } else {
                    term.finish_work();
                }
            }
            Err(crossbeam_channel::RecvTimeoutError::Timeout) => {}
            Err(crossbeam_channel::RecvTimeoutError::Disconnected) => {
                return WorkerStats {
                    distinct: seen.len(),
                    received: states_received,
                    sent: states_sent,
                };
            }
        }
    }
}

#[cfg(test)]
mod net_tests;
#[cfg(test)]
mod tests;
