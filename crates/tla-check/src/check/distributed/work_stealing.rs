// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Work-stealing protocol for distributed BFS load balancing.
//!
//! When a partition worker's local frontier is exhausted and its exchange
//! channel is empty, it attempts to steal work from busier partitions before
//! entering the termination detection protocol.
//!
//! # Algorithm
//!
//! 1. The idle worker selects a victim partition using a round-robin probe.
//! 2. It sends a [`StealRequest`][`super::protocol::PartitionMessage::StealRequest`]
//!    to the victim's channel.
//! 3. The victim, on its next channel drain, detects the steal request and
//!    donates up to half of its local frontier (bounded by `max_steal_batch`).
//! 4. The idle worker receives the donated states via a
//!    [`StealResponse`][`super::protocol::PartitionMessage::StealResponse`].
//!
//! The half-frontier donation strategy ensures the victim retains enough work
//! to stay busy while the idle worker gets a meaningful batch to process.
//!
//! # Fairness
//!
//! Victims are probed in round-robin order starting from a random offset
//! (based on the requester's partition ID), so no single partition is
//! always the first steal target.
//!
//! Part of #3796.

use std::collections::VecDeque;

use super::protocol::{PartitionId, PartitionMessage, StateTransfer};

/// Configuration for the work-stealing subsystem.
#[derive(Debug, Clone, Copy)]
pub(crate) struct WorkStealingConfig {
    /// Maximum number of states to steal in a single batch.
    /// The actual batch is `min(max_steal_batch, victim_frontier / 2)`.
    pub(crate) max_steal_batch: usize,
    /// Number of consecutive steal failures before giving up and entering
    /// the termination protocol.
    pub(crate) max_steal_attempts: usize,
}

impl Default for WorkStealingConfig {
    fn default() -> Self {
        Self {
            max_steal_batch: 64,
            max_steal_attempts: 3,
        }
    }
}

/// Work-stealing state for a single partition worker.
///
/// Tracks the round-robin victim pointer and steal attempt count so that
/// repeated steal failures eventually give up and enter termination detection.
pub(crate) struct WorkStealer {
    /// This worker's partition ID.
    partition_id: PartitionId,
    /// Total partitions in the distributed run.
    num_partitions: usize,
    /// Configuration parameters.
    config: WorkStealingConfig,
    /// Round-robin pointer: next victim to probe.
    next_victim: PartitionId,
    /// Number of consecutive steal failures (empty responses or no response).
    consecutive_failures: usize,
}

impl WorkStealer {
    /// Create a new work stealer for the given partition.
    pub(crate) fn new(
        partition_id: PartitionId,
        num_partitions: usize,
        config: WorkStealingConfig,
    ) -> Self {
        // Start probing from the partition after ours (avoid self).
        let next_victim = (partition_id + 1) % num_partitions;
        Self {
            partition_id,
            num_partitions,
            config,
            next_victim,
            consecutive_failures: 0,
        }
    }

    /// Whether the stealer has exhausted its steal attempts.
    ///
    /// When this returns `true`, the worker should enter the termination
    /// detection protocol instead of trying more steals.
    pub(crate) fn exhausted(&self) -> bool {
        // Single-partition runs have nobody to steal from.
        if self.num_partitions <= 1 {
            return true;
        }
        self.consecutive_failures >= self.config.max_steal_attempts
    }

    /// Reset the consecutive failure counter (called when the worker
    /// finds work — either from its own frontier or a successful steal).
    pub(crate) fn reset(&mut self) {
        self.consecutive_failures = 0;
    }

    /// Select the next victim to probe and build a steal request message.
    ///
    /// Returns `None` if steal attempts are exhausted.
    pub(crate) fn make_request(&mut self) -> Option<(PartitionId, PartitionMessage)> {
        if self.exhausted() {
            return None;
        }

        let victim = self.next_victim;
        // Advance round-robin, skipping self.
        self.next_victim = (self.next_victim + 1) % self.num_partitions;
        if self.next_victim == self.partition_id {
            self.next_victim = (self.next_victim + 1) % self.num_partitions;
        }

        Some((
            victim,
            PartitionMessage::StealRequest {
                requester: self.partition_id,
                max_states: self.config.max_steal_batch,
            },
        ))
    }

    /// Record a steal failure (empty response or timeout).
    pub(crate) fn record_failure(&mut self) {
        self.consecutive_failures += 1;
    }

    /// Record a successful steal (non-empty response).
    pub(crate) fn record_success(&mut self) {
        self.consecutive_failures = 0;
    }
}

/// Process an incoming steal request by donating up to half of the local
/// frontier, bounded by `max_states`.
///
/// Returns the response message (which may contain an empty batch if the
/// frontier has no states to spare).
///
/// The "donate half" strategy balances load: the donor retains enough work
/// to stay busy, while the thief gets a meaningful batch.
pub(crate) fn handle_steal_request(
    frontier: &mut VecDeque<StateTransfer>,
    donor_id: PartitionId,
    max_states: usize,
) -> PartitionMessage {
    // Donate at most half the frontier, capped at max_states.
    let donate_count = (frontier.len() / 2).min(max_states);
    let mut stolen = Vec::with_capacity(donate_count);

    // Take from the back of the frontier (least-recently-added states),
    // which in BFS are the deepest and thus least likely to produce
    // successors that the donor needs urgently.
    for _ in 0..donate_count {
        if let Some(state) = frontier.pop_back() {
            stolen.push(state);
        }
    }

    PartitionMessage::StealResponse {
        donor: donor_id,
        states: stolen,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::Fingerprint;

    fn make_transfer(fp: u64) -> StateTransfer {
        StateTransfer {
            fp: Fingerprint(fp),
            state: crate::state::ArrayState::new(1),
            depth: 0,
        }
    }

    #[test]
    fn test_work_stealer_creation() {
        let ws = WorkStealer::new(0, 4, WorkStealingConfig::default());
        assert!(!ws.exhausted());
        assert_eq!(ws.next_victim, 1); // Starts at partition after ours.
    }

    #[test]
    fn test_work_stealer_single_partition_exhausted() {
        let mut ws = WorkStealer::new(0, 1, WorkStealingConfig::default());
        assert!(ws.exhausted()); // Nobody to steal from.
        assert!(ws.make_request().is_none());
    }

    #[test]
    fn test_work_stealer_round_robin() {
        let mut ws = WorkStealer::new(
            1,
            4,
            WorkStealingConfig {
                max_steal_batch: 32,
                max_steal_attempts: 10,
            },
        );

        // Should cycle through 2, 3, 0 (skipping 1 = self).
        let (v1, _) = ws.make_request().expect("should have request");
        assert_eq!(v1, 2);

        let (v2, _) = ws.make_request().expect("should have request");
        assert_eq!(v2, 3);

        let (v3, _) = ws.make_request().expect("should have request");
        assert_eq!(v3, 0);

        // Wraps around, skips self again.
        let (v4, _) = ws.make_request().expect("should have request");
        assert_eq!(v4, 2);
    }

    #[test]
    fn test_work_stealer_exhaustion() {
        let mut ws = WorkStealer::new(
            0,
            3,
            WorkStealingConfig {
                max_steal_batch: 32,
                max_steal_attempts: 2,
            },
        );

        assert!(!ws.exhausted());
        ws.record_failure();
        assert!(!ws.exhausted());
        ws.record_failure();
        assert!(ws.exhausted());
        assert!(ws.make_request().is_none());
    }

    #[test]
    fn test_work_stealer_reset() {
        let mut ws = WorkStealer::new(
            0,
            3,
            WorkStealingConfig {
                max_steal_batch: 32,
                max_steal_attempts: 2,
            },
        );

        ws.record_failure();
        ws.record_failure();
        assert!(ws.exhausted());

        ws.reset();
        assert!(!ws.exhausted());
    }

    #[test]
    fn test_work_stealer_success_resets_failures() {
        let mut ws = WorkStealer::new(
            0,
            3,
            WorkStealingConfig {
                max_steal_batch: 32,
                max_steal_attempts: 3,
            },
        );

        ws.record_failure();
        ws.record_failure();
        ws.record_success();
        assert!(!ws.exhausted()); // Success reset the counter.
    }

    #[test]
    fn test_handle_steal_request_empty_frontier() {
        let mut frontier: VecDeque<StateTransfer> = VecDeque::new();
        let response = handle_steal_request(&mut frontier, 0, 32);

        match response {
            PartitionMessage::StealResponse { donor, states } => {
                assert_eq!(donor, 0);
                assert!(states.is_empty());
            }
            other => panic!("expected StealResponse, got {:?}", other),
        }
    }

    #[test]
    fn test_handle_steal_request_donates_half() {
        let mut frontier: VecDeque<StateTransfer> = (0..10).map(|i| make_transfer(i)).collect();

        let response = handle_steal_request(&mut frontier, 1, 100);

        match response {
            PartitionMessage::StealResponse { donor, states } => {
                assert_eq!(donor, 1);
                assert_eq!(states.len(), 5); // Half of 10.
                assert_eq!(frontier.len(), 5); // Donor retains half.
            }
            other => panic!("expected StealResponse, got {:?}", other),
        }
    }

    #[test]
    fn test_handle_steal_request_capped_by_max_states() {
        let mut frontier: VecDeque<StateTransfer> = (0..100).map(|i| make_transfer(i)).collect();

        let response = handle_steal_request(&mut frontier, 2, 10);

        match response {
            PartitionMessage::StealResponse { donor, states } => {
                assert_eq!(donor, 2);
                // Half of 100 = 50, but capped at max_states=10.
                assert_eq!(states.len(), 10);
                assert_eq!(frontier.len(), 90);
            }
            other => panic!("expected StealResponse, got {:?}", other),
        }
    }

    #[test]
    fn test_handle_steal_request_single_state_frontier() {
        let mut frontier: VecDeque<StateTransfer> = VecDeque::new();
        frontier.push_back(make_transfer(42));

        let response = handle_steal_request(&mut frontier, 0, 32);

        match response {
            PartitionMessage::StealResponse { states, .. } => {
                // Half of 1 = 0 — cannot donate when frontier has only 1 state.
                assert!(states.is_empty());
                assert_eq!(frontier.len(), 1);
            }
            other => panic!("expected StealResponse, got {:?}", other),
        }
    }

    #[test]
    fn test_handle_steal_request_takes_from_back() {
        let mut frontier: VecDeque<StateTransfer> = VecDeque::new();
        for i in 0..6 {
            frontier.push_back(make_transfer(i));
        }

        let response = handle_steal_request(&mut frontier, 0, 100);

        match response {
            PartitionMessage::StealResponse { states, .. } => {
                assert_eq!(states.len(), 3); // Half of 6.
                                             // States taken from back: 5, 4, 3.
                let stolen_fps: Vec<u64> = states.iter().map(|s| s.fp.0).collect();
                assert_eq!(stolen_fps, vec![5, 4, 3]);
                // Remaining: 0, 1, 2.
                let remaining_fps: Vec<u64> = frontier.iter().map(|s| s.fp.0).collect();
                assert_eq!(remaining_fps, vec![0, 1, 2]);
            }
            other => panic!("expected StealResponse, got {:?}", other),
        }
    }

    /// Verify that consecutive steal requests with empty responses exhaust
    /// the stealer and it stops requesting.
    #[test]
    fn test_steal_request_message_format() {
        let mut ws = WorkStealer::new(
            2,
            4,
            WorkStealingConfig {
                max_steal_batch: 16,
                max_steal_attempts: 5,
            },
        );

        let (victim, msg) = ws.make_request().expect("should produce request");
        assert_eq!(victim, 3); // Next after 2.

        match msg {
            PartitionMessage::StealRequest {
                requester,
                max_states,
            } => {
                assert_eq!(requester, 2);
                assert_eq!(max_states, 16);
            }
            other => panic!("expected StealRequest, got {:?}", other),
        }
    }
}
