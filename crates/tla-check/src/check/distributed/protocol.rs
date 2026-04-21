// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Message protocol for distributed BFS inter-partition communication.
//!
//! Defines the envelope types exchanged between partition workers over their
//! crossbeam channels (local simulation) or a future network transport.
//!
//! # Message Taxonomy
//!
//! - [`PartitionMessage::State`] — a successor state forwarded to its owning
//!   partition for deduplication and further exploration.
//! - [`PartitionMessage::StealRequest`] — an idle worker asks a busy worker
//!   to share part of its frontier.
//! - [`PartitionMessage::StealResponse`] — the busy worker replies with a
//!   batch of states (or an empty batch if it has nothing to share).
//! - [`PartitionMessage::TerminationProbe`] — phase-1 probe in the two-phase
//!   quiescence protocol: asks the receiver "are you idle?"
//! - [`PartitionMessage::TerminationConfirm`] — phase-2 reply: "yes, I am
//!   still idle after re-draining my channel."
//!
//! Part of #3796.

use crate::state::{ArrayState, Fingerprint};

/// Unique identifier for a partition worker.
pub(crate) type PartitionId = usize;

/// A state in transit between partitions.
///
/// Carries the pre-computed fingerprint (avoids re-hashing at the receiver),
/// the full state data, and the BFS depth for level-sync tracking.
#[derive(Debug, Clone)]
pub(crate) struct StateTransfer {
    /// Pre-computed fingerprint of the state.
    pub(crate) fp: Fingerprint,
    /// Full state data for successor generation.
    pub(crate) state: ArrayState,
    /// BFS depth at which this state was discovered.
    pub(crate) depth: usize,
}

/// Message envelope for inter-partition communication.
///
/// All communication between distributed BFS workers flows through this type.
/// The transport layer (crossbeam channels for local, TCP/QUIC for network)
/// delivers `PartitionMessage` values opaquely.
#[derive(Debug, Clone)]
pub(crate) enum PartitionMessage {
    /// A successor state forwarded to its owning partition.
    ///
    /// The sender has already computed the fingerprint and determined that
    /// the state belongs to the target partition.
    State(StateTransfer),

    /// Work-stealing request from an idle partition.
    ///
    /// The `requester` field identifies who to send the stolen states to.
    /// The `max_states` field caps the batch size to avoid over-draining
    /// the victim's frontier.
    StealRequest {
        /// Partition ID of the idle worker requesting work.
        requester: PartitionId,
        /// Maximum number of states the requester wants.
        max_states: usize,
    },

    /// Work-stealing response: a batch of states donated by a busy partition.
    ///
    /// May be empty if the victim has no states to spare. The requester
    /// should try a different victim or re-enter the idle protocol.
    StealResponse {
        /// Partition ID of the worker that donated the states.
        donor: PartitionId,
        /// Batch of states to process. Empty means "nothing to give."
        states: Vec<StateTransfer>,
    },
}

/// Statistics for message protocol activity on a single partition.
#[derive(Debug, Clone, Default)]
pub(crate) struct ProtocolStats {
    /// Number of state messages sent to other partitions.
    pub(crate) states_sent: usize,
    /// Number of state messages received from other partitions.
    pub(crate) states_received: usize,
    /// Number of steal requests sent.
    pub(crate) steal_requests_sent: usize,
    /// Number of steal requests received.
    pub(crate) steal_requests_received: usize,
    /// Number of states donated via steal responses.
    pub(crate) states_donated: usize,
    /// Number of states received via steal responses.
    pub(crate) states_stolen: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_state_transfer_roundtrip() {
        let transfer = StateTransfer {
            fp: Fingerprint(42),
            state: ArrayState::new(2),
            depth: 5,
        };
        assert_eq!(transfer.fp, Fingerprint(42));
        assert_eq!(transfer.depth, 5);
    }

    #[test]
    fn test_partition_message_variants() {
        // Verify all variants are constructible and matchable.
        let msgs: Vec<PartitionMessage> = vec![
            PartitionMessage::State(StateTransfer {
                fp: Fingerprint(1),
                state: ArrayState::new(1),
                depth: 0,
            }),
            PartitionMessage::StealRequest {
                requester: 0,
                max_states: 32,
            },
            PartitionMessage::StealResponse {
                donor: 1,
                states: vec![],
            },
        ];

        for msg in &msgs {
            match msg {
                PartitionMessage::State(st) => {
                    assert_eq!(st.fp, Fingerprint(1));
                }
                PartitionMessage::StealRequest {
                    requester,
                    max_states,
                } => {
                    assert_eq!(*requester, 0);
                    assert_eq!(*max_states, 32);
                }
                PartitionMessage::StealResponse { donor, states } => {
                    assert_eq!(*donor, 1);
                    assert!(states.is_empty());
                }
            }
        }
    }

    #[test]
    fn test_protocol_stats_default() {
        let stats = ProtocolStats::default();
        assert_eq!(stats.states_sent, 0);
        assert_eq!(stats.states_received, 0);
        assert_eq!(stats.steal_requests_sent, 0);
        assert_eq!(stats.steal_requests_received, 0);
        assert_eq!(stats.states_donated, 0);
        assert_eq!(stats.states_stolen, 0);
    }
}
