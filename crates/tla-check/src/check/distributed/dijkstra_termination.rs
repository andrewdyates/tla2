// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Dijkstra's token-based distributed termination detection.
//!
//! Implements Dijkstra, Feijen, and van Gasteren's token-passing algorithm for
//! detecting global termination in a distributed BFS. This is the standard
//! algorithm used by TLC for multi-machine model checking.
//!
//! # Algorithm
//!
//! The algorithm works on a logical ring of N nodes (0, 1, ..., N-1):
//!
//! 1. Each node maintains a **color** (white or black) and a **message counter**
//!    (net messages sent minus received).
//!
//! 2. When a node sends a message, it increments its counter. When it receives
//!    a message, it decrements its counter.
//!
//! 3. When a node sends a message to a node with a *lower* ID, it becomes
//!    **black** (this signals that the token may have missed some work).
//!
//! 4. **Node 0** initiates termination detection by sending a **white token**
//!    with counter = 0 around the ring when it becomes idle.
//!
//! 5. Each node on the ring, upon receiving the token while idle:
//!    - Adds its local counter to the token's counter
//!    - If the node is black, colors the token black and resets itself to white
//!    - Forwards the token to the next node in the ring
//!
//! 6. When the token returns to node 0:
//!    - If the token is **white** AND its counter is 0 AND node 0 is white
//!      AND node 0 is idle: **termination is confirmed**.
//!    - Otherwise: node 0 resets itself to white and initiates a new round.
//!
//! # Properties
//!
//! - **Safety**: Global termination is declared only when all nodes are idle
//!   and all messages have been delivered.
//! - **Liveness**: If all nodes become permanently idle, termination will
//!   eventually be detected (within 2 rounds in the worst case).
//! - **Overhead**: O(N) messages per detection round, where N is the number
//!   of nodes.
//!
//! Part of Pillar 6 Phase 2: Distributed termination detection.

#![allow(dead_code)]

use std::sync::atomic::{AtomicBool, AtomicI64, Ordering};
use std::sync::Mutex;

use super::transport::{NodeId, TokenColor};

/// Per-node termination detection state for Dijkstra's algorithm.
///
/// Each node in the distributed system owns one instance. The fields are
/// atomic or mutex-protected for safe access from both the BFS worker
/// thread and the network reader thread.
pub(crate) struct DijkstraTermination {
    /// This node's ID.
    node_id: NodeId,
    /// Total number of nodes.
    num_nodes: u32,
    /// This node's color (white = clean, black = sent backward message).
    /// Protected by mutex because color transitions are read-modify-write.
    color: Mutex<TokenColor>,
    /// Net message counter: incremented on send, decremented on receive.
    /// A node is considered "idle w.r.t. messages" when its counter is zero.
    message_counter: AtomicI64,
    /// Whether this node is currently idle (no local work).
    is_idle: AtomicBool,
    /// Whether global termination has been detected.
    terminated: AtomicBool,
    /// Whether node 0 has initiated a token round.
    token_in_flight: AtomicBool,
    /// Number of completed token rounds (for diagnostics).
    rounds_completed: AtomicI64,
}

/// Result of processing a received token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TokenAction {
    /// Forward the token to the next node with the given color and counter.
    Forward {
        next_node: NodeId,
        color: TokenColor,
        counter: i64,
    },
    /// Termination confirmed — all nodes are idle, all messages delivered.
    TerminationConfirmed,
    /// The round failed — node 0 should initiate a new round.
    RoundFailed,
    /// This node is not idle — absorb the token and do not forward.
    Absorbed,
}

impl DijkstraTermination {
    /// Create a new termination detector for the given node.
    pub(crate) fn new(node_id: NodeId, num_nodes: u32) -> Self {
        DijkstraTermination {
            node_id,
            num_nodes,
            color: Mutex::new(TokenColor::White),
            message_counter: AtomicI64::new(0),
            is_idle: AtomicBool::new(false),
            terminated: AtomicBool::new(false),
            token_in_flight: AtomicBool::new(false),
            rounds_completed: AtomicI64::new(0),
        }
    }

    /// Notify that this node sent a message.
    ///
    /// If the message is sent to a node with a lower ID, this node becomes black.
    pub(crate) fn on_message_sent(&self, target: NodeId) {
        self.message_counter.fetch_add(1, Ordering::SeqCst);
        if target < self.node_id {
            let mut color = self.color.lock().expect("color lock");
            *color = TokenColor::Black;
        }
    }

    /// Notify that this node received a message.
    pub(crate) fn on_message_received(&self) {
        self.message_counter.fetch_sub(1, Ordering::SeqCst);
    }

    /// Mark this node as idle (no local work remaining).
    pub(crate) fn set_idle(&self, idle: bool) {
        self.is_idle.store(idle, Ordering::SeqCst);
    }

    /// Whether this node is currently idle.
    pub(crate) fn is_idle(&self) -> bool {
        self.is_idle.load(Ordering::SeqCst)
    }

    /// Whether global termination has been confirmed.
    pub(crate) fn is_terminated(&self) -> bool {
        self.terminated.load(Ordering::SeqCst)
    }

    /// Force termination (used when a halt signal is received from another node).
    pub(crate) fn force_terminate(&self) {
        self.terminated.store(true, Ordering::SeqCst);
    }

    /// Initiate a termination detection round (node 0 only).
    ///
    /// Returns `Some(token)` if this node is idle and should start a round,
    /// `None` if this node is not idle or a round is already in progress.
    pub(crate) fn initiate_round(&self) -> Option<(NodeId, TokenColor, i64)> {
        if self.node_id != 0 {
            return None;
        }
        if !self.is_idle.load(Ordering::SeqCst) {
            return None;
        }
        if self.token_in_flight.swap(true, Ordering::SeqCst) {
            return None; // Already in flight
        }

        // Reset our color to white before sending the token
        {
            let mut color = self.color.lock().expect("color lock");
            *color = TokenColor::White;
        }

        let next_node = 1 % self.num_nodes;
        let counter = self.message_counter.load(Ordering::SeqCst);
        Some((next_node, TokenColor::White, counter))
    }

    /// Process a received termination token.
    ///
    /// Called when this node receives a token from the previous node in the ring.
    ///
    /// For non-initiator nodes: adds this node's message counter to the token
    /// counter and forwards. For node 0 (initiator): does NOT re-add its own
    /// counter because `initiate_round` already included it in the initial
    /// token value. This prevents double-counting node 0's messages.
    pub(crate) fn process_token(
        &self,
        token_color: TokenColor,
        _initiator: NodeId,
        token_counter: i64,
    ) -> TokenAction {
        // If we're not idle, absorb the token — we can't participate
        if !self.is_idle.load(Ordering::SeqCst) {
            self.token_in_flight.store(false, Ordering::SeqCst);
            return TokenAction::Absorbed;
        }

        if self.node_id == 0 {
            // Token has completed a full round back to node 0.
            // Node 0's counter was already included in the token by initiate_round(),
            // so we must NOT add it again here. We only check the accumulated counter
            // and our current color/idle state.
            self.rounds_completed.fetch_add(1, Ordering::SeqCst);
            self.token_in_flight.store(false, Ordering::SeqCst);

            let my_color = {
                let mut color = self.color.lock().expect("color lock");
                let c = *color;
                *color = TokenColor::White;
                c
            };

            let forwarded_color =
                if token_color == TokenColor::Black || my_color == TokenColor::Black {
                    TokenColor::Black
                } else {
                    TokenColor::White
                };

            if forwarded_color == TokenColor::White
                && token_counter == 0
                && self.is_idle.load(Ordering::SeqCst)
            {
                self.terminated.store(true, Ordering::SeqCst);
                return TokenAction::TerminationConfirmed;
            }
            return TokenAction::RoundFailed;
        }

        // Non-initiator node: add our counter and forward
        let my_counter = self.message_counter.load(Ordering::SeqCst);
        let combined_counter = token_counter + my_counter;

        let my_color = {
            let mut color = self.color.lock().expect("color lock");
            let c = *color;
            // Reset to white after participating
            *color = TokenColor::White;
            c
        };

        // The forwarded token color is black if either the incoming token
        // or this node is black
        let forwarded_color = if token_color == TokenColor::Black || my_color == TokenColor::Black {
            TokenColor::Black
        } else {
            TokenColor::White
        };

        // Forward to the next node in the ring
        let next_node = (self.node_id + 1) % self.num_nodes;
        TokenAction::Forward {
            next_node,
            color: forwarded_color,
            counter: combined_counter,
        }
    }

    /// Current message counter value (for diagnostics).
    pub(crate) fn message_counter(&self) -> i64 {
        self.message_counter.load(Ordering::SeqCst)
    }

    /// Number of completed token rounds (for diagnostics).
    pub(crate) fn rounds_completed(&self) -> i64 {
        self.rounds_completed.load(Ordering::SeqCst)
    }

    /// Current node color (for diagnostics).
    pub(crate) fn node_color(&self) -> TokenColor {
        *self.color.lock().expect("color lock")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_node_starts_white_idle_false() {
        let dt = DijkstraTermination::new(0, 3);
        assert_eq!(dt.node_color(), TokenColor::White);
        assert!(!dt.is_idle());
        assert!(!dt.is_terminated());
        assert_eq!(dt.message_counter(), 0);
    }

    #[test]
    fn test_message_sent_increments_counter() {
        let dt = DijkstraTermination::new(1, 3);
        dt.on_message_sent(2);
        assert_eq!(dt.message_counter(), 1);
        // Sent to higher ID — stays white
        assert_eq!(dt.node_color(), TokenColor::White);
    }

    #[test]
    fn test_message_sent_to_lower_id_turns_black() {
        let dt = DijkstraTermination::new(2, 3);
        dt.on_message_sent(0);
        assert_eq!(dt.message_counter(), 1);
        assert_eq!(dt.node_color(), TokenColor::Black);
    }

    #[test]
    fn test_message_received_decrements_counter() {
        let dt = DijkstraTermination::new(0, 3);
        dt.on_message_sent(1);
        dt.on_message_sent(1);
        dt.on_message_received();
        assert_eq!(dt.message_counter(), 1);
    }

    #[test]
    fn test_initiate_round_only_node0() {
        let dt1 = DijkstraTermination::new(1, 3);
        dt1.set_idle(true);
        assert!(
            dt1.initiate_round().is_none(),
            "non-zero node cannot initiate"
        );

        let dt0 = DijkstraTermination::new(0, 3);
        assert!(dt0.initiate_round().is_none(), "not idle yet");
        dt0.set_idle(true);
        let round = dt0.initiate_round();
        assert!(round.is_some());
        let (next, color, counter) = round.unwrap();
        assert_eq!(next, 1);
        assert_eq!(color, TokenColor::White);
        assert_eq!(counter, 0);
    }

    #[test]
    fn test_initiate_round_no_double_initiation() {
        let dt = DijkstraTermination::new(0, 3);
        dt.set_idle(true);
        assert!(dt.initiate_round().is_some());
        assert!(
            dt.initiate_round().is_none(),
            "second initiation should fail"
        );
    }

    #[test]
    fn test_simple_two_node_termination() {
        // Simulate: 2 nodes, both idle, no messages in flight.
        let dt0 = DijkstraTermination::new(0, 2);
        let dt1 = DijkstraTermination::new(1, 2);

        dt0.set_idle(true);
        dt1.set_idle(true);

        // Node 0 initiates
        let (next, color, counter) = dt0.initiate_round().expect("should initiate");
        assert_eq!(next, 1);

        // Node 1 processes token
        let action = dt1.process_token(color, 0, counter);
        match action {
            TokenAction::Forward {
                next_node,
                color,
                counter,
            } => {
                assert_eq!(next_node, 0);
                assert_eq!(color, TokenColor::White);
                assert_eq!(counter, 0);

                // Token returns to node 0
                let final_action = dt0.process_token(color, 0, counter);
                assert_eq!(final_action, TokenAction::TerminationConfirmed);
                assert!(dt0.is_terminated());
            }
            other => panic!("expected Forward, got {other:?}"),
        }
    }

    #[test]
    fn test_three_node_termination_with_balanced_messages() {
        // 3 nodes. Node 0 sent 1 message to node 1, node 1 received it.
        // Net counter sum should be 0.
        let dt0 = DijkstraTermination::new(0, 3);
        let dt1 = DijkstraTermination::new(1, 3);
        let dt2 = DijkstraTermination::new(2, 3);

        // Simulate: node 0 sends to node 1, node 1 receives
        dt0.on_message_sent(1);
        dt1.on_message_received();

        dt0.set_idle(true);
        dt1.set_idle(true);
        dt2.set_idle(true);

        // Round 1
        let (_next, color, counter) = dt0.initiate_round().expect("initiate");
        assert_eq!(counter, 1); // node 0 has +1

        let action1 = dt1.process_token(color, 0, counter);
        match action1 {
            TokenAction::Forward {
                next_node,
                color: c1,
                counter: cnt1,
            } => {
                assert_eq!(next_node, 2);
                assert_eq!(cnt1, 0); // 1 + (-1) = 0

                let action2 = dt2.process_token(c1, 0, cnt1);
                match action2 {
                    TokenAction::Forward {
                        next_node: n2,
                        color: c2,
                        counter: cnt2,
                    } => {
                        assert_eq!(n2, 0);
                        assert_eq!(cnt2, 0);

                        let final_action = dt0.process_token(c2, 0, cnt2);
                        assert_eq!(final_action, TokenAction::TerminationConfirmed);
                    }
                    other => panic!("expected Forward from node 2, got {other:?}"),
                }
            }
            other => panic!("expected Forward from node 1, got {other:?}"),
        }
    }

    #[test]
    fn test_black_node_fails_round() {
        // Node 2 sent a message to node 0 (backward), making it black.
        // The token should come back black, failing the round.
        let dt0 = DijkstraTermination::new(0, 3);
        let dt1 = DijkstraTermination::new(1, 3);
        let dt2 = DijkstraTermination::new(2, 3);

        // Node 2 sends backward to node 0, node 0 receives.
        dt2.on_message_sent(0);
        dt0.on_message_received();

        dt0.set_idle(true);
        dt1.set_idle(true);
        dt2.set_idle(true);

        let (_, color, counter) = dt0.initiate_round().expect("initiate");
        // Node 0: counter = -1 (received 1)
        assert_eq!(counter, -1);

        let action1 = dt1.process_token(color, 0, counter);
        let (_, c1, cnt1) = match action1 {
            TokenAction::Forward {
                next_node,
                color,
                counter,
            } => (next_node, color, counter),
            other => panic!("expected Forward, got {other:?}"),
        };

        // Node 2 is black (sent backward), so token turns black
        let action2 = dt2.process_token(c1, 0, cnt1);
        let (_, c2, cnt2) = match action2 {
            TokenAction::Forward {
                next_node,
                color,
                counter,
            } => (next_node, color, counter),
            other => panic!("expected Forward, got {other:?}"),
        };
        assert_eq!(c2, TokenColor::Black);
        // Counter: -1 + 0 + 1 = 0
        assert_eq!(cnt2, 0);

        // Token returns to node 0 — black token means round fails
        let final_action = dt0.process_token(c2, 0, cnt2);
        assert_eq!(final_action, TokenAction::RoundFailed);
        assert!(!dt0.is_terminated());
    }

    #[test]
    fn test_not_idle_absorbs_token() {
        let dt1 = DijkstraTermination::new(1, 2);
        // Node 1 is NOT idle
        let action = dt1.process_token(TokenColor::White, 0, 0);
        assert_eq!(action, TokenAction::Absorbed);
    }

    #[test]
    fn test_force_terminate() {
        let dt = DijkstraTermination::new(1, 3);
        assert!(!dt.is_terminated());
        dt.force_terminate();
        assert!(dt.is_terminated());
    }

    #[test]
    fn test_rounds_completed_counter() {
        let dt0 = DijkstraTermination::new(0, 1);
        dt0.set_idle(true);

        // Single node: token goes 0 -> 0 immediately
        let (_, color, counter) = dt0.initiate_round().expect("initiate");
        let action = dt0.process_token(color, 0, counter);
        assert_eq!(action, TokenAction::TerminationConfirmed);
        assert_eq!(dt0.rounds_completed(), 1);
    }

    #[test]
    fn test_node_resets_to_white_after_token_pass() {
        let dt = DijkstraTermination::new(1, 3);
        dt.on_message_sent(0); // Turns black
        assert_eq!(dt.node_color(), TokenColor::Black);

        dt.set_idle(true);
        let _ = dt.process_token(TokenColor::White, 0, 0);

        // After passing the token, node should be white again
        assert_eq!(dt.node_color(), TokenColor::White);
    }
}
