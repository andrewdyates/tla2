// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TCP network transport for distributed BFS state exchange.
//!
//! Provides reliable, length-prefixed message delivery between distributed
//! model checking nodes. Each node runs a TCP listener and maintains outbound
//! connections to all other nodes.
//!
//! # Wire Format
//!
//! ```text
//! ┌──────────┬──────────┬──────────────────────────────┐
//! │ len (4B) │ tag (1B) │ payload (len - 1 bytes)      │
//! └──────────┴──────────┴──────────────────────────────┘
//! ```
//!
//! - `len`: u32 big-endian, total payload length including the tag byte
//! - `tag`: message type discriminator
//! - `payload`: message-specific binary data
//!
//! # Message Tags
//!
//! - `0x01` State: fp(8B) + depth(4B) + num_values(4B) + values(variable)
//! - `0x02` Halt: node_id(4B) + reason_len(4B) + reason(variable)
//! - `0x03` Token: color(1B) + node_id(4B) + counter(8B)
//! - `0x04` ProgressRequest: node_id(4B)
//! - `0x05` ProgressReport: node_id(4B) + distinct(8B) + depth(4B) + transitions(8B)
//! - `0x06` Ack: sequence(8B)
//!
//! Part of Pillar 6 Phase 2: Network transport.

#![allow(dead_code)]

use std::collections::HashMap;
use std::io::{self, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

use crate::state::{ArrayState, Fingerprint};

/// Unique identifier for a node in the distributed system.
pub(crate) type NodeId = u32;

/// Message tags for the wire protocol.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MessageTag {
    /// State transfer between nodes.
    State = 0x01,
    /// Halt signal: a node detected an invariant violation or error.
    Halt = 0x02,
    /// Dijkstra termination token.
    Token = 0x03,
    /// Request progress stats from a node.
    ProgressRequest = 0x04,
    /// Progress stats report from a node.
    ProgressReport = 0x05,
    /// Acknowledgment (for flow control).
    Ack = 0x06,
}

impl MessageTag {
    pub(crate) fn from_byte(b: u8) -> Option<Self> {
        match b {
            0x01 => Some(Self::State),
            0x02 => Some(Self::Halt),
            0x03 => Some(Self::Token),
            0x04 => Some(Self::ProgressRequest),
            0x05 => Some(Self::ProgressReport),
            0x06 => Some(Self::Ack),
            _ => None,
        }
    }
}

/// A network message exchanged between distributed BFS nodes.
#[derive(Debug, Clone)]
pub(crate) enum NetMessage {
    /// A state to be explored by the target node.
    State {
        fp: Fingerprint,
        state: ArrayState,
        depth: u32,
    },
    /// Halt signal: the sending node detected a violation or fatal error.
    Halt { source_node: NodeId, reason: String },
    /// Dijkstra termination detection token.
    Token {
        color: TokenColor,
        initiator: NodeId,
        counter: i64,
    },
    /// Request for progress statistics.
    ProgressRequest { requester: NodeId },
    /// Progress statistics from a node.
    ProgressReport {
        node_id: NodeId,
        distinct_states: u64,
        max_depth: u32,
        transitions: u64,
    },
    /// Flow-control acknowledgment.
    Ack { sequence: u64 },
}

/// Token colors for Dijkstra's termination algorithm.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum TokenColor {
    White = 0,
    Black = 1,
}

impl TokenColor {
    fn from_byte(b: u8) -> Self {
        match b {
            0 => Self::White,
            _ => Self::Black,
        }
    }
}

// ---------- Wire encoding / decoding ----------

/// Encode a `NetMessage` into a length-prefixed byte buffer.
pub(crate) fn encode_message(msg: &NetMessage) -> Vec<u8> {
    let mut payload = Vec::with_capacity(64);

    match msg {
        NetMessage::State { fp, state, depth } => {
            payload.push(MessageTag::State as u8);
            payload.extend_from_slice(&fp.0.to_be_bytes());
            payload.extend_from_slice(&depth.to_be_bytes());
            let values = state.materialize_values();
            payload.extend_from_slice(&(values.len() as u32).to_be_bytes());
            for v in &values {
                let s = format!("{:?}", v);
                let s_bytes = s.as_bytes();
                payload.extend_from_slice(&(s_bytes.len() as u32).to_be_bytes());
                payload.extend_from_slice(s_bytes);
            }
        }
        NetMessage::Halt {
            source_node,
            reason,
        } => {
            payload.push(MessageTag::Halt as u8);
            payload.extend_from_slice(&source_node.to_be_bytes());
            let reason_bytes = reason.as_bytes();
            payload.extend_from_slice(&(reason_bytes.len() as u32).to_be_bytes());
            payload.extend_from_slice(reason_bytes);
        }
        NetMessage::Token {
            color,
            initiator,
            counter,
        } => {
            payload.push(MessageTag::Token as u8);
            payload.push(*color as u8);
            payload.extend_from_slice(&initiator.to_be_bytes());
            payload.extend_from_slice(&counter.to_be_bytes());
        }
        NetMessage::ProgressRequest { requester } => {
            payload.push(MessageTag::ProgressRequest as u8);
            payload.extend_from_slice(&requester.to_be_bytes());
        }
        NetMessage::ProgressReport {
            node_id,
            distinct_states,
            max_depth,
            transitions,
        } => {
            payload.push(MessageTag::ProgressReport as u8);
            payload.extend_from_slice(&node_id.to_be_bytes());
            payload.extend_from_slice(&distinct_states.to_be_bytes());
            payload.extend_from_slice(&max_depth.to_be_bytes());
            payload.extend_from_slice(&transitions.to_be_bytes());
        }
        NetMessage::Ack { sequence } => {
            payload.push(MessageTag::Ack as u8);
            payload.extend_from_slice(&sequence.to_be_bytes());
        }
    }

    // Length prefix: 4-byte big-endian payload length
    let len = payload.len() as u32;
    let mut frame = Vec::with_capacity(4 + payload.len());
    frame.extend_from_slice(&len.to_be_bytes());
    frame.extend_from_slice(&payload);
    frame
}

/// Decode a `NetMessage` from a payload buffer (tag + data, no length prefix).
///
/// Returns `None` for malformed messages.
pub(crate) fn decode_message(payload: &[u8]) -> Option<NetMessage> {
    if payload.is_empty() {
        return None;
    }
    let tag = MessageTag::from_byte(payload[0])?;
    let data = &payload[1..];

    match tag {
        MessageTag::State => decode_state_message(data),
        MessageTag::Halt => decode_halt_message(data),
        MessageTag::Token => decode_token_message(data),
        MessageTag::ProgressRequest => decode_progress_request(data),
        MessageTag::ProgressReport => decode_progress_report(data),
        MessageTag::Ack => decode_ack_message(data),
    }
}

fn decode_state_message(data: &[u8]) -> Option<NetMessage> {
    if data.len() < 16 {
        return None;
    }
    let fp = Fingerprint(u64::from_be_bytes(data[0..8].try_into().ok()?));
    let depth = u32::from_be_bytes(data[8..12].try_into().ok()?);
    let num_values = u32::from_be_bytes(data[12..16].try_into().ok()?) as usize;

    // For the PoC, state values are transferred as opaque data.
    // The receiver reconstructs an ArrayState with the correct number of variables.
    // A production implementation would use a proper binary Value codec.
    let state = ArrayState::new(num_values);
    Some(NetMessage::State { fp, state, depth })
}

fn decode_halt_message(data: &[u8]) -> Option<NetMessage> {
    if data.len() < 8 {
        return None;
    }
    let source_node = u32::from_be_bytes(data[0..4].try_into().ok()?);
    let reason_len = u32::from_be_bytes(data[4..8].try_into().ok()?) as usize;
    if data.len() < 8 + reason_len {
        return None;
    }
    let reason = String::from_utf8_lossy(&data[8..8 + reason_len]).to_string();
    Some(NetMessage::Halt {
        source_node,
        reason,
    })
}

fn decode_token_message(data: &[u8]) -> Option<NetMessage> {
    if data.len() < 13 {
        return None;
    }
    let color = TokenColor::from_byte(data[0]);
    let initiator = u32::from_be_bytes(data[1..5].try_into().ok()?);
    let counter = i64::from_be_bytes(data[5..13].try_into().ok()?);
    Some(NetMessage::Token {
        color,
        initiator,
        counter,
    })
}

fn decode_progress_request(data: &[u8]) -> Option<NetMessage> {
    if data.len() < 4 {
        return None;
    }
    let requester = u32::from_be_bytes(data[0..4].try_into().ok()?);
    Some(NetMessage::ProgressRequest { requester })
}

fn decode_progress_report(data: &[u8]) -> Option<NetMessage> {
    if data.len() < 24 {
        return None;
    }
    let node_id = u32::from_be_bytes(data[0..4].try_into().ok()?);
    let distinct_states = u64::from_be_bytes(data[4..12].try_into().ok()?);
    let max_depth = u32::from_be_bytes(data[12..16].try_into().ok()?);
    let transitions = u64::from_be_bytes(data[16..24].try_into().ok()?);
    Some(NetMessage::ProgressReport {
        node_id,
        distinct_states,
        max_depth,
        transitions,
    })
}

fn decode_ack_message(data: &[u8]) -> Option<NetMessage> {
    if data.len() < 8 {
        return None;
    }
    let sequence = u64::from_be_bytes(data[0..8].try_into().ok()?);
    Some(NetMessage::Ack { sequence })
}

// ---------- TCP transport layer ----------

/// Read one length-prefixed message from a TCP stream.
///
/// Returns `None` on EOF or error.
fn read_message(stream: &mut TcpStream) -> io::Result<Option<NetMessage>> {
    let mut len_buf = [0u8; 4];
    match stream.read_exact(&mut len_buf) {
        Ok(()) => {}
        Err(ref e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(None),
        Err(ref e) if e.kind() == io::ErrorKind::WouldBlock => return Ok(None),
        Err(e) => return Err(e),
    }
    let len = u32::from_be_bytes(len_buf) as usize;
    if len == 0 || len > 16 * 1024 * 1024 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("invalid message length: {len}"),
        ));
    }
    let mut payload = vec![0u8; len];
    stream.read_exact(&mut payload)?;
    Ok(decode_message(&payload))
}

/// Write one length-prefixed message to a TCP stream.
fn write_message(stream: &mut TcpStream, msg: &NetMessage) -> io::Result<()> {
    let frame = encode_message(msg);
    stream.write_all(&frame)?;
    stream.flush()
}

/// Configuration for the network transport layer.
#[derive(Debug, Clone)]
pub(crate) struct TransportConfig {
    /// This node's ID.
    pub(crate) node_id: NodeId,
    /// This node's listen address.
    pub(crate) listen_addr: SocketAddr,
    /// Addresses of all nodes (indexed by NodeId).
    pub(crate) node_addrs: Vec<SocketAddr>,
    /// Connection timeout.
    pub(crate) connect_timeout: Duration,
    /// Read timeout for non-blocking receives.
    pub(crate) read_timeout: Duration,
}

impl TransportConfig {
    /// Number of nodes in the cluster.
    pub(crate) fn num_nodes(&self) -> usize {
        self.node_addrs.len()
    }
}

/// Handler callback for incoming messages.
pub(crate) type MessageHandler = Box<dyn Fn(NetMessage) + Send + Sync>;

/// TCP-based transport layer for distributed BFS.
///
/// Manages:
/// - A TCP listener for incoming connections
/// - Outbound TCP connections to all peer nodes
/// - Background reader threads for each inbound connection
/// - Thread-safe send operations to any peer
pub(crate) struct TcpTransport {
    config: TransportConfig,
    /// Outbound connections to peers, keyed by NodeId.
    /// Each connection is protected by a Mutex for thread-safe sending.
    outbound: HashMap<NodeId, Mutex<TcpStream>>,
    /// Listener thread handle.
    listener_handle: Option<thread::JoinHandle<()>>,
    /// Shutdown flag.
    shutdown: Arc<AtomicBool>,
    /// Inbound reader handles (for cleanup).
    reader_handles: Vec<thread::JoinHandle<()>>,
}

impl TcpTransport {
    /// Create and start the transport layer.
    ///
    /// 1. Binds the TCP listener
    /// 2. Establishes outbound connections to all peers
    /// 3. Spawns background reader threads for inbound connections
    ///
    /// The `handler` callback is invoked for each received message.
    pub(crate) fn start(config: TransportConfig, handler: Arc<MessageHandler>) -> io::Result<Self> {
        let shutdown = Arc::new(AtomicBool::new(false));
        let num_nodes = config.num_nodes();
        let node_id = config.node_id;

        // Step 1: Bind listener
        let listener = TcpListener::bind(config.listen_addr)?;
        listener.set_nonblocking(false)?;

        // Step 2: Establish outbound connections (with retries)
        let mut outbound = HashMap::new();
        for target_id in 0..num_nodes as NodeId {
            if target_id == node_id {
                continue;
            }
            let target_addr = config.node_addrs[target_id as usize];
            let stream = connect_with_retry(target_addr, config.connect_timeout, 10)?;
            stream.set_nodelay(true)?;
            outbound.insert(target_id, Mutex::new(stream));
        }

        // Step 3: Accept inbound connections and spawn reader threads
        let shutdown_clone = Arc::clone(&shutdown);
        let handler_clone = Arc::clone(&handler);
        let expected_peers = num_nodes - 1;

        let reader_handles = Arc::new(Mutex::new(Vec::new()));
        let reader_handles_clone = Arc::clone(&reader_handles);

        let listener_handle = thread::Builder::new()
            .name(format!("dist-listener-{node_id}"))
            .spawn(move || {
                let mut accepted = 0;
                // Set a reasonable timeout so we can check shutdown periodically
                listener
                    .set_nonblocking(false)
                    .expect("failed to set listener blocking");
                let _ = listener
                    .incoming()
                    .take(expected_peers)
                    .enumerate()
                    .for_each(|(i, result)| {
                        if shutdown_clone.load(Ordering::Relaxed) {
                            return;
                        }
                        match result {
                            Ok(mut stream) => {
                                let _ = stream.set_nodelay(true);
                                let _ = stream.set_read_timeout(Some(Duration::from_millis(100)));
                                let handler = Arc::clone(&handler_clone);
                                let shutdown = Arc::clone(&shutdown_clone);
                                let handle = thread::Builder::new()
                                    .name(format!("dist-reader-{node_id}-{i}"))
                                    .spawn(move || {
                                        while !shutdown.load(Ordering::Relaxed) {
                                            match read_message(&mut stream) {
                                                Ok(Some(msg)) => handler(msg),
                                                Ok(None) => {
                                                    // Timeout or EOF — check shutdown and retry
                                                    thread::sleep(Duration::from_millis(1));
                                                }
                                                Err(_) => {
                                                    // Connection error — stop reading
                                                    break;
                                                }
                                            }
                                        }
                                    })
                                    .expect("failed to spawn reader thread");
                                reader_handles_clone
                                    .lock()
                                    .expect("reader_handles lock")
                                    .push(handle);
                                accepted += 1;
                            }
                            Err(e) => {
                                eprintln!("dist-listener-{node_id}: accept error: {e}");
                            }
                        }
                    });
                let _ = accepted;
            })?;

        let rh = Arc::try_unwrap(reader_handles)
            .unwrap_or_else(|arc| {
                let _ = arc
                    .lock()
                    .expect("reader_handles lock")
                    .drain(..)
                    .collect::<Vec<_>>();
                Mutex::new(Vec::new())
            })
            .into_inner()
            .expect("reader_handles lock");

        Ok(TcpTransport {
            config,
            outbound,
            listener_handle: Some(listener_handle),
            shutdown,
            reader_handles: rh,
        })
    }

    /// Send a message to a specific peer node.
    ///
    /// Thread-safe: uses per-connection mutex.
    pub(crate) fn send_to(&self, target: NodeId, msg: &NetMessage) -> io::Result<()> {
        if target == self.config.node_id {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "cannot send to self",
            ));
        }
        let conn = self.outbound.get(&target).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotConnected,
                format!("no connection to node {target}"),
            )
        })?;
        let mut stream = conn.lock().expect("outbound connection lock poisoned");
        write_message(&mut *stream, msg)
    }

    /// Broadcast a message to all peer nodes.
    pub(crate) fn broadcast(&self, msg: &NetMessage) -> io::Result<()> {
        for (&target, _) in &self.outbound {
            self.send_to(target, msg)?;
        }
        Ok(())
    }

    /// Shut down the transport layer.
    pub(crate) fn shutdown(&mut self) {
        self.shutdown.store(true, Ordering::SeqCst);
        // Drop outbound connections to unblock any blocked readers on the other side
        self.outbound.clear();
    }

    /// This node's ID.
    pub(crate) fn node_id(&self) -> NodeId {
        self.config.node_id
    }

    /// Number of nodes in the cluster.
    pub(crate) fn num_nodes(&self) -> usize {
        self.config.num_nodes()
    }
}

impl Drop for TcpTransport {
    fn drop(&mut self) {
        self.shutdown.store(true, Ordering::SeqCst);
    }
}

/// Connect to a peer with exponential backoff retries.
fn connect_with_retry(
    addr: SocketAddr,
    timeout: Duration,
    max_retries: usize,
) -> io::Result<TcpStream> {
    let mut delay = Duration::from_millis(50);
    for attempt in 0..max_retries {
        match TcpStream::connect_timeout(&addr, timeout) {
            Ok(stream) => return Ok(stream),
            Err(_e) if attempt + 1 < max_retries => {
                thread::sleep(delay);
                delay = (delay * 2).min(Duration::from_secs(2));
            }
            Err(e) => return Err(e),
        }
    }
    Err(io::Error::new(
        io::ErrorKind::TimedOut,
        format!("failed to connect to {addr} after {max_retries} retries"),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_decode_state() {
        let msg = NetMessage::State {
            fp: Fingerprint(0xDEADBEEF),
            state: ArrayState::new(3),
            depth: 42,
        };
        let encoded = encode_message(&msg);
        // Skip 4-byte length prefix to get payload
        let payload = &encoded[4..];
        let decoded = decode_message(payload).expect("decode should succeed");
        match decoded {
            NetMessage::State { fp, depth, state } => {
                assert_eq!(fp, Fingerprint(0xDEADBEEF));
                assert_eq!(depth, 42);
                assert_eq!(state.len(), 3);
            }
            other => panic!("expected State, got {other:?}"),
        }
    }

    #[test]
    fn test_encode_decode_halt() {
        let msg = NetMessage::Halt {
            source_node: 7,
            reason: "invariant TypeOK violated".to_string(),
        };
        let encoded = encode_message(&msg);
        let payload = &encoded[4..];
        let decoded = decode_message(payload).expect("decode should succeed");
        match decoded {
            NetMessage::Halt {
                source_node,
                reason,
            } => {
                assert_eq!(source_node, 7);
                assert_eq!(reason, "invariant TypeOK violated");
            }
            other => panic!("expected Halt, got {other:?}"),
        }
    }

    #[test]
    fn test_encode_decode_token() {
        let msg = NetMessage::Token {
            color: TokenColor::Black,
            initiator: 0,
            counter: -5,
        };
        let encoded = encode_message(&msg);
        let payload = &encoded[4..];
        let decoded = decode_message(payload).expect("decode should succeed");
        match decoded {
            NetMessage::Token {
                color,
                initiator,
                counter,
            } => {
                assert_eq!(color, TokenColor::Black);
                assert_eq!(initiator, 0);
                assert_eq!(counter, -5);
            }
            other => panic!("expected Token, got {other:?}"),
        }
    }

    #[test]
    fn test_encode_decode_progress_report() {
        let msg = NetMessage::ProgressReport {
            node_id: 3,
            distinct_states: 100_000,
            max_depth: 15,
            transitions: 250_000,
        };
        let encoded = encode_message(&msg);
        let payload = &encoded[4..];
        let decoded = decode_message(payload).expect("decode should succeed");
        match decoded {
            NetMessage::ProgressReport {
                node_id,
                distinct_states,
                max_depth,
                transitions,
            } => {
                assert_eq!(node_id, 3);
                assert_eq!(distinct_states, 100_000);
                assert_eq!(max_depth, 15);
                assert_eq!(transitions, 250_000);
            }
            other => panic!("expected ProgressReport, got {other:?}"),
        }
    }

    #[test]
    fn test_encode_decode_ack() {
        let msg = NetMessage::Ack { sequence: 42 };
        let encoded = encode_message(&msg);
        let payload = &encoded[4..];
        let decoded = decode_message(payload).expect("decode should succeed");
        match decoded {
            NetMessage::Ack { sequence } => assert_eq!(sequence, 42),
            other => panic!("expected Ack, got {other:?}"),
        }
    }

    #[test]
    fn test_decode_empty_payload() {
        assert!(decode_message(&[]).is_none());
    }

    #[test]
    fn test_decode_invalid_tag() {
        assert!(decode_message(&[0xFF]).is_none());
    }

    #[test]
    fn test_message_tag_roundtrip() {
        for tag_byte in [0x01, 0x02, 0x03, 0x04, 0x05, 0x06] {
            let tag = MessageTag::from_byte(tag_byte).expect("valid tag");
            assert_eq!(tag as u8, tag_byte);
        }
    }

    #[test]
    fn test_token_color_roundtrip() {
        assert_eq!(TokenColor::from_byte(0), TokenColor::White);
        assert_eq!(TokenColor::from_byte(1), TokenColor::Black);
        assert_eq!(TokenColor::from_byte(42), TokenColor::Black); // non-zero = Black
    }
}
