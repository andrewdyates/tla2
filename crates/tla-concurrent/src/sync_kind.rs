// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Synchronization primitive types.

use serde::{Deserialize, Serialize};

use crate::model::SyncId;

/// A synchronization primitive instance in the model.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SyncPrimitive {
    /// Unique identifier.
    pub id: SyncId,
    /// The kind of synchronization primitive.
    pub kind: SyncKind,
    /// Human-readable name (e.g., Rust variable name).
    pub name: Option<String>,
}

/// Kind of synchronization primitive.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum SyncKind {
    /// `std::sync::Mutex` or `parking_lot::Mutex`.
    Mutex {
        /// Whether this mutex supports reentrant locking (parking_lot).
        reentrant: bool,
        /// Whether this mutex can be poisoned (std::sync only).
        poisonable: bool,
    },
    /// `std::sync::RwLock` or `parking_lot::RwLock`.
    RwLock {
        /// Whether this rwlock can be poisoned (std::sync only).
        poisonable: bool,
    },
    /// `std::sync::Condvar`.
    Condvar {
        /// Dynamically associated mutex (resolved at `wait()` call site).
        associated_mutex: Option<SyncId>,
    },
    /// `std::sync::Barrier`.
    Barrier {
        /// Number of threads that must reach the barrier.
        count: usize,
    },
    /// `std::sync::Once` or `std::sync::OnceLock`.
    Once,
    /// A channel (mpsc, sync_channel, crossbeam).
    Channel {
        /// Channel semantics.
        kind: ChannelKind,
        /// Buffer capacity (None = unbounded).
        capacity: Option<usize>,
    },
}

/// Channel semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChannelKind {
    /// `std::sync::mpsc::channel` — multiple producers, single consumer, unbounded.
    Mpsc,
    /// `std::sync::mpsc::sync_channel` — bounded, rendezvous at capacity 0.
    SyncChannel,
    /// `crossbeam::channel` — multi-producer, multi-consumer.
    Crossbeam,
}
