// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core concurrent model types: processes, shared state, access sites.

use serde::{Deserialize, Serialize};

use crate::assumptions::Assumptions;
use crate::property::Property;
use crate::source_map::SourceMap;
use crate::sync_kind::SyncPrimitive;
use crate::transition::Transition;

/// Unique identifier for a process (thread).
pub type ProcessId = String;

/// Unique identifier for a sync primitive instance.
pub type SyncId = String;

/// Unique identifier for a state in a process's transition graph.
pub type StateId = String;

/// Unique identifier for a linearizable object (distinct from SyncId).
pub type ObjectId = String;

/// The complete concurrent model extracted from Rust MIR by tRust.
///
/// This is the contract between the extractor (tRust) and the checker (TLA2).
/// It is serialized as JSON and passed via the `tla2 thread-check` CLI.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConcurrentModel {
    /// All processes (threads) in the model.
    pub processes: Vec<Process>,
    /// Shared variables accessed by multiple processes.
    pub shared_vars: Vec<SharedVar>,
    /// Synchronization primitives (mutexes, rwlocks, condvars, channels, etc.).
    pub sync_primitives: Vec<SyncPrimitive>,
    /// Properties to verify (default + opt-in).
    pub properties: Vec<Property>,
    /// Assumptions under which verification is performed.
    pub assumptions: Assumptions,
    /// Mapping from TLA+ states/transitions to Rust source locations.
    pub source_map: SourceMap,
}

/// A process (thread) in the concurrent model.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Process {
    /// Unique identifier for this process.
    pub id: ProcessId,
    /// How this process was created.
    pub kind: ProcessKind,
    /// Process-local variables.
    pub local_vars: Vec<LocalVar>,
    /// Transitions in this process's state machine.
    pub transitions: Vec<Transition>,
    /// Initial state of this process.
    pub initial_state: StateId,
    /// Terminal (completed) states.
    pub terminal_states: Vec<StateId>,
}

/// How a process was spawned.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum ProcessKind {
    /// The main thread.
    Main,
    /// A thread created via `thread::spawn` or `Builder::spawn`.
    Spawned {
        /// The parent process that spawned this thread.
        parent: ProcessId,
        /// The JoinHandle variable in the parent's frame, if captured.
        join_handle_in_parent: Option<JoinHandleRef>,
    },
    /// A scoped thread created via `Scope::spawn`.
    Scoped {
        /// The scope identifier.
        scope_id: String,
        /// Variables borrowed from the parent's stack frame.
        borrowed_captures: Vec<String>,
    },
}

/// Reference to a JoinHandle in the parent process's frame.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JoinHandleRef {
    /// The DefId of the parent frame.
    pub parent_def_id: String,
    /// The MIR Local index.
    pub local: String,
}

/// A process-local variable.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LocalVar {
    pub name: String,
    pub initial_value: Option<String>,
}

/// A shared variable accessed by multiple processes.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SharedVar {
    /// Variable name.
    pub name: String,
    /// Field-sensitive path (e.g., `["data", "counter"]`).
    pub field_path: Vec<String>,
    /// Initial value expression (TLA+ syntax).
    pub initial_value: Option<String>,
    /// All access sites across all processes.
    pub access_sites: Vec<AccessSite>,
}

/// A location where a shared variable is accessed.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AccessSite {
    /// Which process performs this access.
    pub process: ProcessId,
    /// Read, Write, or Read-Modify-Write.
    pub kind: AccessKind,
    /// Guards held at this access point.
    pub guards_held: Vec<HeldGuard>,
    /// The program counter state at which this access occurs.
    /// When `Some`, the DataRaceFreedom invariant is conditioned on
    /// `pc[process] = state_id`, avoiding false positives when guards are
    /// released and re-acquired across different program states.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub state_id: Option<StateId>,
    /// Rust source location.
    pub source_file: Option<String>,
    pub source_line: Option<u32>,
    pub source_col: Option<u32>,
}

/// Kind of access to a shared variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum AccessKind {
    Read,
    Write,
    ReadModifyWrite,
}

/// A guard held during a shared variable access.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HeldGuard {
    /// The sync primitive this guard belongs to.
    pub sync_id: SyncId,
    /// The mode of the guard (exclusive, shared read, etc.).
    pub mode: GuardMode,
}

/// Guard acquisition mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum GuardMode {
    /// Mutex exclusive lock.
    MutexExclusive,
    /// RwLock shared read lock.
    RwLockRead,
    /// RwLock exclusive write lock.
    RwLockWrite,
    /// RwLock upgradable read lock (parking_lot).
    RwLockUpgradableRead,
}
