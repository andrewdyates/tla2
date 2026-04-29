// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Transition types: the 54-variant `TransitionKind` enum covering all
//! concurrent operations extracted from Rust MIR.

use serde::{Deserialize, Serialize};

use crate::model::{GuardMode, ProcessId, StateId, SyncId};

/// A transition in a process's state machine.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transition {
    /// Source state.
    pub from: StateId,
    /// Target state.
    pub to: StateId,
    /// The concurrent operation this transition represents.
    pub kind: TransitionKind,
    /// Index into the source map for this transition.
    pub source_map_index: Option<usize>,
}

/// All concurrent operations that can be extracted from Rust MIR.
///
/// 54 variants covering: thread lifecycle, mutex, rwlock, atomics,
/// channels, condvar, barrier, once, park/unpark, panic.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum TransitionKind {
    // ── Thread Lifecycle ──────────────────────────────────────────
    /// `thread::spawn` or `Builder::spawn` — creates a new process.
    Spawn { child: ProcessId },
    /// `JoinHandle::join()` — successful join, child exited normally.
    JoinOk { child: ProcessId },
    /// `JoinHandle::join()` — child panicked.
    JoinErr { child: ProcessId },
    /// Scoped thread scope exits — all scoped threads must have joined.
    ScopeEnd { scope_id: String },

    // ── Mutex Operations ─────────────────────────────────────────
    /// `Mutex::lock()` — blocking acquire.
    Lock { mutex: SyncId },
    /// `Mutex::try_lock()` — non-blocking, succeeded (returns `TryLockResult`).
    TryLockOk { mutex: SyncId },
    /// `Mutex::try_lock()` — non-blocking, failed (mutex held by another).
    TryLockErr { mutex: SyncId },
    /// Drop of `MutexGuard` — releases the lock.
    Unlock { mutex: SyncId },
    /// Lock on a poisoned mutex — handler present (`.into_inner()` or match).
    LockPoisonOk { mutex: SyncId },
    /// Lock on a poisoned mutex — no handler, propagates panic.
    LockPoisonPanic { mutex: SyncId },

    // ── RwLock Operations ────────────────────────────────────────
    /// `RwLock::read()` — acquire shared read lock.
    ReadLock { rwlock: SyncId },
    /// `RwLock::write()` — acquire exclusive write lock.
    WriteLock { rwlock: SyncId },
    /// `RwLock::try_read()` — succeeded.
    TryReadOk { rwlock: SyncId },
    /// `RwLock::try_read()` — failed.
    TryReadErr { rwlock: SyncId },
    /// `RwLock::try_write()` — succeeded.
    TryWriteOk { rwlock: SyncId },
    /// `RwLock::try_write()` — failed.
    TryWriteErr { rwlock: SyncId },
    /// Drop of `RwLockReadGuard`.
    ReadUnlock { rwlock: SyncId },
    /// Drop of `RwLockWriteGuard`.
    WriteUnlock { rwlock: SyncId },
    /// `parking_lot::RwLock::upgradable_read()`.
    UpgradableReadLock { rwlock: SyncId },
    /// `RwLockUpgradableReadGuard::upgrade()`.
    UpgradeToWrite { rwlock: SyncId },
    /// `RwLockWriteGuard::downgrade()`.
    DowngradeToRead { rwlock: SyncId },

    // ── Atomic Operations ────────────────────────────────────────
    /// `AtomicT::load(ordering)`.
    AtomicLoad {
        variable: String,
        ordering: MemoryOrdering,
    },
    /// `AtomicT::store(val, ordering)`.
    AtomicStore {
        variable: String,
        ordering: MemoryOrdering,
    },
    /// `AtomicT::fetch_add/sub/and/or/xor/nand/max/min/swap(val, ordering)`.
    AtomicRmw {
        variable: String,
        op: AtomicOp,
        ordering: MemoryOrdering,
    },
    /// `AtomicT::compare_exchange` — succeeded.
    CasOk { variable: String, info: CasInfo },
    /// `AtomicT::compare_exchange` — failed.
    CasFail { variable: String, info: CasInfo },
    /// `std::sync::atomic::fence(ordering)`.
    Fence { ordering: MemoryOrdering },

    // ── Channel Operations ───────────────────────────────────────
    /// `Sender::send(msg)` — successful send.
    ChannelSend { channel: SyncId },
    /// `Sender::send(msg)` — receiver disconnected.
    ChannelSendErr { channel: SyncId },
    /// `Receiver::recv()` — successful receive.
    ChannelRecv { channel: SyncId },
    /// `Receiver::recv()` — all senders disconnected.
    ChannelRecvDisconnected { channel: SyncId },
    /// `Receiver::try_recv()` — got a message.
    TryRecvOk { channel: SyncId },
    /// `Receiver::try_recv()` — channel empty.
    TryRecvEmpty { channel: SyncId },
    /// `Receiver::try_recv()` — all senders disconnected.
    TryRecvDisconnected { channel: SyncId },
    /// Last `Sender` clone dropped.
    SenderDrop { channel: SyncId },
    /// `Receiver` dropped.
    ReceiverDrop { channel: SyncId },

    // ── Condvar Operations (Two-Transition Model) ────────────────
    /// `Condvar::wait()` phase 1: release mutex + enter wait set.
    CondvarWaitRelease { condvar: SyncId, mutex: SyncId },
    /// `Condvar::wait()` phase 2: leave wait set + reacquire mutex.
    CondvarWaitReacquire { condvar: SyncId, mutex: SyncId },
    /// Spurious wakeup: always-enabled reacquire for waiting processes.
    SpuriousWake { condvar: SyncId, mutex: SyncId },
    /// `Condvar::notify_one()`.
    NotifyOne { condvar: SyncId },
    /// `Condvar::notify_all()`.
    NotifyAll { condvar: SyncId },
    /// `Condvar::wait_timeout()` expired without notification.
    WaitTimeoutExpired { condvar: SyncId, mutex: SyncId },

    // ── Barrier ──────────────────────────────────────────────────
    /// `Barrier::wait()` — blocks until all threads arrive.
    BarrierWait { barrier: SyncId },

    // ── Once / OnceLock ──────────────────────────────────────────
    /// `Once::call_once()` — executes the closure exactly once.
    OnceCallOnce { once: SyncId },
    /// `OnceLock::set()` — sets the value exactly once.
    OnceLockSet { once: SyncId },

    // ── Park / Unpark ────────────────────────────────────────────
    /// `thread::park()` — suspends the current thread.
    Park,
    /// `Thread::unpark()` — unblocks a parked thread.
    Unpark { target: ProcessId },

    // ── Panic / Unwind ───────────────────────────────────────────
    /// Thread panics, dropping all held guards (with correct poisoning).
    Panic {
        /// Guards held at the point of panic, with their modes.
        /// Mutex guards always poison; RwLock only write guards poison.
        guards: Vec<PanicGuard>,
    },

    // ── Internal (no-op transition for sequencing) ───────────────
    /// A no-op transition used for state machine sequencing.
    Internal { label: Option<String> },
}

impl TransitionKind {
    /// Human-readable tag string for this transition kind.
    ///
    /// Used by source mapping to label counterexample steps.
    #[must_use]
    pub fn tag(&self) -> &'static str {
        match self {
            TransitionKind::Spawn { .. } => "spawn",
            TransitionKind::JoinOk { .. } => "join_ok",
            TransitionKind::JoinErr { .. } => "join_err",
            TransitionKind::ScopeEnd { .. } => "scope_end",
            TransitionKind::Lock { .. } => "lock",
            TransitionKind::TryLockOk { .. } => "try_lock_ok",
            TransitionKind::TryLockErr { .. } => "try_lock_err",
            TransitionKind::Unlock { .. } => "unlock",
            TransitionKind::LockPoisonOk { .. } => "lock_poison_ok",
            TransitionKind::LockPoisonPanic { .. } => "lock_poison_panic",
            TransitionKind::ReadLock { .. } => "read_lock",
            TransitionKind::WriteLock { .. } => "write_lock",
            TransitionKind::TryReadOk { .. } => "try_read_ok",
            TransitionKind::TryReadErr { .. } => "try_read_err",
            TransitionKind::TryWriteOk { .. } => "try_write_ok",
            TransitionKind::TryWriteErr { .. } => "try_write_err",
            TransitionKind::ReadUnlock { .. } => "read_unlock",
            TransitionKind::WriteUnlock { .. } => "write_unlock",
            TransitionKind::UpgradableReadLock { .. } => "upgradable_read_lock",
            TransitionKind::UpgradeToWrite { .. } => "upgrade_to_write",
            TransitionKind::DowngradeToRead { .. } => "downgrade_to_read",
            TransitionKind::AtomicLoad { .. } => "atomic_load",
            TransitionKind::AtomicStore { .. } => "atomic_store",
            TransitionKind::AtomicRmw { .. } => "atomic_rmw",
            TransitionKind::CasOk { .. } => "cas_ok",
            TransitionKind::CasFail { .. } => "cas_fail",
            TransitionKind::Fence { .. } => "fence",
            TransitionKind::ChannelSend { .. } => "channel_send",
            TransitionKind::ChannelSendErr { .. } => "channel_send_err",
            TransitionKind::ChannelRecv { .. } => "channel_recv",
            TransitionKind::ChannelRecvDisconnected { .. } => "channel_recv_disconnected",
            TransitionKind::TryRecvOk { .. } => "try_recv_ok",
            TransitionKind::TryRecvEmpty { .. } => "try_recv_empty",
            TransitionKind::TryRecvDisconnected { .. } => "try_recv_disconnected",
            TransitionKind::SenderDrop { .. } => "sender_drop",
            TransitionKind::ReceiverDrop { .. } => "receiver_drop",
            TransitionKind::CondvarWaitRelease { .. } => "condvar_wait_release",
            TransitionKind::CondvarWaitReacquire { .. } => "condvar_wait_reacquire",
            TransitionKind::SpuriousWake { .. } => "spurious_wake",
            TransitionKind::NotifyOne { .. } => "notify_one",
            TransitionKind::NotifyAll { .. } => "notify_all",
            TransitionKind::WaitTimeoutExpired { .. } => "wait_timeout_expired",
            TransitionKind::BarrierWait { .. } => "barrier_wait",
            TransitionKind::OnceCallOnce { .. } => "once_call_once",
            TransitionKind::OnceLockSet { .. } => "once_lock_set",
            TransitionKind::Park => "park",
            TransitionKind::Unpark { .. } => "unpark",
            TransitionKind::Panic { .. } => "panic",
            TransitionKind::Internal { .. } => "internal",
        }
    }
}

/// Atomic read-modify-write operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum AtomicOp {
    Add,
    Sub,
    And,
    Or,
    Xor,
    Nand,
    Max,
    Min,
    Swap,
}

/// Memory ordering for atomic operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum MemoryOrdering {
    Relaxed,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
}

/// Compare-and-swap operation details.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CasInfo {
    /// Expected value expression.
    pub expected: String,
    /// New value expression.
    pub new_value: String,
    /// Whether this is a weak CAS (may spuriously fail).
    pub weak: bool,
    /// Ordering on success.
    pub success_ordering: MemoryOrdering,
    /// Ordering on failure.
    pub failure_ordering: MemoryOrdering,
}

/// A guard held at the point of panic, for correct poisoning semantics.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PanicGuard {
    /// The sync primitive.
    pub sync_id: SyncId,
    /// Guard mode — determines whether poisoning occurs.
    /// Mutex: always poisons. RwLock: only Write poisons (Read does not).
    pub mode: GuardMode,
}
