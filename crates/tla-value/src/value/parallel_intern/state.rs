// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared state, globals, and TLS worker overlay definitions for parallel interning.
//!
//! Part of #3412: extracted from `parallel_intern.rs` (lines 44-125).

use rustc_hash::FxHashMap;
use std::cell::{Cell, RefCell};
use std::sync::atomic::{AtomicBool, AtomicU32};
use std::sync::{Arc, Mutex};

use super::super::Value;

/// Global flag: true when parallel interning is active.
/// Checked on the hot path with `Relaxed` ordering (~1ns atomic read).
pub(crate) static PARALLEL_INTERN_ACTIVE: AtomicBool = AtomicBool::new(false);

/// Global flag: true when shared values may read cache fields but must not
/// write them back. Used to disable `AtomicU64` cache-line bouncing during
/// parallel BFS without changing fingerprint results.
pub(crate) static PARALLEL_READONLY_VALUE_CACHES_ACTIVE: AtomicBool = AtomicBool::new(false);

/// Frozen snapshots of the optimization-only intern tables.
/// Immutable after creation; shared across workers via Arc.
pub(super) struct FrozenValueInterners {
    pub(super) sets: FxHashMap<u64, Arc<[Value]>>,
    pub(super) int_funcs: FxHashMap<u64, Arc<Vec<Value>>>,
    /// Part of #3285: Frozen snapshot of STRING_INTERN_TABLE.
    pub(super) strings: FxHashMap<String, Arc<str>>,
    /// Part of #3285: Frozen snapshot of TLC_STRING_TOKENS.
    pub(super) string_tokens: FxHashMap<Arc<str>, u32>,
}

/// Global storage for the frozen snapshot, accessible to workers during install.
pub(super) static FROZEN_SNAPSHOT: Mutex<Option<Arc<FrozenValueInterners>>> = Mutex::new(None);

/// Worker-local token counter for TLC string tokens.
/// Each worker assigns tokens from a high range that won't collide with the frozen
/// snapshot tokens. Workers start at the frozen counter value and increment locally.
/// Token ordering consistency across workers is not required because TLC_STRING_TOKENS
/// is an append-only registry and worker-local tokens are only for new strings
/// first seen during parallel BFS.
pub(super) static WORKER_TOKEN_COUNTER: AtomicU32 = AtomicU32::new(1);

/// Per-worker intern attribution counters.
///
/// Part of #3285: tracks where intern lookups resolve (frozen vs overlay vs new insert)
/// to determine whether remaining eval overhead is in the interner or elsewhere.
/// Counters are `u64` to avoid overflow on large specs (MCKVSSafetySmall: 56M transitions).
#[derive(Debug, Clone, Default)]
pub struct InternAttributionCounters {
    pub frozen_string_hits: u64,
    pub frozen_token_hits: u64,
    pub frozen_set_hits: u64,
    pub frozen_int_func_hits: u64,
    pub overlay_string_hits: u64,
    pub overlay_token_hits: u64,
    pub overlay_set_hits: u64,
    pub overlay_int_func_hits: u64,
    pub new_string_inserts: u64,
    pub new_set_inserts: u64,
    pub new_int_func_inserts: u64,
}

/// Per-worker interning state: frozen snapshot reference + local overlay maps.
///
/// Attribution counters use `Cell<u64>` so they can be incremented during shared
/// borrows on the hot path (overlay/frozen hit returns) without restructuring
/// the borrow pattern. Zero runtime overhead since `Cell` is transparent for
/// `Copy` types.
pub(super) struct WorkerInternState {
    pub(super) frozen: Arc<FrozenValueInterners>,
    pub(super) set_overlay: FxHashMap<u64, Arc<[Value]>>,
    pub(super) int_func_overlay: FxHashMap<u64, Arc<Vec<Value>>>,
    /// Part of #3285: Worker-local overlay for string interning.
    pub(super) string_overlay: FxHashMap<String, Arc<str>>,
    /// Part of #3285: Worker-local overlay for TLC string tokens.
    pub(super) string_token_overlay: FxHashMap<Arc<str>, u32>,
    // Part of #3285: Attribution counters (Cell for increment during shared borrow)
    pub(super) frozen_string_hits: Cell<u64>,
    pub(super) frozen_token_hits: Cell<u64>,
    pub(super) frozen_set_hits: Cell<u64>,
    pub(super) frozen_int_func_hits: Cell<u64>,
    pub(super) overlay_string_hits: Cell<u64>,
    pub(super) overlay_token_hits: Cell<u64>,
    pub(super) overlay_set_hits: Cell<u64>,
    pub(super) overlay_int_func_hits: Cell<u64>,
    pub(super) new_string_inserts: Cell<u64>,
    pub(super) new_set_inserts: Cell<u64>,
    pub(super) new_int_func_inserts: Cell<u64>,
}

thread_local! {
    pub(super) static WORKER_INTERN: RefCell<Option<WorkerInternState>> = const { RefCell::new(None) };
}
