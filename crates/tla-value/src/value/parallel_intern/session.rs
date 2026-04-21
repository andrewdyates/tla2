// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Session lifecycle management: freeze/unfreeze, preload, install/uninstall,
//! `WorkerInternGuard`, and attribution counter reads.
//!
//! Part of #3412: extracted from `parallel_intern.rs` (lines 127-362).

use rustc_hash::FxHashMap;
use std::cell::Cell;
use std::sync::atomic::Ordering;
use std::sync::{Arc, OnceLock};

use super::super::{intern_tables, strings, Value};
use super::state::{
    FrozenValueInterners, InternAttributionCounters, WorkerInternState, FROZEN_SNAPSHOT,
    PARALLEL_INTERN_ACTIVE, PARALLEL_READONLY_VALUE_CACHES_ACTIVE, WORKER_INTERN,
    WORKER_TOKEN_COUNTER,
};

/// Returns true if parallel intern mode is active.
///
/// Checked by `intern_set_array()` and `intern_int_func_array()` on the hot path.
/// Uses `Relaxed` ordering because this is a mode flag, not a data guard.
#[inline]
pub(in crate::value) fn is_parallel_intern_active() -> bool {
    PARALLEL_INTERN_ACTIVE.load(Ordering::Relaxed)
}

/// Snapshot all global intern tables into immutable FxHashMaps.
///
/// Call on the main thread after parsing is complete and before spawning BFS
/// workers. This makes the snapshot available for workers to clone via
/// [`install_worker_intern_scope()`].
///
/// Covers: SET_INTERN_TABLE, INT_FUNC_INTERN_TABLE, STRING_INTERN_TABLE,
/// TLC_STRING_TOKENS. Part of #3285.
pub(crate) fn freeze_value_interners() {
    let frozen = Arc::new(FrozenValueInterners {
        sets: intern_tables::snapshot_set_intern_table(),
        int_funcs: intern_tables::snapshot_int_func_intern_table(),
        strings: strings::snapshot_string_intern_table(),
        string_tokens: strings::snapshot_tlc_string_tokens(),
    });
    // Set the worker-local token counter to the current global counter value
    // so worker-local token assignments start above all frozen tokens.
    WORKER_TOKEN_COUNTER.store(strings::tlc_string_token_counter_value(), Ordering::Relaxed);
    *FROZEN_SNAPSHOT
        .lock()
        .expect("freeze_value_interners: lock poisoned") = Some(frozen);
    PARALLEL_INTERN_ACTIVE.store(true, Ordering::Release);
}

/// Enable read-only cache mode for shared values during parallel BFS.
pub(crate) fn enable_parallel_readonly_value_caches() {
    PARALLEL_READONLY_VALUE_CACHES_ACTIVE.store(true, Ordering::Release);
}

/// Disable read-only cache mode for shared values.
pub(crate) fn disable_parallel_readonly_value_caches() {
    PARALLEL_READONLY_VALUE_CACHES_ACTIVE.store(false, Ordering::Release);
}

/// Returns true when shared values must skip embedded cache writes.
#[inline]
pub fn parallel_readonly_value_caches_active() -> bool {
    PARALLEL_READONLY_VALUE_CACHES_ACTIVE.load(Ordering::Relaxed)
}

/// Remove the frozen snapshot and deactivate parallel interning.
///
/// Call on the main thread after all BFS workers have finished.
/// Workers should have already called [`uninstall_worker_intern_scope()`].
pub(crate) fn unfreeze_value_interners() {
    PARALLEL_INTERN_ACTIVE.store(false, Ordering::Release);
    *FROZEN_SNAPSHOT
        .lock()
        .expect("unfreeze_value_interners: lock poisoned") = None;
}

/// Returns true if frozen overlay preload is disabled.
///
/// By default, `install_worker_intern_scope()` pre-populates each worker's
/// overlay with independent `Arc` copies of all frozen entries. This eliminates
/// cross-worker cache-line bouncing on shared `Arc` refcount headers.
///
/// Set `TLA2_PARALLEL_NO_PRELOAD_FROZEN=1` to disable (for A/B debugging only).
///
/// Part of #3285: promoted to default after A/B matrix confirmed 7.6% wall-time
/// improvement at 8W and elimination of 4W→8W anti-scaling.
fn preload_frozen_disabled() -> bool {
    static FLAG: OnceLock<bool> = OnceLock::new();
    tla_core::env_flag_is_set(&FLAG, "TLA2_PARALLEL_NO_PRELOAD_FROZEN")
}

/// Build worker-local string and token overlays from the frozen snapshot.
///
/// Returns independent `Arc<str>` copies so that overlay lookups always hit
/// and the frozen snapshot's shared `Arc` headers are never touched during BFS.
/// The token overlay reuses the same worker-local `Arc<str>` instances from the
/// string overlay so both tables share a single refcount header per string.
pub(super) fn preload_frozen_string_overlays(
    frozen: &FrozenValueInterners,
) -> (FxHashMap<String, Arc<str>>, FxHashMap<Arc<str>, u32>) {
    let mut strings = FxHashMap::default();
    let mut tokens = FxHashMap::default();

    // Build token overlay first to reuse string Arcs for both tables
    for (name, tok) in &frozen.string_tokens {
        let arc = strings
            .entry(name.to_string())
            .or_insert_with(|| Arc::from(name.as_ref()));
        tokens.insert(Arc::clone(arc), *tok);
    }

    // Add any strings that have no token entry
    for name in frozen.strings.keys() {
        strings
            .entry(name.clone())
            .or_insert_with(|| Arc::from(name.as_str()));
    }

    (strings, tokens)
}

/// Install the worker-local intern scope on the current thread.
///
/// Clones an `Arc` reference to the frozen snapshot into the thread-local.
/// Must be called after [`freeze_value_interners()`].
///
/// By default, pre-populates all four overlay tables with independent `Arc`
/// copies of frozen entries. This eliminates cross-worker cache-line bouncing
/// on shared `Arc` refcount headers during parallel BFS. Cost: ~15KB per
/// worker, <1ms setup.
///
/// Set `TLA2_PARALLEL_NO_PRELOAD_FROZEN=1` to disable (for A/B debugging only).
///
/// Part of #3285: promoted from opt-in to default after A/B matrix confirmed
/// 7.6% wall-time improvement at 8W.
pub fn install_worker_intern_scope() {
    let frozen = {
        let snapshot = FROZEN_SNAPSHOT
            .lock()
            .expect("install_worker_intern_scope: lock poisoned");
        snapshot.clone()
    }
    .expect("install_worker_intern_scope: called before freeze_value_interners()");

    let preload = !preload_frozen_disabled();

    let (string_overlay, string_token_overlay) = if preload {
        preload_frozen_string_overlays(&frozen)
    } else {
        (FxHashMap::default(), FxHashMap::default())
    };

    let (set_overlay, int_func_overlay) = if preload {
        let set_overlay: FxHashMap<u64, Arc<[Value]>> = frozen
            .sets
            .iter()
            .map(|(k, v)| (*k, Arc::from(v.as_ref())))
            .collect();

        let int_func_overlay: FxHashMap<u64, Arc<Vec<Value>>> = frozen
            .int_funcs
            .iter()
            .map(|(k, v)| (*k, Arc::new(v.as_ref().clone())))
            .collect();

        (set_overlay, int_func_overlay)
    } else {
        (FxHashMap::default(), FxHashMap::default())
    };

    WORKER_INTERN.with(|c| {
        *c.borrow_mut() = Some(WorkerInternState {
            frozen,
            set_overlay,
            int_func_overlay,
            string_overlay,
            string_token_overlay,
            frozen_string_hits: Cell::new(0),
            frozen_token_hits: Cell::new(0),
            frozen_set_hits: Cell::new(0),
            frozen_int_func_hits: Cell::new(0),
            overlay_string_hits: Cell::new(0),
            overlay_token_hits: Cell::new(0),
            overlay_set_hits: Cell::new(0),
            overlay_int_func_hits: Cell::new(0),
            new_string_inserts: Cell::new(0),
            new_set_inserts: Cell::new(0),
            new_int_func_inserts: Cell::new(0),
        });
    });
}

/// Remove the worker-local intern scope and clear overlay maps.
///
/// Called at worker exit. Dropping the overlay maps frees any worker-local
/// interned values that were not shared with the frozen snapshot.
pub fn uninstall_worker_intern_scope() {
    WORKER_INTERN.with(|c| {
        *c.borrow_mut() = None;
    });
}

/// Read the attribution counters from the current worker's intern scope.
///
/// Returns `None` if no worker scope is installed. Call before dropping
/// `WorkerInternGuard` to capture the counters.
///
/// Part of #3285: decision gate flat/mixed fallback — determines whether
/// remaining eval overhead is in frozen interner families or outside.
pub fn read_intern_attribution_counters() -> Option<InternAttributionCounters> {
    WORKER_INTERN.with(|c| {
        c.borrow().as_ref().map(|state| InternAttributionCounters {
            frozen_string_hits: state.frozen_string_hits.get(),
            frozen_token_hits: state.frozen_token_hits.get(),
            frozen_set_hits: state.frozen_set_hits.get(),
            frozen_int_func_hits: state.frozen_int_func_hits.get(),
            overlay_string_hits: state.overlay_string_hits.get(),
            overlay_token_hits: state.overlay_token_hits.get(),
            overlay_set_hits: state.overlay_set_hits.get(),
            overlay_int_func_hits: state.overlay_int_func_hits.get(),
            new_string_inserts: state.new_string_inserts.get(),
            new_set_inserts: state.new_set_inserts.get(),
            new_int_func_inserts: state.new_int_func_inserts.get(),
        })
    })
}

/// RAII guard that installs the worker intern scope on creation and
/// uninstalls it on drop.
pub struct WorkerInternGuard {
    _private: (),
}

impl Default for WorkerInternGuard {
    fn default() -> Self {
        Self::new()
    }
}

impl WorkerInternGuard {
    /// Create a new guard, installing the worker intern scope.
    pub fn new() -> Self {
        install_worker_intern_scope();
        Self { _private: () }
    }
}

impl Drop for WorkerInternGuard {
    fn drop(&mut self) {
        uninstall_worker_intern_scope();
    }
}

/// Cache behavior for shared values during a parallel BFS run.
///
/// Part of #3334: replaces the paired `enable/disable_parallel_readonly_value_caches`
/// toggle calls with a semantic enum boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SharedValueCacheMode {
    /// Shared values may write embedded caches during the run.
    Writable,
    /// Shared values must skip embedded cache writes during the run.
    /// Prevents `AtomicU64` cache-line bouncing during parallel BFS.
    Readonly,
}

/// RAII guard for the main-thread parallel value-intern run lifecycle.
///
/// Part of #3334: collapses the raw `freeze/enable/disable/unfreeze`
/// orchestration into one semantic boundary.
///
/// # Usage
///
/// ```ignore
/// let _run_guard = ParallelValueInternRunGuard::new(SharedValueCacheMode::Readonly);
/// // spawn workers with WorkerInternGuard...
/// // guard drop unfreezes interners and disables read-only cache mode
/// ```
pub struct ParallelValueInternRunGuard {
    _private: (),
}

impl ParallelValueInternRunGuard {
    /// Freeze value interners and set cache mode for a parallel BFS run.
    ///
    /// 1. Clears any stale read-only flag
    /// 2. Freezes the value interners (snapshots global tables)
    /// 3. Enables read-only cache mode only when `cache_mode` is `Readonly`
    pub fn new(cache_mode: SharedValueCacheMode) -> Self {
        disable_parallel_readonly_value_caches();
        freeze_value_interners();
        if cache_mode == SharedValueCacheMode::Readonly {
            enable_parallel_readonly_value_caches();
        }
        Self { _private: () }
    }

    /// Reset parallel value-intern state for abnormal-run cleanup.
    ///
    /// Idempotent: safe to call even when no guard is active. This is the
    /// single public entry point for `reset_global_state()` to clean up
    /// stale parallel value-intern state after aborted runs.
    pub fn reset_for_recovery() {
        unfreeze_value_interners();
        disable_parallel_readonly_value_caches();
    }
}

impl Drop for ParallelValueInternRunGuard {
    fn drop(&mut self) {
        disable_parallel_readonly_value_caches();
        unfreeze_value_interners();
    }
}
