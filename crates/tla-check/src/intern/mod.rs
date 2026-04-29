// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Value Interning for TLA+ Model Checking
//!
//! This module provides a value interning system that eliminates Arc atomic
//! contention during parallel model checking. Values are stored once in a
//! global table and referenced by lightweight handles.
//!
//! # Design
//!
//! In standard TLA2, `ArrayState` stores `Box<[Value]>` where `Value` contains
//! Arc-based shared data (Sets, Funcs, Seqs, etc.). Cloning a state requires
//! atomic reference count increments for each Arc, causing cache line bouncing
//! and contention across threads.
//!
//! Value interning replaces this with:
//! - `ValueHandle(u64)`: A lightweight handle (the value's fingerprint)
//! - `ValueInterner`: A global table mapping handles to values
//! - `HandleState`: State as `Box<[ValueHandle]>` - pure memcpy clone
//!
//! # Performance
//!
//! - State cloning: O(n) memcpy instead of O(n) atomic operations
//! - Value deduplication: Automatic (same value = same fingerprint = same handle)
//! - Value lookup: O(1) DashMap access when needed
//!
//! # Usage
//!
//! ```rust,ignore
//! use tla_check::intern::ValueInterner; // crate-internal path
//! use tla_check::Value;
//!
//! let interner = ValueInterner::new();
//! let handle = interner.intern(Value::int(42));
//! let value = interner.try_get(handle).expect("value was interned");
//! assert_eq!(value, Value::int(42));
//! ```

mod handle_state;

pub use handle_state::HandleState;

use crate::state::value_fingerprint;
use crate::Value;
use dashmap::DashMap;
use rustc_hash::FxHasher;
use std::hash::BuildHasherDefault;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::OnceLock;
use thiserror::Error;

/// FxHasher-based BuildHasher for faster hashing of u64 handles.
type FxBuildHasher = BuildHasherDefault<FxHasher>;

/// FxHasher-based DashMap for concurrent handle -> Value storage.
type FxDashMap<K, V> = DashMap<K, V, FxBuildHasher>;

// ============================================================================
// ValueHandle - Lightweight reference to an interned value
// ============================================================================

/// A lightweight handle to an interned value.
///
/// This is just the value's 64-bit fingerprint, used as a key into the
/// global value table. Handles are `Copy` and can be cloned without
/// any atomic operations.
///
/// # Invariants
///
/// - A valid handle always corresponds to a value in the interner
/// - Two handles are equal iff they refer to the same value
/// - The handle value is the fingerprint of the interned value
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ValueHandle(pub u64);

/// Fallible lookup error for stale or invalid interned value handles.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
#[error("invalid handle {handle:#x}: value not interned")]
pub struct InvalidValueHandleError {
    handle: u64,
}

impl InvalidValueHandleError {
    #[inline]
    fn new(handle: ValueHandle) -> Self {
        Self { handle: handle.0 }
    }

    #[cfg(test)]
    #[inline]
    fn handle(self) -> ValueHandle {
        ValueHandle(self.handle)
    }
}

// ============================================================================
// ValueInterner - Global thread-safe value table
// ============================================================================

/// Global thread-safe value interner.
///
/// Values are stored in a DashMap keyed by their fingerprint. The interner
/// provides O(1) insertion and lookup with minimal contention.
///
/// # Thread Safety
///
/// The interner uses DashMap which provides fine-grained locking at the
/// shard level, allowing multiple threads to insert/lookup concurrently
/// with minimal blocking.
pub struct ValueInterner {
    /// Map from fingerprint to value
    values: FxDashMap<u64, Value>,
}

impl ValueInterner {
    /// Create a new value interner.
    pub fn new() -> Self {
        ValueInterner {
            values: DashMap::with_hasher(FxBuildHasher::default()),
        }
    }

    /// Intern a value and return its handle.
    ///
    /// If the value (by fingerprint) was already interned, returns the
    /// existing handle. Otherwise, stores the value and returns a new handle.
    ///
    /// # Performance
    ///
    /// This computes the value's fingerprint (O(value size)) and does a
    /// DashMap insertion (O(1) amortized).
    #[inline]
    pub fn intern(&self, value: Value) -> ValueHandle {
        let fp = value_fingerprint(&value);
        // Use entry API to avoid race conditions
        self.values.entry(fp).or_insert(value);
        ValueHandle(fp)
    }

    /// Get the value for a handle if it is still interned.
    ///
    /// Returns an error if the handle is stale or invalid, for example after a
    /// `clear()` call invalidated previously issued handles.
    #[inline]
    pub fn try_get(&self, handle: ValueHandle) -> Result<Value, InvalidValueHandleError> {
        self.values
            .get(&handle.0)
            .map(|v| v.clone())
            .ok_or_else(|| InvalidValueHandleError::new(handle))
    }

    /// Clear all interned values.
    ///
    /// # Warning
    ///
    /// This invalidates all existing handles!
    pub fn clear(&self) {
        self.values.clear();
    }
}

/// Test-only query methods (not used in production).
#[cfg(test)]
impl ValueInterner {
    /// Get the number of interned values.
    #[inline]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Check if the interner is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Check if a fingerprint is present in the interner.
    #[inline]
    pub fn contains_fp(&self, fp: u64) -> bool {
        self.values.contains_key(&fp)
    }
}

impl Default for ValueInterner {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// HandleStateInternerBank - Per-run sharded interner for owner-local access
// ============================================================================

/// Per-run interner bank with one shard per worker.
///
/// Part of #3212: Replaces the single global `ValueInterner` for HandleState
/// mode. Each worker interns into its own shard (no cross-thread DashMap traffic
/// on the common local-queue path). Stolen states are materialized from the
/// producing worker's shard via the `owner_worker` field on `HandleState`.
pub(crate) struct HandleStateInternerBank {
    shards: Box<[ValueInterner]>,
}

impl HandleStateInternerBank {
    /// Create a bank with `num_workers` independent interner shards.
    pub(crate) fn new(num_workers: usize) -> Self {
        let shards: Vec<ValueInterner> = (0..num_workers).map(|_| ValueInterner::new()).collect();
        HandleStateInternerBank {
            shards: shards.into_boxed_slice(),
        }
    }

    /// Get the interner shard for a given worker.
    ///
    /// # Panics
    ///
    /// Panics if `worker_id >= num_workers`.
    #[inline]
    pub(crate) fn shard(&self, worker_id: usize) -> &ValueInterner {
        &self.shards[worker_id]
    }
}

// ============================================================================
// Global Interner Instance
// ============================================================================

/// Global value interner singleton.
///
/// Use `get_interner()` to access this.
static GLOBAL_INTERNER: OnceLock<ValueInterner> = OnceLock::new();
static ACTIVE_MODEL_CHECK_RUNS: AtomicUsize = AtomicUsize::new(0);

/// Reset the active model check run counter to zero.
///
/// Part of #3384: Called by `reset_global_state()` to ensure the refcount
/// does not leak across independent runs in the same process. A leaked
/// counter causes `begin_model_check_run()` to skip `clear_run_scoped_interners()`.
pub(crate) fn reset_active_model_check_runs() {
    ACTIVE_MODEL_CHECK_RUNS.store(0, Ordering::Release);
}

/// Returns true if at least one model check run is currently active.
///
/// Part of #4067: Used by `reset_global_state()` to skip destructive cache
/// clearing when a concurrent model check run is in progress. Without this
/// guard, concurrent tests calling `reset_global_state()` corrupt eval caches
/// for in-flight runs.
#[cfg(test)]
pub(crate) fn has_active_model_check_runs() -> bool {
    ACTIVE_MODEL_CHECK_RUNS.load(Ordering::Acquire) > 0
}

/// Atomically try to acquire the right to clear global state.
///
/// Part of #4067: TOCTOU fix. `reset_global_state()` must atomically check
/// that no model check runs are active AND prevent new ones from starting
/// during the clear. This uses compare-exchange to transition 0 -> SENTINEL.
/// `begin_model_check_run()` will spin-wait if it sees the sentinel.
///
/// Returns true if the caller should proceed with clearing. The caller MUST
/// call `release_reset_lock()` after clearing is complete.
#[cfg(test)]
const RESET_SENTINEL: usize = usize::MAX / 2;

#[cfg(test)]
pub(crate) fn try_acquire_reset_lock() -> bool {
    ACTIVE_MODEL_CHECK_RUNS
        .compare_exchange(0, RESET_SENTINEL, Ordering::AcqRel, Ordering::Acquire)
        .is_ok()
}

/// Release the reset lock, restoring the counter to 0.
#[cfg(test)]
pub(crate) fn release_reset_lock() {
    ACTIVE_MODEL_CHECK_RUNS.store(0, Ordering::Release);
}

/// Get the global value interner for test infrastructure.
///
/// This initializes the interner on first call.
/// Production code now uses worker-local `InternerBank` shards (Part of #3212).
/// The accessor is test-only; production lifecycle code clears the singleton
/// via `clear_global_value_interner()` and `ModelCheckRunGuard`.
#[cfg(test)]
#[inline]
pub(crate) fn get_interner() -> &'static ValueInterner {
    GLOBAL_INTERNER.get_or_init(ValueInterner::new)
}

/// Clear the global value interner.
///
/// # Warning
///
/// This invalidates all existing handles! Only call between model checking runs.
///
/// Note: Named `clear_global_value_interner` to distinguish from
/// `tla_core::clear_global_name_interner()` which clears name interning.
pub fn clear_global_value_interner() {
    if let Some(interner) = GLOBAL_INTERNER.get() {
        interner.clear();
    }
}

fn clear_run_scoped_interners() {
    clear_global_value_interner();
    crate::value::clear_string_intern_table();
}

/// Mark the start of a model-checking run that may use global interners.
///
/// The first active run clears stale interned state before execution. Nested
/// or concurrent runs increment a refcount and defer clearing until the last
/// run completes.
///
/// Part of #4067: In test builds, spin-wait if a concurrent reset is in
/// progress (counter == RESET_SENTINEL). This prevents new model check runs
/// from starting while `reset_global_state()` is clearing global state.
pub(crate) fn begin_model_check_run() {
    #[cfg(test)]
    {
        // Spin-wait if reset is in progress (RESET_SENTINEL).
        loop {
            let current = ACTIVE_MODEL_CHECK_RUNS.load(Ordering::Acquire);
            if current == RESET_SENTINEL {
                std::thread::yield_now();
                continue;
            }
            // Try to atomically increment from current value.
            match ACTIVE_MODEL_CHECK_RUNS.compare_exchange_weak(
                current,
                current + 1,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(prev) => {
                    if prev == 0 {
                        clear_run_scoped_interners();
                    }
                    return;
                }
                Err(_) => continue,
            }
        }
    }

    #[cfg(not(test))]
    {
        let prev = ACTIVE_MODEL_CHECK_RUNS.fetch_add(1, Ordering::AcqRel);
        if prev == 0 {
            clear_run_scoped_interners();
        }
    }
}

/// Mark the end of a model-checking run that may use global interners.
pub(crate) fn end_model_check_run() {
    let mut active = ACTIVE_MODEL_CHECK_RUNS.load(Ordering::Acquire);
    loop {
        if active == 0 {
            // This can happen legitimately during multi-threaded test runs when
            // reset_global_state() in one test zeroes the counter while another
            // test's ModelCheckRunGuard is still alive. In release builds the
            // assert was already absent; make debug builds resilient too.
            #[cfg(test)]
            eprintln!(
                "WARN: end_model_check_run called with counter already 0 \
                 (likely test interaction via reset_global_state)"
            );
            #[cfg(not(test))]
            debug_assert!(
                false,
                "end_model_check_run called without matching begin_model_check_run"
            );
            return;
        }
        // Part of #4067: If we see the RESET_SENTINEL, a concurrent
        // reset_global_state() is clearing global state. Spin-wait until
        // it finishes, then re-read the counter.
        #[cfg(test)]
        if active == RESET_SENTINEL {
            std::thread::yield_now();
            active = ACTIVE_MODEL_CHECK_RUNS.load(Ordering::Acquire);
            continue;
        }
        match ACTIVE_MODEL_CHECK_RUNS.compare_exchange_weak(
            active,
            active - 1,
            Ordering::AcqRel,
            Ordering::Acquire,
        ) {
            Ok(_) => {
                if active == 1 {
                    clear_run_scoped_interners();
                }
                return;
            }
            Err(actual) => active = actual,
        }
    }
}

/// RAII guard for model-checking run interner lifecycle.
pub(crate) struct ModelCheckRunGuard;

impl ModelCheckRunGuard {
    #[must_use]
    pub(crate) fn begin() -> Self {
        begin_model_check_run();
        Self
    }
}

impl Drop for ModelCheckRunGuard {
    fn drop(&mut self) {
        end_model_check_run();
    }
}

/// Wait until no model check runs are active, then return.
///
/// Part of #2724: Used by interner lifecycle tests to synchronize with
/// concurrent model check runs. Once this returns, clearing has occurred
/// (the last `end_model_check_run` to see counter==1 cleared the interner).
///
/// # Panics
///
/// Panics if the counter doesn't reach 0 within ~240 seconds.
///
/// Part of #4067: Increased from 5s because long-running tests
/// (e.g., real_disruptor) hold active model check runs. Keep this above the
/// slowest model-check test timeout so interner cleanup tests do not panic
/// while a legitimate run is still active.
#[cfg(test)]
pub(crate) fn wait_for_no_active_runs() {
    for _ in 0..240_000 {
        if ACTIVE_MODEL_CHECK_RUNS.load(Ordering::Acquire) == 0 {
            return;
        }
        std::thread::sleep(std::time::Duration::from_millis(1));
    }
    panic!(
        "timed out waiting for concurrent model check runs to finish (active: {})",
        ACTIVE_MODEL_CHECK_RUNS.load(Ordering::Acquire)
    );
}

#[cfg(test)]
mod tests;
