// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Worker-local value fingerprinting and state management for the parallel value lane.
//!
//! Part of #3337: This module provides:
//!
//! 1. `WorkerArrayState` — a worker-local copy of an `ArrayState` where all
//!    top-level Arc allocations are unshared (private refcounts). This eliminates
//!    cross-thread atomic refcount contention during `EvalCtx::lookup_state_var`.
//!
//! 2. `WorkerFpMemo` — a worker-local fingerprint cache that replaces the embedded
//!    `AtomicU64` caches in `FuncValue`, `SortedSet`, etc. Keyed by Arc pointer
//!    identity for compound types, avoiding cross-thread cache-line bouncing.
//!
//! 3. Round-trip conversion between `ArrayState` and `WorkerArrayState`, with
//!    fingerprint parity guarantees.
//!
//! Gated behind `TLA2_PARALLEL_WORKER_VALUES=1`.

pub(crate) mod array_state;
// Worker-local fingerprint computation — tested but not wired into the
// production successor pipeline. WorkerFpMemo is a field of WorkerArrayState
// but fingerprint() is not called in production (only values() is live).
#[allow(dead_code)]
pub(crate) mod fingerprint;

// Re-export public items
pub(crate) use array_state::WorkerArrayState;
#[allow(unused_imports)] // Used by tests via crate::state::worker_value_hash::WorkerFpMemo
pub(crate) use fingerprint::WorkerFpMemo;

// Feature flag
feature_flag!(pub(crate) parallel_worker_values, "TLA2_PARALLEL_WORKER_VALUES");
