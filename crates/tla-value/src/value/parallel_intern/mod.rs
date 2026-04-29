// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Frozen-snapshot + worker-local overlay for value interning during parallel BFS.
//!
//! Part of #3285: Removes `DashMap` contention from parallel BFS by snapshotting
//! the global optimization-only interners into immutable `FxHashMap`s before
//! spawning workers. Each worker thread uses a thread-local overlay for new
//! entries during BFS, completely avoiding cross-thread synchronization.
//!
//! # Usage
//!
//! 1. Call [`freeze_value_interners()`] on the main thread after parsing and
//!    before spawning BFS workers.
//! 2. Each worker thread calls [`install_worker_intern_scope()`] at startup.
//! 3. During BFS, [`intern_set_array()`](super::intern_tables::intern_set_array)
//!    and [`intern_int_func_array()`](super::intern_tables::intern_int_func_array)
//!    automatically use the frozen snapshot + overlay when active.
//! 4. Workers call [`uninstall_worker_intern_scope()`] at exit (or rely on the
//!    [`WorkerInternGuard`] RAII guard).
//! 5. Call [`unfreeze_value_interners()`] after all workers finish.
//!
//! # Design
//!
//! See `designs/2026-03-16-3285-parallel-value-interning-boundary.md` Phase 2.
//! Pattern follows `tla-core::name_intern::freeze_interner()` from #2955.
//!
//! # Module structure (Part of #3412)
//!
//! - `state.rs`: Shared globals, frozen snapshot type, worker-local TLS overlay
//! - `session.rs`: Lifecycle (freeze/unfreeze), preload, install/uninstall, RAII guard
//! - `lookups.rs`: Hot-path set/int-func/string/token lookup+insert helpers

// Test-only imports (tests/ uses `use super::*` which pulls from this scope)
#[cfg(test)]
use self::session::{
    freeze_value_interners, install_worker_intern_scope, preload_frozen_string_overlays,
    unfreeze_value_interners, uninstall_worker_intern_scope,
};
#[cfg(test)]
use self::state::{FrozenValueInterners, WorkerInternState, FROZEN_SNAPSHOT, WORKER_INTERN};
#[cfg(test)]
use super::{intern_tables, strings, Value};

mod lookups;
mod session;
mod state;
#[cfg(test)]
mod tests;

// Re-exports: public API surface (Part of #3334: run-scoped guard replaces raw lifecycle toggles)
pub use self::session::{
    parallel_readonly_value_caches_active, read_intern_attribution_counters,
    ParallelValueInternRunGuard, SharedValueCacheMode, WorkerInternGuard,
};
pub use self::state::InternAttributionCounters;

// Part of #3334: raw lifecycle helpers (freeze/unfreeze/enable/disable) are now
// internal to the parallel_intern module, called only by ParallelValueInternRunGuard.

// Crate-internal re-exports used by value/intern_tables/, value/strings.rs, etc.
pub(in crate::value) use self::lookups::{
    parallel_intern_int_func, parallel_intern_set, parallel_intern_string,
    parallel_tlc_string_token, parallel_try_get_interned_modified,
};
pub(super) use self::session::is_parallel_intern_active;
