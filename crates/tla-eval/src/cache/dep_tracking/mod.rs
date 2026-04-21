// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dependency tracking infrastructure for evaluator caching.
//!
//! This is the foundational layer of the cache subsystem. Every cache depends on
//! `OpEvalDeps` to track which state variables, next-state variables, and captured
//! locals were read during operator evaluation.
//!
//! Part of #2744 decomposition from eval_cache.rs.
//! Part of #3471 split into deps, runtime, guards, and tests.

mod deps;
mod guards;
mod runtime;

#[cfg(test)]
mod tests;

// === Re-exports: stable `crate::cache::dep_tracking::*` surface ===

// deps.rs
#[cfg(test)]
pub(crate) use deps::VarDepMap;
pub(crate) use deps::{dep_map_contains_key, OpEvalDeps};

// runtime.rs
pub(crate) use runtime::{
    current_state_lookup_mode, is_dep_tracking_active, mark_instance_lazy_read,
    mark_runtime_nondeterministic, propagate_cached_deps, record_local_read, record_next_read,
    record_state_read, record_tlc_level_read, EvalRuntimeState, StateLookupMode,
};

// guards.rs
pub use guards::try_eval_const_level;
pub(crate) use guards::{
    eval_with_dep_tracking, eval_with_dep_tracking_unpropagated, OpDepGuard, StateLookupModeGuard,
};
