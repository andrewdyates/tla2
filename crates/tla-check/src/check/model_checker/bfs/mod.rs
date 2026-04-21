// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BFS submodule: storage-mode abstractions and exploration engine.
//!
//! Part of #2351: boundary-aligned split from `run_bfs_common.rs`.
//! Separates storage-mode contracts (trait + implementations) from the
//! BFS exploration algorithm, mirroring TLC's Worker/IStateQueue split.

mod checkpoint_view;
pub(crate) mod core_step;
// core_step_seq removed in #2963: both diff and full-state paths now do
// inline admit → invariant → enqueue (no need for SequentialBfsAdapter
// or run_core_step_batch).
mod diff_successors;
mod diff_successors_streaming;
pub(crate) mod engine;
mod full_state_successors;
mod full_state_successors_streaming;
mod iter_state;
mod observer;
pub(in crate::check::model_checker) mod storage_modes;
mod successor_processing;
pub(crate) mod transport;
pub(in crate::check::model_checker) mod transport_seq;
pub(crate) mod worker_loop;
// Arena-backed BFS frontier for FlatState buffers (Part of #4126)
pub(in crate::check::model_checker) mod flat_frontier;
// Arena-backed flat state pool for zero-allocation successor dedup (Part of #4172)
pub(in crate::check::model_checker) mod flat_state_pool;
// Compiled BFS level loop for JIT-compiled frontier processing (Part of #3988)
#[cfg(feature = "jit")]
mod compiled_bfs_loop;
// Frontier sampling for Cooperative Dual-Engine Model Checking (Part of #3768)
#[cfg(feature = "z4")]
pub(crate) mod frontier_sampler;

use crate::var_index::VarRegistry;

/// Value parameters shared by all BFS successor-processing functions.
///
/// Bundles the read-only depth/level/registry arguments that are threaded
/// identically through `process_{diff,full_state}_successors{,_streaming}`,
/// reducing their argument count from 9 to 6.
pub(super) struct BfsStepParams<'a> {
    pub registry: &'a VarRegistry,
    pub current_depth: usize,
    pub succ_depth: usize,
    /// TLC level of the current (parent) state: `depth_to_tlc_level(current_depth)`.
    /// ACTION_CONSTRAINT expressions that reference `TLCGet("level")` should see
    /// this value, not `succ_level`.  Part of #1281.
    pub current_level: u32,
    pub succ_level: u32,
}

// Re-export storage types for sibling modules (run_bfs_full, run_bfs_notrace, run_resume).
pub(in crate::check::model_checker) use self::storage_modes::{
    FingerprintOnlyStorage, FullStateStorage, NoTraceQueueEntry,
};
pub(in crate::check::model_checker) use self::worker_loop::BfsLoopOutcome;
