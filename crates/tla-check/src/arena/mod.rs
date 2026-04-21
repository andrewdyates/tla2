// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Memory arena for efficient state storage
//!
//! This module provides arena-based allocation to reduce heap fragmentation
//! during model checking, and contiguous bulk storage for multiple states.

mod bulk_storage;
pub(crate) mod flat_bridge;
#[cfg(test)]
mod state_arena;
pub(crate) mod successor_buffer;
#[cfg(test)]
mod tests;
pub(crate) mod worker_arena;

pub(crate) use bulk_storage::{BulkStateHandle, BulkStateStorage};
// Arena flat bridge + successor buffer — scaffolding for arena promotion path (#3990)
#[allow(unused_imports)]
pub(crate) use flat_bridge::ArenaFlatBridge;
#[allow(unused_imports)]
pub(crate) use successor_buffer::{SuccessorBuffer, SuccessorEntry};
pub(crate) use worker_arena::{init_worker_arena, report_worker_arena_stats, worker_arena_reset};
// Arena promotion path scaffolding — not yet wired into production BFS (#3990)
#[allow(unused_imports)]
pub(crate) use worker_arena::{with_worker_arena, ArenaArrayState, WorkerArena};
