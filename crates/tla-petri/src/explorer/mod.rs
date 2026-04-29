// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! BFS state space explorer for Petri nets.
//!
//! Uses FxHashSet for fast marking deduplication. Exploration is
//! parameterized by an `ExplorationObserver` trait that receives
//! callbacks on state discovery, transition firing, and deadlock
//! detection, enabling early termination for specific examinations.

mod adaptive;
mod checkpoint;
mod config;
#[allow(dead_code)]
pub(crate) mod diff_bfs;
pub(crate) mod fingerprint;
pub(crate) mod fingerprint_only;
mod graph;
mod observer;
mod seen;
mod setup;
mod state_registry;
mod transition_selection;

#[cfg(test)]
pub(crate) use adaptive::{
    analyze_observer_parallelism, estimate_state_space, select_strategy, Strategy,
    LARGE_SPEC_THRESHOLD, MEDIUM_SPEC_THRESHOLD, PARALLEL_THRESHOLD, PILOT_SAMPLE_SIZE,
};
pub(crate) use checkpoint::{explore_checkpointable_observer, CheckpointableObserver};
pub use config::{AutoSizeInfo, CheckpointConfig, ExplorationConfig, FpsetBackend, StorageMode};
pub(crate) use config::{
    ExplorationObserver, ExplorationResult, ParallelExplorationObserver, ParallelExplorationSummary,
};
pub(crate) use graph::{
    explore_and_build_graph, explore_full, FullReachabilityGraph, ReachabilityGraph,
};
#[cfg(test)]
pub(crate) use observer::explore;
pub(crate) use observer::explore_observer;
pub(crate) use setup::ExplorationSetup;
#[cfg(test)]
pub(crate) use transition_selection::enabled_transitions_into;

#[cfg(test)]
mod tests;
