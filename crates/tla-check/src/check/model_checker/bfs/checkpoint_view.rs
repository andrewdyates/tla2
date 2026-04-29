// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Checkpoint frontier projection helpers for BFS storage modes.
//!
//! Part of #2351: extracted from storage-mode implementations to keep
//! queue-to-frontier materialization separate from BFS algorithm/storage
//! contracts.

use super::super::frontier::BfsFrontier;
use super::super::{ArrayState, State, VecDeque};

/// Materialize the checkpoint frontier from the current state and queue entries.
///
/// Callers provide `map_entry` to project each queue entry into an optional
/// frontier state. Returning `None` skips the queue entry.
pub(in crate::check::model_checker) fn build_checkpoint_frontier<Q: Clone>(
    current: &ArrayState,
    queue: &impl BfsFrontier<Entry = Q>,
    registry: &crate::var_index::VarRegistry,
    map_entry: impl FnMut(&Q) -> Option<State>,
) -> VecDeque<State> {
    let mut frontier: VecDeque<State> = queue
        .checkpoint_entries()
        .iter()
        .filter_map(map_entry)
        .collect();
    frontier.push_front(current.to_state(registry));
    frontier
}
