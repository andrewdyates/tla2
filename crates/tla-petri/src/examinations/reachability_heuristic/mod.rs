// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Heuristic best-first search for reachability witness finding.
//!
//! Phase 2e in the reachability pipeline, between random walk (2d) and
//! full BFS (Phase 3). Uses LP state-equation relaxation as an admissible
//! distance heuristic to guide exploration toward EF(φ) witnesses.
//!
//! **Memory-bounded:** Uses a Bloom filter for visited-state tracking (O(1)
//! per state, ~10 bits/entry) and truncates the priority queue when it
//! exceeds a configurable bound. This allows exploring nets with 10^8+
//! reachable states without OOM.
//!
//! **Witness-only:** Like random walk, this phase only resolves
//! EF(φ)=TRUE and AG(φ)=FALSE. It cannot prove universal properties.
//! Unresolved trackers fall through to BFS.
//!
//! **Sound because:** Any marking reached by firing enabled transitions from
//! the initial marking is reachable. Bloom filter false positives only skip
//! states (safe for witness search). Queue truncation only discards states.

mod frontier;
mod heuristic;
mod search;

#[cfg(test)]
mod tests;

use std::time::Instant;

use crate::examinations::reachability_witness::WitnessValidationContext;
use crate::petri_net::PetriNet;

use super::reachability::PropertyTracker;

/// Default maximum states in the Bloom filter before stopping.
const DEFAULT_BLOOM_CAPACITY: usize = 10_000_000;

/// Default maximum entries in the priority queue.
const DEFAULT_MAX_QUEUE_SIZE: usize = 1_000_000;

/// Default budget: maximum state expansions before giving up.
const DEFAULT_MAX_EXPANSIONS: u64 = 5_000_000;

/// Run heuristic best-first witness search on unresolved trackers.
///
/// For each unresolved tracker, computes LP-derived heuristic weights and
/// uses them to guide a memory-bounded best-first search toward witness
/// states.
pub(crate) fn run_heuristic_seeding(
    net: &PetriNet,
    trackers: &mut [PropertyTracker],
    validation: &WitnessValidationContext<'_>,
    deadline: Option<Instant>,
) {
    search::run_heuristic_seeding_params(
        net,
        trackers,
        validation,
        deadline,
        DEFAULT_MAX_EXPANSIONS,
        DEFAULT_BLOOM_CAPACITY,
        DEFAULT_MAX_QUEUE_SIZE,
    );
}
