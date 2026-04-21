// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! StableMarking examination.
//!
//! Checks whether there exists a place whose token count is identical
//! in every reachable marking. A place is "stable" if its value never
//! deviates from the initial marking across the entire state space.
//!
//! Early termination: if all places become unstable, the verdict is
//! definitively FALSE even on partial exploration.

use crate::explorer::{
    CheckpointableObserver, ExplorationObserver, ParallelExplorationObserver,
    ParallelExplorationSummary,
};
use crate::petri_net::TransitionIdx;
use serde::{Deserialize, Serialize};

/// Observer that tracks per-place marking stability.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct StableMarkingObserver {
    /// Initial token count for each place (the reference value).
    initial_tokens: Vec<u64>,
    /// Per-place flag: true if the place is still stable.
    stable: Vec<bool>,
    /// Count of places that are still stable.
    stable_count: usize,
}

impl StableMarkingObserver {
    #[cfg(test)]
    #[must_use]
    pub(crate) fn new(initial_marking: &[u64]) -> Self {
        let n = initial_marking.len();
        Self {
            initial_tokens: initial_marking.to_vec(),
            stable: vec![true; n],
            stable_count: n,
        }
    }

    /// Create an observer pre-seeded with BMC instability results.
    ///
    /// Places marked `true` in `bmc_unstable` are already known to be
    /// unstable — the observer starts with those marked, so BFS only
    /// needs to resolve the remaining candidate places.
    #[must_use]
    pub(crate) fn new_seeded(initial_marking: &[u64], bmc_unstable: &[bool]) -> Self {
        let stable: Vec<bool> = bmc_unstable.iter().map(|&u| !u).collect();
        let stable_count = stable.iter().filter(|&&s| s).count();
        Self {
            initial_tokens: initial_marking.to_vec(),
            stable,
            stable_count,
        }
    }

    /// Returns true if all places have been shown to be unstable.
    #[must_use]
    pub(crate) fn all_unstable(&self) -> bool {
        self.stable_count == 0
    }
}

impl ExplorationObserver for StableMarkingObserver {
    fn on_new_state(&mut self, marking: &[u64]) -> bool {
        for (i, &tokens) in marking.iter().enumerate() {
            if self.stable[i] && tokens != self.initial_tokens[i] {
                self.stable[i] = false;
                self.stable_count -= 1;
                if self.stable_count == 0 {
                    return false; // all unstable — definitive FALSE
                }
            }
        }
        true
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) -> bool {
        true
    }

    fn on_deadlock(&mut self, _marking: &[u64]) {}

    fn is_done(&self) -> bool {
        self.stable_count == 0
    }
}

pub(crate) struct StableMarkingSummary {
    initial_tokens: Vec<u64>,
    stable: Vec<bool>,
}

impl ParallelExplorationSummary for StableMarkingSummary {
    fn on_new_state(&mut self, marking: &[u64]) {
        for (i, &tokens) in marking.iter().enumerate() {
            if self.stable[i] && tokens != self.initial_tokens[i] {
                self.stable[i] = false;
            }
        }
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) {}

    fn on_deadlock(&mut self, _marking: &[u64]) {}

    fn stop_requested(&self) -> bool {
        !self.stable.iter().any(|stable| *stable)
    }
}

impl ParallelExplorationObserver for StableMarkingObserver {
    type Summary = StableMarkingSummary;

    fn new_summary(&self) -> Self::Summary {
        StableMarkingSummary {
            initial_tokens: self.initial_tokens.clone(),
            stable: vec![true; self.stable.len()],
        }
    }

    fn merge_summary(&mut self, summary: Self::Summary) {
        for (idx, stable) in summary.stable.into_iter().enumerate() {
            if !stable && self.stable[idx] {
                self.stable[idx] = false;
                self.stable_count -= 1;
            }
        }
    }
}

impl CheckpointableObserver for StableMarkingObserver {
    type Snapshot = Self;

    const CHECKPOINT_KIND: &'static str = "StableMarkingObserver";

    fn snapshot(&self) -> Self::Snapshot {
        self.clone()
    }

    fn restore_from_snapshot(&mut self, snapshot: Self::Snapshot) {
        *self = snapshot;
    }
}
