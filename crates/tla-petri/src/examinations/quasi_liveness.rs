// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QuasiLiveness examination.
//!
//! Checks whether every transition in the net can fire at least once
//! from some reachable marking. Terminates early when all transitions
//! have been observed firing.

use crate::explorer::{
    CheckpointableObserver, ExplorationObserver, ParallelExplorationObserver,
    ParallelExplorationSummary,
};
use crate::petri_net::TransitionIdx;
use serde::{Deserialize, Serialize};

/// Observer that tracks which transitions have fired at least once.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct QuasiLivenessObserver {
    /// Per-transition "has fired" flag.
    fired: Vec<bool>,
    /// Count of transitions that have NOT yet fired.
    remaining: usize,
}

impl QuasiLivenessObserver {
    #[cfg(test)]
    #[must_use]
    pub(crate) fn new(num_transitions: usize) -> Self {
        Self {
            fired: vec![false; num_transitions],
            remaining: num_transitions,
        }
    }

    /// Create an observer pre-seeded with BMC results.
    ///
    /// Transitions marked `true` in `bmc_resolved` are already known to be
    /// quasi-live — the observer starts with those counted, so BFS only
    /// needs to discover the remaining transitions.
    #[must_use]
    pub(crate) fn new_seeded(bmc_resolved: &[bool]) -> Self {
        let remaining = bmc_resolved.iter().filter(|&&r| !r).count();
        Self {
            fired: bmc_resolved.to_vec(),
            remaining,
        }
    }

    /// Returns true if every transition has fired at least once.
    #[must_use]
    pub(crate) fn all_fired(&self) -> bool {
        self.remaining == 0
    }
}

impl ExplorationObserver for QuasiLivenessObserver {
    fn on_new_state(&mut self, _marking: &[u64]) -> bool {
        true
    }

    fn on_transition_fire(&mut self, trans: TransitionIdx) -> bool {
        let idx = trans.0 as usize;
        if !self.fired[idx] {
            self.fired[idx] = true;
            self.remaining -= 1;
        }
        true
    }

    fn on_deadlock(&mut self, _marking: &[u64]) {}

    fn is_done(&self) -> bool {
        self.remaining == 0
    }
}

pub(crate) struct QuasiLivenessSummary {
    fired: Vec<bool>,
}

impl ParallelExplorationSummary for QuasiLivenessSummary {
    fn on_new_state(&mut self, _marking: &[u64]) {}

    fn on_transition_fire(&mut self, trans: TransitionIdx) {
        self.fired[trans.0 as usize] = true;
    }

    fn on_deadlock(&mut self, _marking: &[u64]) {}

    fn stop_requested(&self) -> bool {
        false
    }
}

impl ParallelExplorationObserver for QuasiLivenessObserver {
    type Summary = QuasiLivenessSummary;

    fn new_summary(&self) -> Self::Summary {
        QuasiLivenessSummary {
            fired: vec![false; self.fired.len()],
        }
    }

    fn merge_summary(&mut self, summary: Self::Summary) {
        for (idx, fired) in summary.fired.into_iter().enumerate() {
            if fired && !self.fired[idx] {
                self.fired[idx] = true;
                self.remaining -= 1;
            }
        }
    }
}

impl CheckpointableObserver for QuasiLivenessObserver {
    type Snapshot = Self;

    const CHECKPOINT_KIND: &'static str = "QuasiLivenessObserver";

    fn snapshot(&self) -> Self::Snapshot {
        self.clone()
    }

    fn restore_from_snapshot(&mut self, snapshot: Self::Snapshot) {
        *self = snapshot;
    }
}
