// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! UpperBounds observer: sequential and parallel state-space exploration adapters.

use crate::explorer::{
    ExplorationObserver, ParallelExplorationObserver, ParallelExplorationSummary,
};
use crate::petri_net::TransitionIdx;

use super::model::BoundTracker;

/// Update all trackers' max bounds from a single marking.
fn update_trackers_from_marking(trackers: &mut [BoundTracker], marking: &[u64]) {
    for tracker in trackers {
        let sum: u64 = tracker
            .place_indices
            .iter()
            .map(|idx| marking[idx.0 as usize])
            .sum();
        if sum > tracker.max_bound {
            tracker.max_bound = sum;
        }
    }
}

/// Observer that tracks UpperBounds across all properties simultaneously.
pub(super) struct UpperBoundsObserver {
    trackers: Vec<BoundTracker>,
}

impl UpperBoundsObserver {
    /// Create an observer from already-validated UpperBounds trackers.
    #[must_use]
    pub(super) fn new(trackers: Vec<BoundTracker>) -> Self {
        Self { trackers }
    }

    /// Consume the observer and return the trackers for result assembly.
    pub(super) fn into_trackers(self) -> Vec<BoundTracker> {
        self.trackers
    }
}

impl ExplorationObserver for UpperBoundsObserver {
    fn on_new_state(&mut self, marking: &[u64]) -> bool {
        update_trackers_from_marking(&mut self.trackers, marking);
        true
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) -> bool {
        true
    }

    fn on_deadlock(&mut self, _marking: &[u64]) {}

    fn is_done(&self) -> bool {
        // Early-terminate when all trackers have reached their structural
        // upper bound. At that point, observed == structural bound proves
        // the bound is exact (observed ≤ true_max ≤ structural_bound).
        !self.trackers.is_empty()
            && self
                .trackers
                .iter()
                .all(BoundTracker::is_structurally_resolved)
    }
}

pub(super) struct UpperBoundsSummary {
    trackers: Vec<BoundTracker>,
}

impl ParallelExplorationSummary for UpperBoundsSummary {
    fn on_new_state(&mut self, marking: &[u64]) {
        update_trackers_from_marking(&mut self.trackers, marking);
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) {}

    fn on_deadlock(&mut self, _marking: &[u64]) {}

    fn stop_requested(&self) -> bool {
        false
    }
}

impl ParallelExplorationObserver for UpperBoundsObserver {
    type Summary = UpperBoundsSummary;

    fn new_summary(&self) -> Self::Summary {
        UpperBoundsSummary {
            trackers: self.trackers.clone(),
        }
    }

    fn merge_summary(&mut self, summary: Self::Summary) {
        for (tracker, merged) in self.trackers.iter_mut().zip(summary.trackers) {
            tracker.max_bound = tracker.max_bound.max(merged.max_bound);
        }
    }
}
