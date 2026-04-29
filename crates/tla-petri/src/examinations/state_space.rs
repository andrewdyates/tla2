// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! StateSpace examination.
//!
//! Computes state space statistics: number of reachable markings,
//! number of explored transition edges, maximum tokens in any place,
//! and maximum token sum.

use crate::explorer::{
    CheckpointableObserver, ExplorationObserver, ParallelExplorationObserver,
    ParallelExplorationSummary,
};
use crate::petri_net::TransitionIdx;
use serde::{Deserialize, Serialize};

/// Observer that collects state space statistics during exploration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct StateSpaceObserver {
    states_count: usize,
    transition_edges: u64,
    max_token_in_place: u64,
    max_token_sum: u64,
}

impl StateSpaceObserver {
    #[must_use]
    pub(crate) fn new(initial_marking: &[u64]) -> Self {
        let sum: u64 = initial_marking.iter().sum();
        let max_place = initial_marking.iter().copied().max().unwrap_or(0);
        Self {
            states_count: 0,
            transition_edges: 0,
            max_token_in_place: max_place,
            max_token_sum: sum,
        }
    }

    /// Returns the computed state space statistics.
    #[must_use]
    pub(crate) fn stats(&self) -> StateSpaceStats {
        StateSpaceStats {
            states: self.states_count,
            edges: self.transition_edges,
            max_token_in_place: self.max_token_in_place,
            max_token_sum: self.max_token_sum,
        }
    }
}

/// State space statistics computed during exploration.
#[derive(Debug, Clone)]
pub(crate) struct StateSpaceStats {
    /// Total number of unique reachable markings.
    pub(crate) states: usize,
    /// Total number of transition firings explored across all reachable states.
    pub(crate) edges: u64,
    /// Maximum number of tokens seen in any single place.
    pub(crate) max_token_in_place: u64,
    /// Maximum sum of tokens across all places in any marking.
    pub(crate) max_token_sum: u64,
}

impl ExplorationObserver for StateSpaceObserver {
    fn on_new_state(&mut self, marking: &[u64]) -> bool {
        self.states_count += 1;
        let sum: u64 = marking.iter().sum();
        let max_place = marking.iter().copied().max().unwrap_or(0);
        if max_place > self.max_token_in_place {
            self.max_token_in_place = max_place;
        }
        if sum > self.max_token_sum {
            self.max_token_sum = sum;
        }
        true
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) -> bool {
        self.transition_edges += 1;
        true
    }

    fn on_deadlock(&mut self, _marking: &[u64]) {}

    fn is_done(&self) -> bool {
        false // always explore full state space
    }
}

#[derive(Default)]
pub(crate) struct StateSpaceSummary {
    states_count: usize,
    transition_edges: u64,
    max_token_in_place: u64,
    max_token_sum: u64,
}

impl ParallelExplorationSummary for StateSpaceSummary {
    fn on_new_state(&mut self, marking: &[u64]) {
        self.states_count += 1;
        let sum: u64 = marking.iter().sum();
        let max_place = marking.iter().copied().max().unwrap_or(0);
        self.max_token_in_place = self.max_token_in_place.max(max_place);
        self.max_token_sum = self.max_token_sum.max(sum);
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) {
        self.transition_edges += 1;
    }

    fn on_deadlock(&mut self, _marking: &[u64]) {}

    fn stop_requested(&self) -> bool {
        false
    }
}

impl ParallelExplorationObserver for StateSpaceObserver {
    type Summary = StateSpaceSummary;

    fn new_summary(&self) -> Self::Summary {
        StateSpaceSummary::default()
    }

    fn merge_summary(&mut self, summary: Self::Summary) {
        self.states_count += summary.states_count;
        self.transition_edges += summary.transition_edges;
        self.max_token_in_place = self.max_token_in_place.max(summary.max_token_in_place);
        self.max_token_sum = self.max_token_sum.max(summary.max_token_sum);
    }
}

impl CheckpointableObserver for StateSpaceObserver {
    type Snapshot = Self;

    const CHECKPOINT_KIND: &'static str = "StateSpaceObserver";

    fn snapshot(&self) -> Self::Snapshot {
        self.clone()
    }

    fn restore_from_snapshot(&mut self, snapshot: Self::Snapshot) {
        *self = snapshot;
    }
}
