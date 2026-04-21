// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ReachabilityDeadlock examination.
//!
//! Checks whether any reachable state is a deadlock (no transition enabled).
//! Stops exploration immediately upon finding the first deadlock.

use std::sync::Arc;

use crate::explorer::{
    CheckpointableObserver, ExplorationObserver, ParallelExplorationObserver,
    ParallelExplorationSummary,
};
use crate::petri_net::TransitionIdx;
use crate::portfolio::SharedVerdict;
use serde::{Deserialize, Serialize};

/// Observer that stops on the first deadlock state.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub(crate) struct DeadlockObserver {
    found_deadlock: bool,
}

impl DeadlockObserver {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            found_deadlock: false,
        }
    }

    /// Returns true if a deadlock state was found during exploration.
    #[must_use]
    pub(crate) fn found_deadlock(&self) -> bool {
        self.found_deadlock
    }
}

impl ExplorationObserver for DeadlockObserver {
    fn on_new_state(&mut self, _marking: &[u64]) -> bool {
        true
    }

    fn on_transition_fire(&mut self, _trans: TransitionIdx) -> bool {
        true
    }

    fn on_deadlock(&mut self, _marking: &[u64]) {
        self.found_deadlock = true;
    }

    fn is_done(&self) -> bool {
        self.found_deadlock
    }
}

pub(crate) struct DeadlockSummary {
    found_deadlock: bool,
}

impl ParallelExplorationSummary for DeadlockSummary {
    fn on_new_state(&mut self, _marking: &[u64]) {}

    fn on_transition_fire(&mut self, _trans: TransitionIdx) {}

    fn on_deadlock(&mut self, _marking: &[u64]) {
        self.found_deadlock = true;
    }

    fn stop_requested(&self) -> bool {
        self.found_deadlock
    }
}

impl ParallelExplorationObserver for DeadlockObserver {
    type Summary = DeadlockSummary;

    fn new_summary(&self) -> Self::Summary {
        DeadlockSummary {
            found_deadlock: false,
        }
    }

    fn merge_summary(&mut self, summary: Self::Summary) {
        self.found_deadlock |= summary.found_deadlock;
    }
}

impl CheckpointableObserver for DeadlockObserver {
    type Snapshot = Self;

    const CHECKPOINT_KIND: &'static str = "DeadlockObserver";

    fn snapshot(&self) -> Self::Snapshot {
        self.clone()
    }

    fn restore_from_snapshot(&mut self, snapshot: Self::Snapshot) {
        *self = snapshot;
    }
}

/// Portfolio-aware deadlock observer that stops BFS when the SMT lane resolves.
///
/// Wraps a standard [`DeadlockObserver`] and checks a [`SharedVerdict`] on
/// every `is_done()` query. The parallel summary also reads the shared verdict
/// live so the explorer's inner batch loop can break promptly.
pub(crate) struct PortfolioDeadlockObserver {
    inner: DeadlockObserver,
    shared: Arc<SharedVerdict>,
}

impl PortfolioDeadlockObserver {
    pub(crate) fn new(shared: Arc<SharedVerdict>) -> Self {
        Self {
            inner: DeadlockObserver::new(),
            shared,
        }
    }

    pub(crate) fn found_deadlock(&self) -> bool {
        self.inner.found_deadlock()
    }
}

impl ExplorationObserver for PortfolioDeadlockObserver {
    fn on_new_state(&mut self, marking: &[u64]) -> bool {
        self.inner.on_new_state(marking)
    }

    fn on_transition_fire(&mut self, trans: TransitionIdx) -> bool {
        self.inner.on_transition_fire(trans)
    }

    fn on_deadlock(&mut self, marking: &[u64]) {
        self.inner.on_deadlock(marking);
    }

    fn is_done(&self) -> bool {
        self.inner.is_done() || self.shared.is_resolved()
    }
}

pub(crate) struct PortfolioDeadlockSummary {
    inner_found_deadlock: bool,
    shared: Arc<SharedVerdict>,
}

impl ParallelExplorationSummary for PortfolioDeadlockSummary {
    fn on_new_state(&mut self, _marking: &[u64]) {}

    fn on_transition_fire(&mut self, _trans: TransitionIdx) {}

    fn on_deadlock(&mut self, _marking: &[u64]) {
        self.inner_found_deadlock = true;
    }

    fn stop_requested(&self) -> bool {
        self.inner_found_deadlock || self.shared.is_resolved()
    }
}

impl ParallelExplorationObserver for PortfolioDeadlockObserver {
    type Summary = PortfolioDeadlockSummary;

    fn new_summary(&self) -> Self::Summary {
        PortfolioDeadlockSummary {
            inner_found_deadlock: false,
            shared: Arc::clone(&self.shared),
        }
    }

    fn merge_summary(&mut self, summary: Self::Summary) {
        self.inner.found_deadlock |= summary.inner_found_deadlock;
    }
}
