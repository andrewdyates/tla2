// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::TransitionSystem;
use std::marker::PhantomData;

/// Observer for BFS exploration events.
pub trait ExplorationObserver<TS: TransitionSystem>: Send {
    /// Called when a new unique state is admitted.
    ///
    /// Return `false` to stop exploration immediately.
    fn on_new_state(&mut self, state: &TS::State) -> bool;

    /// Called when a transition is explored.
    ///
    /// Return `false` to stop exploration immediately.
    fn on_transition(&mut self, action: &TS::Action, from: &TS::State, to: &TS::State) -> bool;

    /// Called when a state has no enabled successors.
    fn on_deadlock(&mut self, state: &TS::State);

    /// Whether the observer has already determined that exploration can stop.
    fn is_done(&self) -> bool;
}

/// Worker-local summary contract for parallel exploration.
pub trait ParallelObserverSummary<TS: TransitionSystem>: Send {
    /// Record a newly admitted unique state.
    fn on_new_state(&mut self, state: &TS::State);

    /// Record a transition explored by the worker.
    fn on_transition(&mut self, action: &TS::Action, from: &TS::State, to: &TS::State);

    /// Record a deadlock state.
    fn on_deadlock(&mut self, state: &TS::State);

    /// Whether the worker-local summary has determined that exploration can stop.
    fn stop_requested(&self) -> bool {
        false
    }
}

/// Parallel observer contract with thread-local summaries.
pub trait ParallelObserver<TS: TransitionSystem>: ExplorationObserver<TS> {
    /// Thread-local summary type produced by worker-local exploration.
    type Summary: ParallelObserverSummary<TS>;

    /// Create a fresh summary for a worker or batch.
    fn new_summary(&self) -> Self::Summary;

    /// Merge a finished worker or batch summary back into the canonical observer.
    fn merge_summary(&mut self, summary: Self::Summary);
}

pub struct NoopSummary;

impl<TS: TransitionSystem> ParallelObserverSummary<TS> for NoopSummary {
    fn on_new_state(&mut self, _state: &TS::State) {}

    fn on_transition(&mut self, _action: &TS::Action, _from: &TS::State, _to: &TS::State) {}

    fn on_deadlock(&mut self, _state: &TS::State) {}
}

/// Observer that ignores all events and never requests early termination.
pub struct NoopObserver<TS: TransitionSystem> {
    marker: PhantomData<fn() -> TS>,
}

impl<TS: TransitionSystem> NoopObserver<TS> {
    /// Create a no-op observer.
    pub fn new() -> Self {
        Self {
            marker: PhantomData,
        }
    }
}

impl<TS: TransitionSystem> Default for NoopObserver<TS> {
    fn default() -> Self {
        Self::new()
    }
}

impl<TS: TransitionSystem> ExplorationObserver<TS> for NoopObserver<TS> {
    fn on_new_state(&mut self, _state: &TS::State) -> bool {
        true
    }

    fn on_transition(&mut self, _action: &TS::Action, _from: &TS::State, _to: &TS::State) -> bool {
        true
    }

    fn on_deadlock(&mut self, _state: &TS::State) {}

    fn is_done(&self) -> bool {
        false
    }
}

impl<TS: TransitionSystem> ParallelObserver<TS> for NoopObserver<TS> {
    type Summary = NoopSummary;

    fn new_summary(&self) -> Self::Summary {
        NoopSummary
    }

    fn merge_summary(&mut self, _summary: Self::Summary) {}
}

/// Chains multiple observers together.
///
/// Short-circuits `on_new_state` and `on_transition`: once an observer asks to
/// stop, later observers are not invoked for that event.
pub struct CompositeObserver<TS: TransitionSystem> {
    observers: Vec<Box<dyn ExplorationObserver<TS>>>,
}

impl<TS: TransitionSystem> CompositeObserver<TS> {
    /// Create an empty composite observer.
    pub fn new() -> Self {
        Self {
            observers: Vec::new(),
        }
    }

    /// Create a composite observer from pre-built observers.
    pub fn from_observers(observers: Vec<Box<dyn ExplorationObserver<TS>>>) -> Self {
        Self { observers }
    }

    /// Append an observer.
    pub fn push(&mut self, observer: Box<dyn ExplorationObserver<TS>>) {
        self.observers.push(observer);
    }

    /// Return the number of composed observers.
    pub fn len(&self) -> usize {
        self.observers.len()
    }

    /// Whether the composite contains no observers.
    pub fn is_empty(&self) -> bool {
        self.observers.is_empty()
    }
}

impl<TS: TransitionSystem> Default for CompositeObserver<TS> {
    fn default() -> Self {
        Self::new()
    }
}

impl<TS: TransitionSystem> ExplorationObserver<TS> for CompositeObserver<TS> {
    fn on_new_state(&mut self, state: &TS::State) -> bool {
        self.observers
            .iter_mut()
            .all(|observer| observer.on_new_state(state))
    }

    fn on_transition(&mut self, action: &TS::Action, from: &TS::State, to: &TS::State) -> bool {
        self.observers
            .iter_mut()
            .all(|observer| observer.on_transition(action, from, to))
    }

    fn on_deadlock(&mut self, state: &TS::State) {
        for observer in &mut self.observers {
            observer.on_deadlock(state);
        }
    }

    fn is_done(&self) -> bool {
        self.observers.iter().any(|observer| observer.is_done())
    }
}
