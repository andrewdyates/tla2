// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::hash::Hash;

/// A transition system that can be explored by the generic model-check core.
pub trait TransitionSystem: Send + Sync {
    /// Concrete state representation.
    type State: Clone + Send + Sync;
    /// Domain-specific action or transition label.
    type Action: Clone + Send + Sync;
    /// Deduplication fingerprint for a state.
    type Fingerprint: Copy + Eq + Hash + Send + Sync;

    /// Return the initial states of the system.
    fn initial_states(&self) -> Vec<Self::State>;

    /// Enumerate all enabled transitions from a state.
    fn successors(&self, state: &Self::State) -> Vec<(Self::Action, Self::State)>;

    /// Compute the canonical deduplication fingerprint for a state.
    fn fingerprint(&self, state: &Self::State) -> Self::Fingerprint;
}

/// Property classes relevant to partial-order reduction decisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub enum PorPropertyClass {
    /// Safety / invariant checking.
    #[default]
    Safety,
    /// Deadlock detection.
    Deadlock,
    /// Linear-time temporal checking.
    Liveness,
    /// Branching-time temporal checking (for example: CTL).
    Branching,
    /// The caller cannot provide a sharper classification.
    Unknown,
}

/// Partial-order reduction provider.
pub trait PorProvider<TS: TransitionSystem>: Send + Sync {
    /// Reduce the enabled action set for the given state and property class.
    fn reduce(
        &self,
        state: &TS::State,
        enabled: &[TS::Action],
        property: PorPropertyClass,
    ) -> Vec<TS::Action>;
}

/// Atom evaluator for temporal logic engines.
pub trait AtomEvaluator<TS: TransitionSystem>: Send + Sync {
    /// Evaluate atom `atom_id` on `state`.
    fn evaluate(&self, state: &TS::State, atom_id: usize) -> bool;
}
