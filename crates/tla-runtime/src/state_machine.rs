// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The core `StateMachine` trait for TLA+ specifications.

use std::fmt;
use std::hash::Hash;

/// The core trait for TLA+ state machines.
///
/// Generated Rust code from TLA+ specifications implements this trait.
/// The trait supports:
/// - Multiple initial states (non-determinism in `Init`)
/// - Multiple successor states (non-determinism in `Next`)
/// - Invariant checking via the `check_invariant` method
pub trait StateMachine {
    /// The state type, generated as a struct from TLA+ variables
    type State: Clone + Eq + Hash + fmt::Debug;

    /// Generate all possible initial states.
    ///
    /// Corresponds to the `Init` predicate in TLA+.
    /// Returns an empty vector if no initial state satisfies Init.
    fn init(&self) -> Vec<Self::State>;

    /// Stream initial states with short-circuiting.
    ///
    /// This is a more efficient primitive than `init()` for callers that want to
    /// stop early (e.g. membership checks) or avoid materializing/allocating the
    /// full init-state list.
    ///
    /// The default implementation is built on top of `init()` and therefore
    /// still allocates; code generated from TLA+ should override this method to
    /// avoid allocation.
    fn for_each_init<F>(&self, mut f: F) -> std::ops::ControlFlow<()>
    where
        F: FnMut(Self::State) -> std::ops::ControlFlow<()>,
    {
        for s in self.init() {
            if let std::ops::ControlFlow::Break(()) = f(s) {
                return std::ops::ControlFlow::Break(());
            }
        }
        std::ops::ControlFlow::Continue(())
    }

    /// Generate all successor states from the given state.
    ///
    /// Corresponds to the `Next` action in TLA+.
    /// Returns an empty vector if the state is deadlocked.
    fn next(&self, state: &Self::State) -> Vec<Self::State>;

    /// Stream successor states from the given state, with short-circuiting.
    ///
    /// This is a more efficient primitive than `next()` for callers that want to
    /// stop early (e.g. membership checks) or avoid materializing/allocating the
    /// full successor list.
    ///
    /// The default implementation is built on top of `next()` and therefore
    /// still allocates; code generated from TLA+ should override this method to
    /// avoid allocation.
    fn for_each_next<F>(&self, state: &Self::State, mut f: F) -> std::ops::ControlFlow<()>
    where
        F: FnMut(Self::State) -> std::ops::ControlFlow<()>,
    {
        for s in self.next(state) {
            if let std::ops::ControlFlow::Break(()) = f(s) {
                return std::ops::ControlFlow::Break(());
            }
        }
        std::ops::ControlFlow::Continue(())
    }

    /// Check if an invariant holds on the given state.
    ///
    /// Returns `None` if no invariants are defined.
    /// Returns `Some(true)` if all invariants hold.
    /// Returns `Some(false)` if any invariant is violated.
    fn check_invariant(&self, _state: &Self::State) -> Option<bool> {
        None
    }

    /// Get the names of defined invariants.
    fn invariant_names(&self) -> Vec<&'static str> {
        vec![]
    }

    /// Check a specific invariant by name.
    fn check_named_invariant(&self, _name: &str, _state: &Self::State) -> Option<bool> {
        None
    }

    /// Check whether a transition from `old` to `new` satisfies the Next predicate.
    ///
    /// Returns `Some(true)` if the transition is valid, `Some(false)` if it
    /// violates Next, or `None` if predicate-based checking is not supported
    /// for this spec (the default).
    ///
    /// Generated code overrides this when the Next predicate uses only
    /// simple primed-variable patterns that can be evaluated as a predicate
    /// over (old, new) state pairs.
    fn is_next(&self, _old: &Self::State, _new: &Self::State) -> Option<bool> {
        None
    }
}
