// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! BFS model checker for generated `StateMachine` implementations.

use crate::StateMachine;

/// Result of a model checking run
#[derive(Debug)]
pub struct ModelCheckResult<S> {
    /// Number of states explored
    pub states_explored: usize,
    /// Number of distinct states found
    pub distinct_states: usize,
    /// If an invariant was violated, the state that violated it
    pub violation: Option<InvariantViolation<S>>,
    /// If a deadlock was found (state with no successors), the deadlocked state
    pub deadlock: Option<S>,
}

/// Information about an invariant violation
#[derive(Debug)]
pub struct InvariantViolation<S> {
    /// The state that violated the invariant
    pub state: S,
    /// Name of the violated invariant (if known)
    pub invariant_name: Option<String>,
}

impl<S> ModelCheckResult<S> {
    /// Check if the model check succeeded (no violations or deadlocks)
    pub fn is_ok(&self) -> bool {
        self.violation.is_none() && self.deadlock.is_none()
    }
}

/// A simple BFS model checker that uses the StateMachine trait
///
/// This can be used to verify that generated code behaves correctly:
/// - Explores all reachable states from Init via Next
/// - Checks invariants on each state
/// - Detects deadlocks (states with no successors)
///
/// # Example
/// ```rust
/// use tla_runtime::{model_check, StateMachine};
///
/// #[derive(Clone, Debug, PartialEq, Eq, Hash)]
/// struct CounterState {
///     count: i64,
/// }
///
/// struct Counter;
///
/// impl StateMachine for Counter {
///     type State = CounterState;
///
///     fn init(&self) -> Vec<Self::State> {
///         vec![CounterState { count: 0 }]
///     }
///
///     fn next(&self, state: &Self::State) -> Vec<Self::State> {
///         // A 3-state cycle, so exploration terminates without deadlock.
///         vec![CounterState {
///             count: (state.count + 1) % 3,
///         }]
///     }
/// }
///
/// let spec = Counter;
/// let result = model_check(&spec, 1000);
/// assert!(result.is_ok());
/// ```
pub fn model_check<M: StateMachine>(machine: &M, max_states: usize) -> ModelCheckResult<M::State> {
    use std::collections::{HashSet, VecDeque};

    let mut seen: HashSet<M::State> = HashSet::new();
    let mut queue: VecDeque<M::State> = VecDeque::new();
    let mut states_explored = 0;

    // Initialize with all initial states
    for state in machine.init() {
        if seen.insert(state.clone()) {
            queue.push_back(state);
        }
    }

    // BFS exploration
    while let Some(state) = queue.pop_front() {
        states_explored += 1;

        if states_explored > max_states {
            break;
        }

        // Check invariants
        if let Some(false) = machine.check_invariant(&state) {
            return ModelCheckResult {
                states_explored,
                distinct_states: seen.len(),
                violation: Some(InvariantViolation {
                    state,
                    invariant_name: None,
                }),
                deadlock: None,
            };
        }

        // Generate successors
        let successors = machine.next(&state);

        // Check for deadlock
        if successors.is_empty() {
            return ModelCheckResult {
                states_explored,
                distinct_states: seen.len(),
                violation: None,
                deadlock: Some(state),
            };
        }

        // Add new states to queue
        for succ in successors {
            if seen.insert(succ.clone()) {
                queue.push_back(succ);
            }
        }
    }

    ModelCheckResult {
        states_explored,
        distinct_states: seen.len(),
        violation: None,
        deadlock: None,
    }
}

/// Model check with a custom invariant function
///
/// This allows checking invariants that aren't part of the spec's check_invariant
pub fn model_check_with_invariant<M, F>(
    machine: &M,
    max_states: usize,
    invariant: F,
) -> ModelCheckResult<M::State>
where
    M: StateMachine,
    F: Fn(&M::State) -> bool,
{
    use std::collections::{HashSet, VecDeque};

    let mut seen: HashSet<M::State> = HashSet::new();
    let mut queue: VecDeque<M::State> = VecDeque::new();
    let mut states_explored = 0;

    // Initialize with all initial states
    for state in machine.init() {
        if seen.insert(state.clone()) {
            queue.push_back(state);
        }
    }

    // BFS exploration
    while let Some(state) = queue.pop_front() {
        states_explored += 1;

        if states_explored > max_states {
            break;
        }

        // Check custom invariant
        if !invariant(&state) {
            return ModelCheckResult {
                states_explored,
                distinct_states: seen.len(),
                violation: Some(InvariantViolation {
                    state,
                    invariant_name: Some("custom".to_string()),
                }),
                deadlock: None,
            };
        }

        // Generate successors
        let successors = machine.next(&state);

        // Check for deadlock (don't report if state is same as before)
        if successors.is_empty() {
            return ModelCheckResult {
                states_explored,
                distinct_states: seen.len(),
                violation: None,
                deadlock: Some(state),
            };
        }

        // Add new states to queue
        for succ in successors {
            if seen.insert(succ.clone()) {
                queue.push_back(succ);
            }
        }
    }

    ModelCheckResult {
        states_explored,
        distinct_states: seen.len(),
        violation: None,
        deadlock: None,
    }
}

/// Collect all reachable states (up to a limit) without checking invariants
///
/// Useful for testing that a spec generates the expected state space
pub fn collect_states<M: StateMachine>(machine: &M, max_states: usize) -> Vec<M::State> {
    use std::collections::{HashSet, VecDeque};

    let mut seen: HashSet<M::State> = HashSet::new();
    let mut queue: VecDeque<M::State> = VecDeque::new();
    let mut result: Vec<M::State> = Vec::new();

    // Initialize with all initial states
    for state in machine.init() {
        if seen.insert(state.clone()) {
            queue.push_back(state);
        }
    }

    // BFS exploration
    while let Some(state) = queue.pop_front() {
        if result.len() >= max_states {
            break;
        }

        result.push(state.clone());

        // Generate successors
        for succ in machine.next(&state) {
            if seen.insert(succ.clone()) {
                queue.push_back(succ);
            }
        }
    }

    result
}
