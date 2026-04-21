// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Runtime monitoring for `StateMachine` implementations (Layer 4 of Verification Stack).

use crate::StateMachine;

/// A wrapper that monitors a state machine at runtime, checking invariants
/// on every transition. Use this in production to catch specification violations.
///
/// # Example
///
/// ```rust
/// use tla_runtime::{MonitoredStateMachine, SpecViolation, StateMachine};
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
///         vec![CounterState {
///             count: state.count + 1,
///         }]
///     }
///
///     fn check_invariant(&self, state: &Self::State) -> Option<bool> {
///         Some(state.count < 10)
///     }
/// }
///
/// let mut monitored = MonitoredStateMachine::new(Counter)
///     .expect("invariant: Counter always produces initial states");
/// match monitored.step() {
///     Ok(()) => {}
///     Err(SpecViolation::InvariantViolated { .. }) => { /* handle violation */ }
///     Err(SpecViolation::ActionNotEnabled { .. }) => {}
///     Err(SpecViolation::Deadlock { .. }) => {}
///     Err(SpecViolation::MaxViolationsExceeded { .. }) => { /* stop monitoring */ }
///     Err(SpecViolation::EmptyInit) => { /* no initial states */ }
/// }
/// ```
pub struct MonitoredStateMachine<M: StateMachine> {
    machine: M,
    state: M::State,
    config: MonitorConfig,
    stats: MonitorStats,
}

/// Configuration for runtime monitoring
#[derive(Clone, Debug)]
pub struct MonitorConfig {
    /// Whether to check invariants on every transition (default: true)
    pub check_invariants: bool,
    /// Maximum number of violations to tolerate (default: None = unlimited).
    /// When set to `Some(n)`, the first `n` violations are returned as
    /// `SpecViolation::InvariantViolated`; the `(n+1)`th returns
    /// `SpecViolation::MaxViolationsExceeded`.
    pub max_violations: Option<usize>,
}

impl Default for MonitorConfig {
    fn default() -> Self {
        Self {
            check_invariants: true,
            max_violations: None,
        }
    }
}

/// Statistics collected during monitored execution
#[derive(Clone, Debug, Default)]
pub struct MonitorStats {
    /// Total number of transitions
    pub transitions: u64,
    /// Number of invariant violations detected
    pub violations: u64,
    /// Number of deadlocks detected
    pub deadlocks: u64,
    /// Number of disabled actions attempted
    pub disabled_actions: u64,
}

/// Errors that can occur during monitored execution
#[derive(Debug, Clone)]
pub enum SpecViolation<S> {
    /// An invariant was violated after a transition
    InvariantViolated {
        /// The state that violated the invariant
        state: S,
        /// Index of the action that caused the violation
        action_index: usize,
        /// Names of violated invariants (if available)
        violated_invariants: Vec<String>,
    },
    /// No actions are enabled (deadlock)
    Deadlock {
        /// The deadlocked state
        state: S,
    },
    /// The requested action was not enabled
    ActionNotEnabled {
        /// Index of the action that was not enabled
        action_index: usize,
    },
    /// The configured `max_violations` threshold was exceeded
    MaxViolationsExceeded {
        /// Total violation count at the time of rejection
        violations: u64,
        /// The configured maximum
        max: usize,
    },
    /// The spec produced no initial states (empty Init predicate)
    EmptyInit,
}

impl<M: StateMachine> MonitoredStateMachine<M> {
    /// Create a new monitored state machine, starting from an initial state.
    ///
    /// Returns `Err(SpecViolation::EmptyInit)` if the machine's `init()` produces
    /// no initial states.
    pub fn new(machine: M) -> Result<Self, SpecViolation<M::State>> {
        let init_states = machine.init();
        let state = init_states
            .into_iter()
            .next()
            .ok_or(SpecViolation::EmptyInit)?;
        Ok(Self {
            machine,
            state,
            config: MonitorConfig::default(),
            stats: MonitorStats::default(),
        })
    }

    /// Create with custom configuration.
    ///
    /// Returns `Err(SpecViolation::EmptyInit)` if the machine's `init()` produces
    /// no initial states.
    pub fn with_config(machine: M, config: MonitorConfig) -> Result<Self, SpecViolation<M::State>> {
        let init_states = machine.init();
        let state = init_states
            .into_iter()
            .next()
            .ok_or(SpecViolation::EmptyInit)?;
        Ok(Self {
            machine,
            state,
            config,
            stats: MonitorStats::default(),
        })
    }

    /// Get the current state
    pub fn state(&self) -> &M::State {
        &self.state
    }

    /// Get statistics
    pub fn stats(&self) -> &MonitorStats {
        &self.stats
    }

    /// Take a step (non-deterministically choosing the first enabled action)
    pub fn step(&mut self) -> Result<(), SpecViolation<M::State>> {
        let mut next_state: Option<M::State> = None;
        let cf = self.machine.for_each_next(&self.state, |s| {
            next_state = Some(s);
            std::ops::ControlFlow::Break(())
        });

        if matches!(cf, std::ops::ControlFlow::Continue(())) {
            self.stats.deadlocks += 1;
            return Err(SpecViolation::Deadlock {
                state: self.state.clone(),
            });
        }

        // for_each_next returned Break only after setting next_state = Some(s)
        let Some(next_state) = next_state else {
            unreachable!("for_each_next Break implies at least one successor");
        };

        // Check invariant if enabled
        if self.config.check_invariants {
            if let Some(false) = self.machine.check_invariant(&next_state) {
                let violated_invariants = self
                    .machine
                    .invariant_names()
                    .into_iter()
                    .filter_map(|name| {
                        match self.machine.check_named_invariant(name, &next_state) {
                            Some(false) => Some(name.to_string()),
                            _ => None,
                        }
                    })
                    .collect();
                self.stats.violations += 1;
                if let Some(max) = self.config.max_violations {
                    if self.stats.violations > max as u64 {
                        return Err(SpecViolation::MaxViolationsExceeded {
                            violations: self.stats.violations,
                            max,
                        });
                    }
                }
                return Err(SpecViolation::InvariantViolated {
                    state: next_state,
                    action_index: 0,
                    violated_invariants,
                });
            }
        }

        self.state = next_state;
        self.stats.transitions += 1;
        Ok(())
    }

    /// Apply a specific action by index
    pub fn apply(&mut self, action_index: usize) -> Result<(), SpecViolation<M::State>> {
        let mut next_state: Option<M::State> = None;
        let mut num_seen: usize = 0;
        let cf = self.machine.for_each_next(&self.state, |s| {
            let idx = num_seen;
            num_seen += 1;
            if idx == action_index {
                next_state = Some(s);
                std::ops::ControlFlow::Break(())
            } else {
                std::ops::ControlFlow::Continue(())
            }
        });

        if num_seen == 0 && matches!(cf, std::ops::ControlFlow::Continue(())) {
            self.stats.deadlocks += 1;
            return Err(SpecViolation::Deadlock {
                state: self.state.clone(),
            });
        }

        let Some(next_state) = next_state else {
            self.stats.disabled_actions += 1;
            return Err(SpecViolation::ActionNotEnabled { action_index });
        };

        // Check invariant if enabled
        if self.config.check_invariants {
            if let Some(false) = self.machine.check_invariant(&next_state) {
                let violated_invariants = self
                    .machine
                    .invariant_names()
                    .into_iter()
                    .filter_map(|name| {
                        match self.machine.check_named_invariant(name, &next_state) {
                            Some(false) => Some(name.to_string()),
                            _ => None,
                        }
                    })
                    .collect();
                self.stats.violations += 1;
                if let Some(max) = self.config.max_violations {
                    if self.stats.violations > max as u64 {
                        return Err(SpecViolation::MaxViolationsExceeded {
                            violations: self.stats.violations,
                            max,
                        });
                    }
                }
                return Err(SpecViolation::InvariantViolated {
                    state: next_state,
                    action_index,
                    violated_invariants,
                });
            }
        }

        self.state = next_state;
        self.stats.transitions += 1;
        Ok(())
    }

    /// Reset to an initial state.
    ///
    /// Returns `Err(SpecViolation::EmptyInit)` if the machine's `init()` produces
    /// no initial states.
    pub fn reset(&mut self) -> Result<(), SpecViolation<M::State>> {
        let init_states = self.machine.init();
        self.state = init_states
            .into_iter()
            .next()
            .ok_or(SpecViolation::EmptyInit)?;
        Ok(())
    }

    /// Get the number of enabled actions in the current state
    pub fn enabled_actions(&self) -> usize {
        let mut count: usize = 0;
        let _ = self.machine.for_each_next(&self.state, |_| {
            count += 1;
            std::ops::ControlFlow::Continue(())
        });
        count
    }
}
