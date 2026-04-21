// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Counterexample trace representation and formatting.
//!
//! Split from `api.rs` for file-size hygiene (Part of #3427).

use crate::eval::EvalCtx;
use crate::state::State;
use crate::Value;

/// Action label for a trace step.
///
/// TLC format: `<ActionName line L, col C to line L2, col C2 of module M>`
/// Initial state uses `<Initial predicate>`.
///
/// Part of #2696 Step 2: metadata for TLC-matching action labels in trace output.
#[derive(Debug, Clone)]
pub struct ActionLabel {
    /// Action name (operator name, e.g., "Next", "SendMsg")
    pub name: String,
    /// Source location string in TLC format, e.g., "line 10, col 3 to line 12, col 15 of module Spec"
    pub source_location: Option<String>,
}

impl std::fmt::Display for ActionLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.source_location {
            Some(loc) => write!(f, "<{} {}>", self.name, loc),
            None => write!(f, "<{}>", self.name),
        }
    }
}

/// A counterexample trace - sequence of states leading to the error
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Trace {
    /// Sequence of states from initial to error state
    pub states: Vec<State>,
    /// Action labels for each state transition.
    /// `action_labels[0]` is the label for the initial state (typically "Initial predicate").
    /// `action_labels[i]` for i > 0 is the action that produced `states[i]` from `states[i-1]`.
    /// Empty when action attribution is not available (e.g., no-trace mode).
    ///
    /// Part of #2696 Step 2.
    pub action_labels: Vec<ActionLabel>,
}

impl Trace {
    /// Create an empty trace
    pub(crate) fn new() -> Self {
        Trace {
            states: Vec::new(),
            action_labels: Vec::new(),
        }
    }

    /// Create a trace from states (no action labels).
    ///
    /// Action labels will show `<Initial predicate>` and `<Action>` placeholders.
    pub fn from_states(states: Vec<State>) -> Self {
        Trace {
            states,
            action_labels: Vec::new(),
        }
    }

    /// Create a trace from states with action labels.
    ///
    /// `action_labels` should have the same length as `states`:
    /// - `action_labels[0]` labels the initial state
    /// - `action_labels[i]` labels the action that produced `states[i]`
    pub(crate) fn from_states_with_labels(
        states: Vec<State>,
        action_labels: Vec<ActionLabel>,
    ) -> Self {
        Trace {
            states,
            action_labels,
        }
    }

    /// Length of the trace
    pub fn len(&self) -> usize {
        self.states.len()
    }

    /// Check if trace is empty
    pub fn is_empty(&self) -> bool {
        self.states.is_empty()
    }

    /// Apply ALIAS transformation to this trace.
    ///
    /// For each state in the trace, evaluates the ALIAS operator and replaces
    /// the state variables with the result. If the ALIAS evaluates to a record,
    /// the record fields become the state variables. Otherwise, the original
    /// state is kept unchanged (TLC silently ignores non-record ALIAS results).
    ///
    /// TLC evaluates the ALIAS expression when printing error traces instead of
    /// dumping raw state variables. This provides user-friendly state representations.
    ///
    /// Part of #3012.
    pub fn apply_alias(&self, ctx: &mut EvalCtx, alias_name: &str) -> Trace {
        if self.is_empty() {
            return self.clone();
        }
        let registry = ctx.var_registry().clone();
        let mut new_states = Vec::with_capacity(self.states.len());

        for state in &self.states {
            // Clear state-dependent caches between states (same as invariant checking).
            crate::eval::clear_for_state_boundary();

            // Convert state to array form and bind in the context.
            let values = state.to_values(&registry);
            let prev = ctx.bind_state_array(&values);

            let eval_result = ctx.eval_op(alias_name);
            let new_state = match &eval_result {
                Ok(Value::Record(rec)) => {
                    // Record result: use record fields as the new state variables.
                    State::from_pairs(rec.iter_str().map(|(k, v)| (k, v.clone())))
                }
                _ => {
                    // Non-record or error: keep original state unchanged.
                    state.clone()
                }
            };

            ctx.restore_state_env(prev);
            new_states.push(new_state);
        }

        Trace {
            states: new_states,
            action_labels: self.action_labels.clone(),
        }
    }
}

impl Default for Trace {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Display for Trace {
    /// TLC-matching text format for counterexample traces.
    ///
    /// Format (matches TLC 2.20 console output exactly):
    /// ```text
    /// State 1: <Initial predicate>
    /// /\ x = 0
    /// /\ y = 1
    ///
    /// State 2: <Next line 10, col 3 to line 12, col 15 of module Spec>
    /// /\ x = 1
    /// /\ y = 0
    /// ```
    ///
    /// When `action_labels` is populated, uses actual action names with source locations.
    /// Otherwise falls back to `<Initial predicate>` / `<Action>` placeholders.
    ///
    /// Single-variable states omit the `/\ ` prefix per TLC convention.
    /// Fingerprints are hidden (TLC only shows them in debug mode).
    ///
    /// Part of #2696: Steps 1-2, 6 of trace format parity (#2695, #2470).
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, state) in self.states.iter().enumerate() {
            // Use actual action label if available, otherwise placeholder.
            if let Some(label) = self.action_labels.get(i) {
                writeln!(f, "State {}: {}", i + 1, label)?;
            } else {
                let placeholder = if i == 0 {
                    "<Initial predicate>"
                } else {
                    "<Action>"
                };
                writeln!(f, "State {}: {}", i + 1, placeholder)?;
            }

            let vars: Vec<_> = state.vars().collect();
            if vars.len() == 1 {
                // Single-variable states omit "/\ " prefix (TLC convention).
                writeln!(f, "{} = {}", vars[0].0, vars[0].1)?;
            } else {
                for (name, value) in &vars {
                    writeln!(f, "/\\ {} = {}", name, value)?;
                }
            }
            // TLC emits a blank line after each state.
            writeln!(f)?;
        }
        Ok(())
    }
}

/// Synthetic operator name used for inline NEXT expressions.
/// When a spec formula contains something like `Init /\ [][\E n \in Node: Next(n)]_vars`,
/// we create a synthetic operator with this name to hold the lowered expression.
pub(crate) const INLINE_NEXT_NAME: &str = "__TLA2_INLINE_NEXT__";
