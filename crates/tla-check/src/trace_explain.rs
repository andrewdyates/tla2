// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trace explanation engine: annotates counterexample traces with human-readable
//! descriptions of what changed and why.
//!
//! When the model checker finds a violation, it produces a counterexample trace
//! as a sequence of states. Raw traces show state assignments but do not explain
//! *why* each transition happened. This module provides:
//!
//! - **State diff computation**: what variables changed between consecutive states
//! - **Action attribution**: which Next disjunct produced each transition
//! - **Variable change summaries**: e.g., `pc["p1"] changed from "a" to "b"`
//!
//! TLC provides action names; this engine goes further with diff-based
//! human-readable explanations of each step.

use std::fmt;
use std::sync::Arc;

use crate::check::ActionLabel;
use crate::state::State;
use crate::Trace;
use crate::Value;

/// A single variable change between two consecutive states.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarChange {
    /// Variable name.
    pub name: Arc<str>,
    /// Value in the previous state. `None` if the variable did not exist.
    pub old_value: Option<Value>,
    /// Value in the current state. `None` if the variable no longer exists.
    pub new_value: Option<Value>,
}

impl fmt::Display for VarChange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (&self.old_value, &self.new_value) {
            (Some(old), Some(new)) => {
                write!(f, "{} changed from {} to {}", self.name, old, new)
            }
            (None, Some(new)) => {
                write!(f, "{} appeared with value {}", self.name, new)
            }
            (Some(old), None) => {
                write!(f, "{} removed (was {})", self.name, old)
            }
            (None, None) => {
                write!(f, "{} (no value)", self.name)
            }
        }
    }
}

/// The diff between two consecutive states.
#[derive(Debug, Clone)]
pub struct TraceStateDiff {
    /// Variables that changed between the two states.
    pub changed: Vec<VarChange>,
    /// Variables that remained unchanged.
    pub unchanged_count: usize,
}

impl TraceStateDiff {
    /// Compute the diff between two states.
    #[must_use]
    pub fn compute(prev: &State, curr: &State) -> Self {
        let mut changed = Vec::new();
        let mut unchanged_count = 0;

        for (name, curr_val) in curr.vars() {
            match prev.get(name) {
                Some(prev_val) if prev_val != curr_val => {
                    changed.push(VarChange {
                        name: Arc::clone(name),
                        old_value: Some(prev_val.clone()),
                        new_value: Some(curr_val.clone()),
                    });
                }
                Some(_) => {
                    unchanged_count += 1;
                }
                None => {
                    // Variable appeared (new in this state).
                    changed.push(VarChange {
                        name: Arc::clone(name),
                        old_value: None,
                        new_value: Some(curr_val.clone()),
                    });
                }
            }
        }

        // Check for variables that disappeared (in prev but not in curr).
        for (name, prev_val) in prev.vars() {
            if curr.get(name).is_none() {
                changed.push(VarChange {
                    name: Arc::clone(name),
                    old_value: Some(prev_val.clone()),
                    new_value: None,
                });
            }
        }

        TraceStateDiff {
            changed,
            unchanged_count,
        }
    }

    /// True if no variables changed.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.changed.is_empty()
    }

    /// Number of changed variables.
    #[must_use]
    pub fn num_changed(&self) -> usize {
        self.changed.len()
    }

    /// Total number of variables (changed + unchanged).
    #[must_use]
    pub fn total_vars(&self) -> usize {
        self.changed.len() + self.unchanged_count
    }
}

impl fmt::Display for TraceStateDiff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.changed.is_empty() {
            write!(f, "(no changes)")?;
        } else {
            for (i, change) in self.changed.iter().enumerate() {
                if i > 0 {
                    writeln!(f)?;
                }
                write!(f, "  {}", change)?;
            }
        }
        Ok(())
    }
}

/// An explained step in a trace: one state transition with annotations.
#[derive(Debug, Clone)]
pub struct ExplainedStep {
    /// 1-based step number.
    pub step_number: usize,
    /// The state at this step.
    pub state: State,
    /// Action label for this step (e.g., "Initial predicate", "SendMsg").
    pub action_label: ActionLabel,
    /// Diff from the previous state. `None` for the initial state.
    pub diff: Option<TraceStateDiff>,
    /// Human-readable summary of the transition.
    pub summary: String,
}

impl fmt::Display for ExplainedStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "--- Step {} ---", self.step_number)?;
        writeln!(f, "Action: {}", self.action_label)?;
        writeln!(f, "Summary: {}", self.summary)?;

        if let Some(ref diff) = self.diff {
            if diff.is_empty() {
                writeln!(f, "Changes: (stuttering step - no variables changed)")?;
            } else {
                writeln!(
                    f,
                    "Changes ({} of {} variables):",
                    diff.num_changed(),
                    diff.total_vars()
                )?;
                for change in &diff.changed {
                    writeln!(f, "  {}", change)?;
                }
            }
        }

        // Print the full state.
        writeln!(f, "State:")?;
        let vars: Vec<_> = self.state.vars().collect();
        for (name, value) in &vars {
            writeln!(f, "  /\\ {} = {}", name, value)?;
        }

        Ok(())
    }
}

/// A fully explained counterexample trace.
#[derive(Debug, Clone)]
pub struct ExplainedTrace {
    /// The explained steps, one per state in the original trace.
    pub steps: Vec<ExplainedStep>,
}

impl ExplainedTrace {
    /// Build an explained trace from a `Trace`.
    ///
    /// Computes diffs between consecutive states and generates human-readable
    /// summaries for each transition.
    #[must_use]
    pub fn from_trace(trace: &Trace) -> Self {
        let mut steps = Vec::with_capacity(trace.states.len());

        for (i, state) in trace.states.iter().enumerate() {
            let action_label = trace.action_labels.get(i).cloned().unwrap_or_else(|| {
                if i == 0 {
                    ActionLabel {
                        name: "Initial predicate".to_string(),
                        source_location: None,
                    }
                } else {
                    ActionLabel {
                        name: "Action".to_string(),
                        source_location: None,
                    }
                }
            });

            let diff = if i > 0 {
                Some(TraceStateDiff::compute(&trace.states[i - 1], state))
            } else {
                None
            };

            let summary = build_step_summary(i, state, &action_label, diff.as_ref());

            steps.push(ExplainedStep {
                step_number: i + 1,
                state: state.clone(),
                action_label,
                diff,
                summary,
            });
        }

        ExplainedTrace { steps }
    }

    /// Build an explained trace for a liveness violation (prefix + cycle).
    #[must_use]
    pub fn from_liveness_trace(prefix: &Trace, cycle: &Trace) -> Self {
        // Merge the prefix and cycle into a single explained trace with annotations.
        let prefix_len = prefix.states.len();
        let mut steps = Vec::with_capacity(prefix_len + cycle.states.len());

        // Explain the prefix.
        for (i, state) in prefix.states.iter().enumerate() {
            let action_label = prefix.action_labels.get(i).cloned().unwrap_or_else(|| {
                if i == 0 {
                    ActionLabel {
                        name: "Initial predicate".to_string(),
                        source_location: None,
                    }
                } else {
                    ActionLabel {
                        name: "Action".to_string(),
                        source_location: None,
                    }
                }
            });

            let diff = if i > 0 {
                Some(TraceStateDiff::compute(&prefix.states[i - 1], state))
            } else {
                None
            };

            let summary = build_step_summary(i, state, &action_label, diff.as_ref());

            steps.push(ExplainedStep {
                step_number: i + 1,
                state: state.clone(),
                action_label,
                diff,
                summary,
            });
        }

        // Explain the cycle.
        for (j, state) in cycle.states.iter().enumerate() {
            let global_idx = prefix_len + j;
            let action_label = cycle
                .action_labels
                .get(j)
                .cloned()
                .unwrap_or_else(|| ActionLabel {
                    name: "Action".to_string(),
                    source_location: None,
                });

            let prev = if j > 0 {
                &cycle.states[j - 1]
            } else if !prefix.states.is_empty() {
                prefix
                    .states
                    .last()
                    .expect("invariant: prefix is non-empty")
            } else {
                // Edge case: empty prefix and first cycle state.
                state
            };

            let diff = if j == 0 && prefix.states.is_empty() {
                None
            } else {
                Some(TraceStateDiff::compute(prev, state))
            };

            let mut summary = build_step_summary(global_idx, state, &action_label, diff.as_ref());

            // Annotate cycle states.
            if j == 0 {
                summary = format!("[CYCLE START] {}", summary);
            }

            steps.push(ExplainedStep {
                step_number: global_idx + 1,
                state: state.clone(),
                action_label,
                diff,
                summary,
            });
        }

        ExplainedTrace { steps }
    }
}

impl fmt::Display for ExplainedTrace {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Trace Explanation ({} steps) ===", self.steps.len())?;
        writeln!(f)?;
        for step in &self.steps {
            write!(f, "{}", step)?;
            writeln!(f)?;
        }
        Ok(())
    }
}

/// Build a human-readable summary for a single trace step.
fn build_step_summary(
    step_idx: usize,
    state: &State,
    action_label: &ActionLabel,
    diff: Option<&TraceStateDiff>,
) -> String {
    if step_idx == 0 {
        // Initial state: summarize the initial variable assignments.
        let var_count = state.len();
        return format!(
            "Initial state with {} variable{}",
            var_count,
            if var_count == 1 { "" } else { "s" }
        );
    }

    let Some(diff) = diff else {
        return format!("Action: {}", action_label.name);
    };

    if diff.is_empty() {
        return format!(
            "Stuttering step via {} (no variables changed)",
            action_label.name
        );
    }

    // Build a concise summary of what changed.
    let change_descriptions: Vec<String> = diff
        .changed
        .iter()
        .map(|c| format_var_change_concise(c))
        .collect();

    let changes_text = if change_descriptions.len() <= 3 {
        change_descriptions.join(", ")
    } else {
        // For many changes, show first 3 and a count.
        let first_three = change_descriptions[..3].join(", ");
        format!(
            "{}, and {} more",
            first_three,
            change_descriptions.len() - 3
        )
    };

    format!("{}: {}", action_label.name, changes_text)
}

/// Format a variable change concisely for the summary line.
fn format_var_change_concise(change: &VarChange) -> String {
    match (&change.old_value, &change.new_value) {
        (Some(Value::Bool(a)), Some(Value::Bool(b))) => {
            format!("{}: {} -> {}", change.name, a, b)
        }
        (Some(Value::SmallInt(a)), Some(Value::SmallInt(b))) => {
            format!("{}: {} -> {}", change.name, a, b)
        }
        (Some(Value::String(a)), Some(Value::String(b))) => {
            format!("{}: \"{}\" -> \"{}\"", change.name, a, b)
        }
        (Some(old), Some(new)) => {
            // For complex values, use Display format but truncate if too long.
            let old_str = format!("{}", old);
            let new_str = format!("{}", new);
            let max_val_len = 40;
            let old_display = if old_str.len() > max_val_len {
                format!("{}...", &old_str[..max_val_len])
            } else {
                old_str
            };
            let new_display = if new_str.len() > max_val_len {
                format!("{}...", &new_str[..max_val_len])
            } else {
                new_str
            };
            format!("{}: {} -> {}", change.name, old_display, new_display)
        }
        (None, Some(new)) => {
            format!("{}: (new) -> {}", change.name, new)
        }
        (Some(old), None) => {
            format!("{}: {} -> (removed)", change.name, old)
        }
        (None, None) => {
            format!("{}: (unknown)", change.name)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{State, Trace, Value};

    fn state_xy(x: i64, y: i64) -> State {
        State::from_pairs(vec![("x", Value::SmallInt(x)), ("y", Value::SmallInt(y))])
    }

    fn state_pc(pc_val: &str, step: i64) -> State {
        State::from_pairs(vec![
            ("pc", Value::String(pc_val.into())),
            ("step", Value::SmallInt(step)),
        ])
    }

    // -----------------------------------------------------------------------
    // TraceStateDiff tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_state_diff_no_changes() {
        let s = state_xy(1, 2);
        let diff = TraceStateDiff::compute(&s, &s);
        assert!(diff.is_empty());
        assert_eq!(diff.num_changed(), 0);
        assert_eq!(diff.unchanged_count, 2);
        assert_eq!(diff.total_vars(), 2);
    }

    #[test]
    fn test_state_diff_single_change() {
        let s1 = state_xy(1, 2);
        let s2 = state_xy(3, 2);
        let diff = TraceStateDiff::compute(&s1, &s2);
        assert_eq!(diff.num_changed(), 1);
        assert_eq!(diff.unchanged_count, 1);
        assert_eq!(diff.changed[0].name.as_ref(), "x");
        assert_eq!(diff.changed[0].old_value, Some(Value::SmallInt(1)));
        assert_eq!(diff.changed[0].new_value, Some(Value::SmallInt(3)));
    }

    #[test]
    fn test_state_diff_all_changed() {
        let s1 = state_xy(1, 2);
        let s2 = state_xy(3, 4);
        let diff = TraceStateDiff::compute(&s1, &s2);
        assert_eq!(diff.num_changed(), 2);
        assert_eq!(diff.unchanged_count, 0);
    }

    #[test]
    fn test_state_diff_display() {
        let s1 = state_xy(1, 2);
        let s2 = state_xy(3, 2);
        let diff = TraceStateDiff::compute(&s1, &s2);
        let text = format!("{}", diff);
        assert!(text.contains("x changed from 1 to 3"), "got: {}", text);
    }

    #[test]
    fn test_state_diff_empty_display() {
        let s = state_xy(1, 2);
        let diff = TraceStateDiff::compute(&s, &s);
        let text = format!("{}", diff);
        assert_eq!(text, "(no changes)");
    }

    // -----------------------------------------------------------------------
    // ExplainedTrace tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_explained_trace_initial_state() {
        let trace = Trace::from_states(vec![state_xy(0, 1)]);
        let explained = ExplainedTrace::from_trace(&trace);
        assert_eq!(explained.steps.len(), 1);
        assert_eq!(explained.steps[0].step_number, 1);
        assert!(explained.steps[0].diff.is_none());
        assert!(
            explained.steps[0].summary.contains("Initial state"),
            "got: {}",
            explained.steps[0].summary
        );
    }

    #[test]
    fn test_explained_trace_two_states() {
        let trace = Trace::from_states(vec![state_xy(0, 1), state_xy(1, 1)]);
        let explained = ExplainedTrace::from_trace(&trace);
        assert_eq!(explained.steps.len(), 2);

        // Step 1: initial.
        assert!(explained.steps[0].diff.is_none());

        // Step 2: x changed from 0 to 1.
        let diff = explained.steps[1].diff.as_ref().expect("should have diff");
        assert_eq!(diff.num_changed(), 1);
        assert_eq!(diff.changed[0].name.as_ref(), "x");
        assert!(
            explained.steps[1].summary.contains("x: 0 -> 1"),
            "got: {}",
            explained.steps[1].summary
        );
    }

    #[test]
    fn test_explained_trace_stuttering() {
        let s = state_xy(0, 1);
        let trace = Trace::from_states(vec![s.clone(), s]);
        let explained = ExplainedTrace::from_trace(&trace);
        assert!(
            explained.steps[1].summary.contains("Stuttering step"),
            "got: {}",
            explained.steps[1].summary
        );
        let diff = explained.steps[1].diff.as_ref().expect("should have diff");
        assert!(diff.is_empty());
    }

    #[test]
    fn test_explained_trace_with_action_labels() {
        let states = vec![state_pc("idle", 0), state_pc("running", 1)];
        let labels = vec![
            ActionLabel {
                name: "Initial predicate".to_string(),
                source_location: None,
            },
            ActionLabel {
                name: "Start".to_string(),
                source_location: Some("line 10, col 1 to line 12, col 5 of module Spec".into()),
            },
        ];
        let trace = Trace::from_states_with_labels(states, labels);
        let explained = ExplainedTrace::from_trace(&trace);
        assert_eq!(explained.steps[1].action_label.name, "Start");
        assert!(
            explained.steps[1].summary.contains("Start"),
            "got: {}",
            explained.steps[1].summary
        );
    }

    #[test]
    fn test_explained_trace_display_format() {
        let trace = Trace::from_states(vec![state_xy(0, 0), state_xy(1, 0)]);
        let explained = ExplainedTrace::from_trace(&trace);
        let output = format!("{}", explained);
        assert!(output.contains("=== Trace Explanation (2 steps) ==="));
        assert!(output.contains("--- Step 1 ---"));
        assert!(output.contains("--- Step 2 ---"));
        assert!(output.contains("Initial state"));
        assert!(output.contains("x: 0 -> 1"));
    }

    #[test]
    fn test_explained_trace_many_changes_summary_truncation() {
        // More than 3 variables change: summary should truncate.
        let s1 = State::from_pairs(vec![
            ("a", Value::SmallInt(0)),
            ("b", Value::SmallInt(0)),
            ("c", Value::SmallInt(0)),
            ("d", Value::SmallInt(0)),
            ("e", Value::SmallInt(0)),
        ]);
        let s2 = State::from_pairs(vec![
            ("a", Value::SmallInt(1)),
            ("b", Value::SmallInt(1)),
            ("c", Value::SmallInt(1)),
            ("d", Value::SmallInt(1)),
            ("e", Value::SmallInt(1)),
        ]);
        let trace = Trace::from_states(vec![s1, s2]);
        let explained = ExplainedTrace::from_trace(&trace);
        assert!(
            explained.steps[1].summary.contains("and 2 more"),
            "got: {}",
            explained.steps[1].summary
        );
    }

    #[test]
    fn test_var_change_display() {
        let change = VarChange {
            name: Arc::from("pc"),
            old_value: Some(Value::String("idle".into())),
            new_value: Some(Value::String("running".into())),
        };
        let text = format!("{}", change);
        assert_eq!(text, "pc changed from \"idle\" to \"running\"");
    }

    #[test]
    fn test_explained_liveness_trace() {
        let prefix = Trace::from_states(vec![state_xy(0, 0), state_xy(1, 0)]);
        let cycle = Trace::from_states(vec![state_xy(1, 1), state_xy(1, 0)]);
        let explained = ExplainedTrace::from_liveness_trace(&prefix, &cycle);
        assert_eq!(explained.steps.len(), 4);

        // Step 3 (first cycle state) should be annotated.
        assert!(
            explained.steps[2].summary.contains("[CYCLE START]"),
            "got: {}",
            explained.steps[2].summary
        );
    }

    #[test]
    fn test_string_var_change_concise() {
        let change = VarChange {
            name: Arc::from("status"),
            old_value: Some(Value::String("pending".into())),
            new_value: Some(Value::String("active".into())),
        };
        let concise = format_var_change_concise(&change);
        assert_eq!(concise, "status: \"pending\" -> \"active\"");
    }

    #[test]
    fn test_bool_var_change_concise() {
        let change = VarChange {
            name: Arc::from("flag"),
            old_value: Some(Value::Bool(false)),
            new_value: Some(Value::Bool(true)),
        };
        let concise = format_var_change_concise(&change);
        assert_eq!(concise, "flag: false -> true");
    }

    #[test]
    fn test_int_var_change_concise() {
        let change = VarChange {
            name: Arc::from("count"),
            old_value: Some(Value::SmallInt(5)),
            new_value: Some(Value::SmallInt(6)),
        };
        let concise = format_var_change_concise(&change);
        assert_eq!(concise, "count: 5 -> 6");
    }
}
