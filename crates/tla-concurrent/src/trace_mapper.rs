// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Maps TLA+ counterexample traces back to Rust source locations.
//!
//! When the model checker finds a violation (data race, deadlock, etc.),
//! it produces a counterexample trace expressed in TLA+ states and actions.
//! This module translates those abstract traces into concrete Rust source
//! locations so users see messages like:
//!
//! ```text
//! data race between src/lib.rs:42 and src/lib.rs:87
//! ```
//!
//! instead of raw TLA+ state dumps.

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write;

use crate::model::{ConcurrentModel, ProcessId, StateId};
use crate::property::Property;
use crate::source_map::{MappedStep, MappedTrace, SourceMap, SourceMapEntry, SourceSpan};
use crate::transition::{Transition, TransitionKind};

/// A parsed action name from the TLA+ model.
///
/// Action names follow the format `Action_<process>_<from>_<to>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ParsedActionName {
    pub process: ProcessId,
    pub from_state: StateId,
    pub to_state: StateId,
}

/// Parse an action name of the form `Action_<process>_<from>_<to>`.
///
/// Because process IDs and state IDs can contain underscores, we use
/// a disambiguation strategy: we try to find a matching (process, from, to)
/// triple from the known model processes and their transitions.
pub(crate) fn parse_action_name(
    action_name: &str,
    model: &ConcurrentModel,
) -> Option<ParsedActionName> {
    let rest = action_name.strip_prefix("Action_")?;

    // Try each process to find one whose ID is a prefix of the remainder.
    for process in &model.processes {
        if let Some(after_process) = rest.strip_prefix(&*process.id) {
            let after_process = after_process.strip_prefix('_')?;
            // Try each transition of this process to match from_to.
            for transition in &process.transitions {
                let expected = format!("{}_{}", transition.from, transition.to);
                if after_process == expected {
                    return Some(ParsedActionName {
                        process: process.id.clone(),
                        from_state: transition.from.clone(),
                        to_state: transition.to.clone(),
                    });
                }
            }
        }
    }
    None
}

/// Generate a human-readable tag for a transition kind.
///
/// Delegates to [`TransitionKind::tag()`].
pub(crate) fn transition_tag(kind: &TransitionKind) -> &'static str {
    kind.tag()
}

/// Find the transition in a model matching a parsed action name.
pub(crate) fn find_transition<'a>(
    model: &'a ConcurrentModel,
    parsed: &ParsedActionName,
) -> Option<&'a Transition> {
    model
        .processes
        .iter()
        .find(|p| p.id == parsed.process)?
        .transitions
        .iter()
        .find(|t| t.from == parsed.from_state && t.to == parsed.to_state)
}

/// Convert a source map entry to a source span.
pub(crate) fn entry_to_span(entry: &SourceMapEntry) -> SourceSpan {
    SourceSpan {
        file: entry.rust_file.clone(),
        line: entry.rust_line,
        col: entry.rust_col,
        end_line: entry.rust_end_line,
        end_col: entry.rust_end_col,
    }
}

/// Format a state snapshot as a map of variable name to string value.
#[cfg(feature = "check")]
pub(crate) fn format_state_snapshot(state: &tla_check::State) -> BTreeMap<String, String> {
    state
        .vars()
        .map(|(name, value)| (name.to_string(), format!("{value}")))
        .collect()
}

impl SourceMap {
    /// Build an index from action names to source map entry indices.
    ///
    /// The index maps `Action_<process>_<from>_<to>` names to the index
    /// of the corresponding source map entry.
    pub fn build_action_index(
        &self,
        model: &ConcurrentModel,
    ) -> HashMap<String, usize> {
        let mut index = HashMap::new();
        for process in &model.processes {
            for transition in &process.transitions {
                if let Some(smi) = transition.source_map_index {
                    if smi < self.entries.len() {
                        let action_name = format!(
                            "Action_{}_{}_{}",
                            process.id, transition.from, transition.to
                        );
                        index.insert(action_name, smi);
                    }
                }
            }
        }
        index
    }

    /// Map a TLA+ counterexample trace to Rust source locations.
    #[cfg(feature = "check")]
    pub fn map_trace(
        &self,
        trace: &tla_check::Trace,
        model: &ConcurrentModel,
    ) -> MappedTrace {
        let action_index = self.build_action_index(model);

        let mut steps = Vec::with_capacity(trace.states.len());

        for (i, state) in trace.states.iter().enumerate() {
            let action_label = trace.action_labels.get(i);
            let action_name = action_label.map(|l| l.name.as_str()).unwrap_or("");

            // Try to find source info via the action index
            let (process, tag, rust_location) =
                if let Some(&smi) = action_index.get(action_name) {
                    let entry = &self.entries[smi];
                    (
                        entry.process.clone(),
                        entry.transition_tag.clone(),
                        Some(entry_to_span(entry)),
                    )
                } else if let Some(parsed) = parse_action_name(action_name, model) {
                    // Fallback: parse the action name and look up the transition
                    let transition = find_transition(model, &parsed);
                    let tag = transition
                        .map(|t| transition_tag(&t.kind).to_string())
                        .unwrap_or_else(|| "unknown".to_string());
                    let location = transition
                        .and_then(|t| t.source_map_index)
                        .and_then(|idx| self.entries.get(idx))
                        .map(entry_to_span);
                    (parsed.process, tag, location)
                } else if i == 0 {
                    ("init".to_string(), "initial".to_string(), None)
                } else {
                    ("unknown".to_string(), action_name.to_string(), None)
                };

            steps.push(MappedStep {
                process,
                transition_tag: tag,
                rust_location,
                state_snapshot: format_state_snapshot(state),
            });
        }

        MappedTrace { steps }
    }
}

impl MappedTrace {
    /// Format a human-readable representation of the trace.
    pub fn format_human_readable(&self) -> String {
        let mut out = String::new();
        for (i, step) in self.steps.iter().enumerate() {
            let _ = write!(out, "Step {}: [{}] {}", i + 1, step.process, step.transition_tag);
            if let Some(ref loc) = step.rust_location {
                let _ = write!(out, " at {}:{}:{}", loc.file, loc.line, loc.col);
            }
            let _ = writeln!(out);

            for (var, val) in &step.state_snapshot {
                let _ = writeln!(out, "  {} = {}", var, val);
            }
        }
        out
    }

    /// Format a violation summary suitable for error messages.
    pub fn format_violation_summary(
        &self,
        property: &Property,
        model: &ConcurrentModel,
    ) -> String {
        match property {
            Property::DeadlockFreedom => self.deadlock_summary(),
            Property::DataRaceFreedom => self.data_race_summary(model),
            _ => self.generic_summary(property),
        }
    }

    fn deadlock_summary(&self) -> String {
        let mut out = String::from("Deadlock detected.\n");
        if let Some(last) = self.steps.last() {
            let _ = writeln!(
                out,
                "Final state reached by [{}] via {}",
                last.process, last.transition_tag
            );
            if let Some(ref loc) = last.rust_location {
                let _ = writeln!(out, "  at {}:{}", loc.file, loc.line);
            }
        }
        let _ = writeln!(out, "\nTrace ({} steps):", self.steps.len());
        for (i, step) in self.steps.iter().enumerate() {
            let _ = write!(out, "  {}. [{}] {}", i + 1, step.process, step.transition_tag);
            if let Some(ref loc) = step.rust_location {
                let _ = write!(out, " ({}:{})", loc.file, loc.line);
            }
            let _ = writeln!(out);
        }
        out
    }

    fn data_race_summary(&self, _model: &ConcurrentModel) -> String {
        let mut out = String::from("Data race detected.\n");

        // Collect steps with source locations for the summary
        let located_steps: Vec<_> = self
            .steps
            .iter()
            .filter(|s| s.rust_location.is_some())
            .collect();

        if located_steps.len() >= 2 {
            let a = &located_steps[located_steps.len() - 2];
            let b = &located_steps[located_steps.len() - 1];
            if let (Some(loc_a), Some(loc_b)) = (&a.rust_location, &b.rust_location) {
                let _ = writeln!(
                    out,
                    "Concurrent accesses at:\n  {}:{} ({})\n  {}:{} ({})",
                    loc_a.file, loc_a.line, a.process,
                    loc_b.file, loc_b.line, b.process,
                );
            }
        }

        let _ = writeln!(out, "\nTrace ({} steps):", self.steps.len());
        for (i, step) in self.steps.iter().enumerate() {
            let _ = write!(out, "  {}. [{}] {}", i + 1, step.process, step.transition_tag);
            if let Some(ref loc) = step.rust_location {
                let _ = write!(out, " ({}:{})", loc.file, loc.line);
            }
            let _ = writeln!(out);
        }
        out
    }

    fn generic_summary(&self, property: &Property) -> String {
        let mut out = format!("Property violated: {:?}\n", property);
        let _ = writeln!(out, "\nTrace ({} steps):", self.steps.len());
        for (i, step) in self.steps.iter().enumerate() {
            let _ = write!(out, "  {}. [{}] {}", i + 1, step.process, step.transition_tag);
            if let Some(ref loc) = step.rust_location {
                let _ = write!(out, " ({}:{})", loc.file, loc.line);
            }
            let _ = writeln!(out);
        }
        out
    }
}

/// Format a violation summary for a given property and trace.
///
/// This is the top-level public API for formatting violation messages.
pub fn format_violation_summary(
    property: &Property,
    trace: &MappedTrace,
    model: &ConcurrentModel,
) -> String {
    trace.format_violation_summary(property, model)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assumptions::Assumptions;
    use crate::model::{Process, ProcessKind, SharedVar};
    use crate::source_map::{SourceMap, SourceMapEntry};
    use crate::sync_kind::{SyncKind, SyncPrimitive};
    use crate::transition::{Transition, TransitionKind};

    /// Build a test model with 2 processes, 1 shared var, 1 mutex.
    fn make_test_model() -> ConcurrentModel {
        ConcurrentModel {
            processes: vec![
                Process {
                    id: "main".to_string(),
                    kind: ProcessKind::Main,
                    local_vars: vec![],
                    transitions: vec![
                        Transition {
                            from: "s0".to_string(),
                            to: "s1".to_string(),
                            kind: TransitionKind::Lock {
                                mutex: "mutex_0".to_string(),
                            },
                            source_map_index: Some(0),
                        },
                        Transition {
                            from: "s1".to_string(),
                            to: "done_main".to_string(),
                            kind: TransitionKind::Unlock {
                                mutex: "mutex_0".to_string(),
                            },
                            source_map_index: None,
                        },
                    ],
                    initial_state: "s0".to_string(),
                    terminal_states: vec!["done_main".to_string()],
                },
                Process {
                    id: "worker".to_string(),
                    kind: ProcessKind::Spawned {
                        parent: "main".to_string(),
                        join_handle_in_parent: None,
                    },
                    local_vars: vec![],
                    transitions: vec![
                        Transition {
                            from: "w0".to_string(),
                            to: "w1".to_string(),
                            kind: TransitionKind::Lock {
                                mutex: "mutex_0".to_string(),
                            },
                            source_map_index: Some(1),
                        },
                        Transition {
                            from: "w1".to_string(),
                            to: "done_worker".to_string(),
                            kind: TransitionKind::Unlock {
                                mutex: "mutex_0".to_string(),
                            },
                            source_map_index: None,
                        },
                    ],
                    initial_state: "w0".to_string(),
                    terminal_states: vec!["done_worker".to_string()],
                },
            ],
            shared_vars: vec![SharedVar {
                name: "counter".to_string(),
                field_path: vec![],
                initial_value: Some("0".to_string()),
                access_sites: vec![],
            }],
            sync_primitives: vec![SyncPrimitive {
                id: "mutex_0".to_string(),
                kind: SyncKind::Mutex {
                    reentrant: false,
                    poisonable: true,
                },
                name: None,
            }],
            properties: vec![Property::DeadlockFreedom, Property::DataRaceFreedom],
            assumptions: Assumptions::default(),
            source_map: SourceMap {
                entries: vec![
                    SourceMapEntry {
                        from_state: "s0".to_string(),
                        to_state: "s1".to_string(),
                        process: "main".to_string(),
                        transition_tag: "lock".to_string(),
                        rust_file: "src/lib.rs".to_string(),
                        rust_line: 42,
                        rust_col: 5,
                        rust_end_line: 42,
                        rust_end_col: 30,
                    },
                    SourceMapEntry {
                        from_state: "w0".to_string(),
                        to_state: "w1".to_string(),
                        process: "worker".to_string(),
                        transition_tag: "lock".to_string(),
                        rust_file: "src/lib.rs".to_string(),
                        rust_line: 87,
                        rust_col: 5,
                        rust_end_line: 87,
                        rust_end_col: 30,
                    },
                ],
            },
        }
    }

    #[test]
    fn test_parse_action_name_valid() {
        let model = make_test_model();
        let result = parse_action_name("Action_main_s0_s1", &model);
        assert!(result.is_some(), "should parse a valid action name");
        let parsed = result.unwrap();
        assert_eq!(parsed.process, "main", "process should be 'main'");
        assert_eq!(parsed.from_state, "s0", "from_state should be 's0'");
        assert_eq!(parsed.to_state, "s1", "to_state should be 's1'");
    }

    #[test]
    fn test_parse_action_name_worker() {
        let model = make_test_model();
        let result = parse_action_name("Action_worker_w0_w1", &model);
        assert!(result.is_some(), "should parse worker action name");
        let parsed = result.unwrap();
        assert_eq!(parsed.process, "worker");
        assert_eq!(parsed.from_state, "w0");
        assert_eq!(parsed.to_state, "w1");
    }

    #[test]
    fn test_parse_action_name_invalid() {
        let model = make_test_model();
        assert!(
            parse_action_name("NotAnAction", &model).is_none(),
            "non-Action prefix should return None"
        );
        assert!(
            parse_action_name("Action_unknown_x_y", &model).is_none(),
            "unknown process should return None"
        );
    }

    #[test]
    fn test_build_action_index() {
        let model = make_test_model();
        let index = model.source_map.build_action_index(&model);

        assert_eq!(
            index.get("Action_main_s0_s1"),
            Some(&0),
            "main lock transition should map to source_map_index 0"
        );
        assert_eq!(
            index.get("Action_worker_w0_w1"),
            Some(&1),
            "worker lock transition should map to source_map_index 1"
        );
        assert!(
            index.get("Action_main_s1_done_main").is_none(),
            "transitions without source_map_index should not be indexed"
        );
    }

    #[test]
    fn test_transition_tag_coverage() {
        assert_eq!(
            transition_tag(&TransitionKind::Lock {
                mutex: "m".to_string()
            }),
            "lock"
        );
        assert_eq!(
            transition_tag(&TransitionKind::Spawn {
                child: "c".to_string()
            }),
            "spawn"
        );
        assert_eq!(
            transition_tag(&TransitionKind::ChannelSend {
                channel: "ch".to_string()
            }),
            "channel_send"
        );
        assert_eq!(transition_tag(&TransitionKind::Park), "park");
    }

    #[test]
    fn test_format_human_readable() {
        let trace = MappedTrace {
            steps: vec![
                MappedStep {
                    process: "main".to_string(),
                    transition_tag: "initial".to_string(),
                    rust_location: None,
                    state_snapshot: BTreeMap::from([
                        ("counter".to_string(), "0".to_string()),
                    ]),
                },
                MappedStep {
                    process: "main".to_string(),
                    transition_tag: "lock".to_string(),
                    rust_location: Some(SourceSpan {
                        file: "src/lib.rs".to_string(),
                        line: 42,
                        col: 5,
                        end_line: 42,
                        end_col: 30,
                    }),
                    state_snapshot: BTreeMap::from([
                        ("counter".to_string(), "1".to_string()),
                    ]),
                },
            ],
        };

        let output = trace.format_human_readable();
        assert!(
            output.contains("src/lib.rs:42:5"),
            "should contain source location, got: {output}"
        );
        assert!(
            output.contains("[main]"),
            "should contain process name, got: {output}"
        );
        assert!(
            output.contains("counter = 0"),
            "should contain initial state, got: {output}"
        );
    }

    #[test]
    fn test_format_violation_summary_deadlock() {
        let model = make_test_model();
        let trace = MappedTrace {
            steps: vec![
                MappedStep {
                    process: "main".to_string(),
                    transition_tag: "lock".to_string(),
                    rust_location: Some(SourceSpan {
                        file: "src/lib.rs".to_string(),
                        line: 42,
                        col: 5,
                        end_line: 42,
                        end_col: 30,
                    }),
                    state_snapshot: BTreeMap::new(),
                },
                MappedStep {
                    process: "worker".to_string(),
                    transition_tag: "lock".to_string(),
                    rust_location: Some(SourceSpan {
                        file: "src/lib.rs".to_string(),
                        line: 87,
                        col: 5,
                        end_line: 87,
                        end_col: 30,
                    }),
                    state_snapshot: BTreeMap::new(),
                },
            ],
        };

        let summary = format_violation_summary(
            &Property::DeadlockFreedom,
            &trace,
            &model,
        );
        assert!(
            summary.contains("Deadlock detected"),
            "deadlock summary should mention deadlock, got: {summary}"
        );
        assert!(
            summary.contains("src/lib.rs:87"),
            "should reference last step location, got: {summary}"
        );
    }

    #[test]
    fn test_format_violation_summary_data_race() {
        let model = make_test_model();
        let trace = MappedTrace {
            steps: vec![
                MappedStep {
                    process: "main".to_string(),
                    transition_tag: "lock".to_string(),
                    rust_location: Some(SourceSpan {
                        file: "src/lib.rs".to_string(),
                        line: 42,
                        col: 5,
                        end_line: 42,
                        end_col: 30,
                    }),
                    state_snapshot: BTreeMap::new(),
                },
                MappedStep {
                    process: "worker".to_string(),
                    transition_tag: "lock".to_string(),
                    rust_location: Some(SourceSpan {
                        file: "src/lib.rs".to_string(),
                        line: 87,
                        col: 5,
                        end_line: 87,
                        end_col: 30,
                    }),
                    state_snapshot: BTreeMap::new(),
                },
            ],
        };

        let summary = format_violation_summary(
            &Property::DataRaceFreedom,
            &trace,
            &model,
        );
        assert!(
            summary.contains("Data race detected"),
            "data race summary should mention data race, got: {summary}"
        );
        assert!(
            summary.contains("src/lib.rs:42"),
            "should reference first access location, got: {summary}"
        );
        assert!(
            summary.contains("src/lib.rs:87"),
            "should reference second access location, got: {summary}"
        );
    }
}
