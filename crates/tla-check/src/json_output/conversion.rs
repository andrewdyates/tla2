// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Conversion logic: CheckResult to JsonOutput builders, trace formatting.

use super::diagnostics::error_codes;
use super::error_mapping::{error_code_from_check_error, suggestion_from_check_error};
use super::types::*;
use crate::{CheckResult, CheckStats, PropertyViolationKind, Trace};
use std::collections::HashMap;
use std::time::Duration;

pub use crate::json_codec::value_to_json;
use crate::RuntimeCheckError;

impl JsonOutput {
    pub fn with_soundness(mut self, soundness: SoundnessProvenance) -> Self {
        self.soundness = soundness;
        self
    }

    pub fn with_completeness(mut self, completeness: SearchCompleteness) -> Self {
        self.completeness = completeness;
        self
    }

    pub fn with_cli_error(
        mut self,
        error_code: &str,
        error_message: impl Into<String>,
        suggestion: Option<ErrorSuggestion>,
    ) -> Self {
        self.result.status = "error".to_string();
        self.result.error_type = Some("cli_error".to_string());
        self.result.error_code = Some(error_code.to_string());
        self.result.error_message = Some(error_message.into());
        self.result.suggestion = suggestion;
        self
    }

    /// Set specification info
    pub fn with_spec_info(
        mut self,
        init: Option<&str>,
        next: Option<&str>,
        invariants: Vec<String>,
        properties: Vec<String>,
        variables: Vec<String>,
    ) -> Self {
        self.specification.init = init.map(String::from);
        self.specification.next = next.map(String::from);
        self.specification.invariants = invariants;
        self.specification.properties = properties;
        self.specification.variables = variables;
        self
    }

    /// Set result from CheckResult
    pub fn with_check_result(mut self, result: &CheckResult, elapsed: Duration) -> Self {
        match result {
            CheckResult::Success(stats) => {
                self.result.status = "ok".to_string();
                self.statistics = stats_to_json(stats, elapsed);
                if let Some(ref coverage) = stats.coverage {
                    self.actions_detected = coverage
                        .action_order
                        .iter()
                        .filter_map(|id| coverage.actions.get(id))
                        .map(|a| ActionInfo {
                            id: a.id.to_string(),
                            name: a.name.clone(),
                            occurrences: a.transitions,
                            percentage: if coverage.total_transitions > 0 {
                                Some(
                                    a.transitions as f64 / coverage.total_transitions as f64
                                        * 100.0,
                                )
                            } else {
                                None
                            },
                        })
                        .collect();
                } else if !stats.detected_actions.is_empty() {
                    self.actions_detected = stats
                        .detected_actions
                        .iter()
                        .enumerate()
                        .map(|(idx, name)| ActionInfo {
                            // Preserve distinct ids even when this CheckStats
                            // snapshot predates detected_action_ids plumbing.
                            id: stats
                                .detected_action_ids
                                .get(idx)
                                .cloned()
                                .unwrap_or_else(|| format!("detected:{idx}")),
                            name: name.clone(),
                            occurrences: 0,
                            percentage: None,
                        })
                        .collect();
                }
                canonicalize_action_ids(&mut self.actions_detected);
            }
            CheckResult::InvariantViolation {
                invariant,
                trace,
                stats,
            } => {
                self.result.status = "error".to_string();
                self.result.error_type = Some("invariant_violation".to_string());
                self.result.error_code = Some(error_codes::TLC_INVARIANT_VIOLATED.to_string());
                self.result.error_message = Some(format!("Invariant '{}' violated", invariant));
                self.result.violated_property = Some(ViolatedProperty {
                    name: invariant.clone(),
                    prop_type: "invariant".to_string(),
                    location: None,
                    expression: None,
                });
                self.result.suggestion = Some(ErrorSuggestion {
                    action: "Examine the counterexample trace to understand why the invariant fails".to_string(),
                    example: Some(format!(
                        "Check the definition of {} and verify it holds for the final state in the trace",
                        invariant
                    )),
                    options: vec![
                        "Add CONSTRAINT to limit state space".to_string(),
                        "Strengthen invariant preconditions".to_string(),
                        "Fix the Next action that causes the violation".to_string(),
                    ],
                });
                self.counterexample = Some(trace_to_counterexample(trace, None));
                self.statistics = stats_to_json(stats, elapsed);
            }
            CheckResult::PropertyViolation {
                property,
                kind,
                trace,
                stats,
            } => {
                self.result.status = "error".to_string();
                // Part of #3106: StateLevel properties ([]P) are semantically invariants.
                // TLC reports them as "Invariant X is violated." and classifies the error
                // as "invariant". Match that in JSON so diagnose error_type comparison passes.
                let (error_type, error_code, prop_type, msg) = match kind {
                    PropertyViolationKind::StateLevel => (
                        "invariant_violation",
                        error_codes::TLC_INVARIANT_VIOLATED,
                        "invariant",
                        format!("Invariant '{}' violated", property),
                    ),
                    PropertyViolationKind::ActionLevel => (
                        "property_violation",
                        error_codes::TLC_PROPERTY_VIOLATED,
                        "property",
                        format!("Property '{}' violated", property),
                    ),
                };
                self.result.error_type = Some(error_type.to_string());
                self.result.error_code = Some(error_code.to_string());
                self.result.error_message = Some(msg);
                self.result.violated_property = Some(ViolatedProperty {
                    name: property.clone(),
                    prop_type: prop_type.to_string(),
                    location: None,
                    expression: None,
                });
                self.result.suggestion = Some(ErrorSuggestion {
                    action: "Review the counterexample trace to identify the property violation"
                        .to_string(),
                    example: None,
                    options: vec![],
                });
                self.counterexample = Some(trace_to_counterexample(trace, None));
                self.statistics = stats_to_json(stats, elapsed);
            }
            CheckResult::LivenessViolation {
                property,
                prefix,
                cycle,
                stats,
            } => {
                self.result.status = "error".to_string();
                self.result.error_type = Some("liveness_violation".to_string());
                self.result.error_code = Some(error_codes::TLC_LIVENESS_VIOLATED.to_string());
                self.result.error_message =
                    Some(format!("Liveness property '{}' violated", property));
                self.result.violated_property = Some(ViolatedProperty {
                    name: property.clone(),
                    prop_type: "liveness".to_string(),
                    location: None,
                    expression: None,
                });
                self.result.suggestion = Some(ErrorSuggestion {
                    action:
                        "The trace shows a cycle where the liveness property never becomes true"
                            .to_string(),
                    example: Some(
                        "Check for missing fairness constraints (WF_ or SF_)".to_string(),
                    ),
                    options: vec![
                        "Add weak fairness: WF_vars(Action)".to_string(),
                        "Add strong fairness: SF_vars(Action)".to_string(),
                        "Check for blocking conditions in the cycle".to_string(),
                    ],
                });
                let loop_start = prefix.states.len();
                let mut combined_trace = prefix.clone();
                for state in &cycle.states {
                    combined_trace.states.push(state.clone());
                }
                for label in &cycle.action_labels {
                    combined_trace.action_labels.push(label.clone());
                }
                self.counterexample =
                    Some(trace_to_counterexample(&combined_trace, Some(loop_start)));
                self.statistics = stats_to_json(stats, elapsed);
            }
            CheckResult::Deadlock { trace, stats } => {
                self.result.status = "error".to_string();
                self.result.error_type = Some("deadlock".to_string());
                self.result.error_code = Some(error_codes::TLC_DEADLOCK.to_string());
                self.result.error_message =
                    Some("Deadlock detected: no enabled actions".to_string());
                self.result.suggestion = Some(ErrorSuggestion {
                    action: "No action is enabled in the final state".to_string(),
                    example: Some("Use --no-deadlock if this is expected, or add TERMINAL in config for intentional final states".to_string()),
                    options: vec![
                        "Add --no-deadlock flag to disable deadlock checking".to_string(),
                        "Add TERMINAL state = \"value\" to config for expected final states".to_string(),
                        "Fix the Next relation to enable an action".to_string(),
                    ],
                });
                self.counterexample = Some(trace_to_counterexample(trace, None));
                self.statistics = stats_to_json(stats, elapsed);
            }
            CheckResult::Error { error, stats, .. } => {
                self.result.status = "error".to_string();
                // Distinguish ASSUME violations from general runtime errors.
                // TLC reports assume_violation as a separate error type; diagnose
                // compares error_type strings, so we must emit the matching string.
                self.result.error_type = Some(
                    match error {
                        crate::CheckError::Runtime(RuntimeCheckError::AssumeFalse { .. }) => {
                            "assume_violation"
                        }
                        _ => "runtime_error",
                    }
                    .to_string(),
                );
                self.result.error_code = Some(error_code_from_check_error(error));
                self.result.error_message = Some(error.to_string());
                self.result.suggestion = suggestion_from_check_error(error);
                self.statistics = stats_to_json(stats, elapsed);
            }
            CheckResult::LimitReached { limit_type, stats } => {
                self.result.status = "limit_reached".to_string();
                self.result.error_type = Some(
                    match limit_type {
                        crate::LimitType::States => "state_limit",
                        crate::LimitType::Depth => "depth_limit",
                        crate::LimitType::Exit => "exit_requested",
                        crate::LimitType::Memory => "memory_limit",
                        crate::LimitType::Disk => "disk_limit",
                    }
                    .to_string(),
                );
                self.result.error_code = Some(error_codes::TLC_LIMIT_REACHED.to_string());
                self.result.error_message = Some(format!("{:?} limit reached", limit_type));
                self.result.suggestion = Some(ErrorSuggestion {
                    action: "The model checking stopped due to a configured limit".to_string(),
                    example: Some(
                        "Use --max-states 0 or --max-depth 0 to disable limits".to_string(),
                    ),
                    options: vec![
                        "Increase --max-states to explore more states".to_string(),
                        "Increase --max-depth to explore deeper".to_string(),
                        "Add CONSTRAINT to reduce state space".to_string(),
                    ],
                });
                self.statistics = stats_to_json(stats, elapsed);
            }
        }

        if let Some(msg) =
            crate::guard_error_stats::render_warning(result.suppressed_guard_errors())
        {
            self.add_warning(error_codes::TLC_GUARD_ERRORS_SUPPRESSED, &msg);
        }
        self
    }
}

/// Convert CheckStats to StatisticsInfo
fn stats_to_json(stats: &CheckStats, elapsed: Duration) -> StatisticsInfo {
    let time_secs = elapsed.as_secs_f64();
    StatisticsInfo {
        states_found: stats.states_found,
        states_initial: stats.initial_states,
        states_distinct: Some(stats.states_found),
        transitions: stats.transitions,
        suppressed_guard_errors: (stats.suppressed_guard_errors > 0)
            .then_some(stats.suppressed_guard_errors),
        max_depth: Some(stats.max_depth),
        max_queue_depth: Some(stats.max_queue_depth),
        time_seconds: time_secs,
        states_per_second: if time_secs > 0.0 {
            Some(stats.states_found as f64 / time_secs)
        } else {
            None
        },
        memory_mb: None,
        // Part of #2665: include storage backend stats when disk tier activity
        // or reserved-memory usage would be useful to downstream tooling.
        storage: {
            let ss = &stats.storage_stats;
            if ss.disk_count > 0
                || ss.eviction_count > 0
                || ss.disk_lookups > 0
                || ss.memory_bytes > 0
            {
                Some(StorageStatsInfo {
                    memory_count: ss.memory_count,
                    disk_count: ss.disk_count,
                    memory_bytes: (ss.memory_bytes > 0).then_some(ss.memory_bytes),
                    disk_lookups: (ss.disk_lookups > 0).then_some(ss.disk_lookups),
                    disk_hits: (ss.disk_hits > 0).then_some(ss.disk_hits),
                    eviction_count: (ss.eviction_count > 0).then_some(ss.eviction_count),
                })
            } else {
                None
            }
        },
    }
}

/// Convert Trace to CounterexampleInfo with state diffs
fn trace_to_counterexample(trace: &Trace, loop_start: Option<usize>) -> CounterexampleInfo {
    use crate::State;

    let mut states = Vec::new();
    let mut prev_state: Option<&State> = None;

    for (i, state) in trace.states.iter().enumerate() {
        let variables: HashMap<String, JsonValue> = state
            .vars()
            .map(|(k, v)| (k.to_string(), value_to_json(v)))
            .collect();

        let diff = if let Some(prev) = prev_state {
            let mut changed = HashMap::new();
            let mut unchanged = Vec::new();

            for (var, new_val) in state.vars() {
                if let Some(old_val) = prev.get(var) {
                    if old_val != new_val {
                        changed.insert(
                            var.to_string(),
                            ValueChange {
                                from: value_to_json(old_val),
                                to: value_to_json(new_val),
                            },
                        );
                    } else {
                        unchanged.push(var.to_string());
                    }
                } else {
                    changed.insert(
                        var.to_string(),
                        ValueChange {
                            from: JsonValue::Undefined,
                            to: value_to_json(new_val),
                        },
                    );
                }
            }

            Some(StateDiff { changed, unchanged })
        } else {
            None
        };

        let action_type = if i == 0 { "initial" } else { "next" };
        let action_name = if let Some(label) = trace.action_labels.get(i) {
            label.name.clone()
        } else if i == 0 {
            "Init".to_string()
        } else {
            "Next".to_string()
        };

        states.push(StateInfo {
            index: i + 1,
            fingerprint: Some(format!("{:016x}", state.fingerprint().0)),
            action: ActionRef {
                name: action_name,
                action_type: action_type.to_string(),
                location: None,
            },
            variables,
            diff_from_previous: diff,
        });

        prev_state = Some(state);
    }

    CounterexampleInfo {
        length: states.len(),
        states,
        loop_start: loop_start.map(|s| s + 1),
    }
}
