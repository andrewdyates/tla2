// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structured output for tRust consumption.

use serde::{Deserialize, Serialize};

use crate::model::ConcurrentModel;
use crate::source_map::MappedTrace;

/// Structured verification report.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationReport {
    /// Overall status.
    pub status: VerificationStatus,
    /// Which property was violated (if any).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub violated_property: Option<String>,
    /// Source-mapped counterexample trace (if violation found).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample: Option<MappedTrace>,
    /// Source-mapped liveness counterexample prefix (if liveness violation).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub liveness_prefix: Option<MappedTrace>,
    /// Source-mapped liveness counterexample cycle (if liveness violation).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub liveness_cycle: Option<MappedTrace>,
    /// Statistics from the model checker.
    pub stats: CheckerStats,
}

/// Overall verification outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum VerificationStatus {
    /// All properties hold under stated assumptions.
    AllPropertiesHold,
    /// A safety property (invariant) was violated.
    InvariantViolation,
    /// A temporal property was violated.
    PropertyViolation,
    /// A liveness property was violated.
    LivenessViolation,
    /// Deadlock detected.
    DeadlockDetected,
    /// An error occurred during checking.
    Error,
    /// Exploration limit reached.
    LimitReached,
}

/// Statistics from the model checker run.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CheckerStats {
    pub states_found: usize,
    pub distinct_states: usize,
    pub initial_states: usize,
    pub duration_ms: u64,
}

/// Convert a tla-check `CheckResult` into a `VerificationReport`.
///
/// `duration_ms` is the wall-clock time for the model-checking phase,
/// measured by the caller (`check_concurrent_model`).
pub(crate) fn check_result_to_report(
    result: &tla_check::CheckResult,
    model: &ConcurrentModel,
    duration_ms: u64,
) -> VerificationReport {
    let stats = result.stats();
    // CheckStats::states_found is already the distinct state count
    // (documented as "Number of distinct states explored").
    let checker_stats = CheckerStats {
        states_found: stats.states_found,
        distinct_states: stats.states_found,
        initial_states: stats.initial_states,
        duration_ms,
    };

    match result {
        tla_check::CheckResult::Success(_) => VerificationReport {
            status: VerificationStatus::AllPropertiesHold,
            violated_property: None,
            counterexample: None,
            liveness_prefix: None,
            liveness_cycle: None,
            stats: checker_stats,
        },
        tla_check::CheckResult::InvariantViolation {
            invariant, trace, ..
        } => VerificationReport {
            status: VerificationStatus::InvariantViolation,
            violated_property: Some(invariant.clone()),
            counterexample: Some(model.source_map.map_trace(trace, model)),
            liveness_prefix: None,
            liveness_cycle: None,
            stats: checker_stats,
        },
        tla_check::CheckResult::PropertyViolation {
            property, trace, ..
        } => VerificationReport {
            status: VerificationStatus::PropertyViolation,
            violated_property: Some(property.clone()),
            counterexample: Some(model.source_map.map_trace(trace, model)),
            liveness_prefix: None,
            liveness_cycle: None,
            stats: checker_stats,
        },
        tla_check::CheckResult::LivenessViolation {
            property,
            prefix,
            cycle,
            ..
        } => VerificationReport {
            status: VerificationStatus::LivenessViolation,
            violated_property: Some(property.clone()),
            counterexample: None,
            liveness_prefix: Some(model.source_map.map_trace(prefix, model)),
            liveness_cycle: Some(model.source_map.map_trace(cycle, model)),
            stats: checker_stats,
        },
        tla_check::CheckResult::Deadlock { trace, .. } => VerificationReport {
            status: VerificationStatus::DeadlockDetected,
            violated_property: Some("DeadlockFreedom".to_string()),
            counterexample: Some(model.source_map.map_trace(trace, model)),
            liveness_prefix: None,
            liveness_cycle: None,
            stats: checker_stats,
        },
        tla_check::CheckResult::Error { error, .. } => VerificationReport {
            status: VerificationStatus::Error,
            violated_property: Some(format!("{error}")),
            counterexample: None,
            liveness_prefix: None,
            liveness_cycle: None,
            stats: checker_stats,
        },
        tla_check::CheckResult::LimitReached { limit_type, .. } => VerificationReport {
            status: VerificationStatus::LimitReached,
            violated_property: Some(format!("{limit_type:?}")),
            counterexample: None,
            liveness_prefix: None,
            liveness_cycle: None,
            stats: checker_stats,
        },
        // Non-exhaustive — handle future variants gracefully
        _ => VerificationReport {
            status: VerificationStatus::Error,
            violated_property: Some("unknown check result variant".to_string()),
            counterexample: None,
            liveness_prefix: None,
            liveness_cycle: None,
            stats: checker_stats,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_map::{MappedStep, MappedTrace, SourceSpan};
    use std::collections::BTreeMap;

    #[test]
    fn test_checker_stats_duration_ms_passes_through() {
        let stats = CheckerStats {
            states_found: 42,
            distinct_states: 42,
            initial_states: 1,
            duration_ms: 999,
        };
        assert_eq!(stats.duration_ms, 999);
        assert_eq!(stats.states_found, 42);
        assert_eq!(stats.distinct_states, 42);
    }

    #[test]
    fn test_verification_report_serialization_round_trip() {
        let report = VerificationReport {
            status: VerificationStatus::AllPropertiesHold,
            violated_property: None,
            counterexample: None,
            liveness_prefix: None,
            liveness_cycle: None,
            stats: CheckerStats {
                states_found: 100,
                distinct_states: 100,
                initial_states: 2,
                duration_ms: 500,
            },
        };
        let json = serde_json::to_string(&report)
            .expect("VerificationReport should serialize");
        let parsed: VerificationReport = serde_json::from_str(&json)
            .expect("VerificationReport should deserialize");
        assert_eq!(parsed.status, VerificationStatus::AllPropertiesHold);
        assert_eq!(parsed.stats.duration_ms, 500);
        assert_eq!(parsed.stats.distinct_states, 100);
        assert!(parsed.counterexample.is_none());
    }

    #[test]
    fn test_deadlock_report_with_source_mapped_trace() {
        // Simulate what check_result_to_report produces for a deadlock:
        // An ABBA deadlock trace where thread_a locks mu_x and thread_b locks mu_y.
        let trace = MappedTrace {
            steps: vec![
                MappedStep {
                    process: "init".to_string(),
                    transition_tag: "initial".to_string(),
                    rust_location: None,
                    state_snapshot: BTreeMap::from([
                        ("mu_x_holder".to_string(), "None".to_string()),
                        ("mu_y_holder".to_string(), "None".to_string()),
                    ]),
                },
                MappedStep {
                    process: "thread_a".to_string(),
                    transition_tag: "lock".to_string(),
                    rust_location: Some(SourceSpan {
                        file: "src/main.rs".to_string(),
                        line: 10,
                        col: 5,
                        end_line: 10,
                        end_col: 25,
                    }),
                    state_snapshot: BTreeMap::from([
                        ("mu_x_holder".to_string(), "thread_a".to_string()),
                        ("mu_y_holder".to_string(), "None".to_string()),
                    ]),
                },
                MappedStep {
                    process: "thread_b".to_string(),
                    transition_tag: "lock".to_string(),
                    rust_location: Some(SourceSpan {
                        file: "src/main.rs".to_string(),
                        line: 20,
                        col: 5,
                        end_line: 20,
                        end_col: 25,
                    }),
                    state_snapshot: BTreeMap::from([
                        ("mu_x_holder".to_string(), "thread_a".to_string()),
                        ("mu_y_holder".to_string(), "thread_b".to_string()),
                    ]),
                },
            ],
        };

        let report = VerificationReport {
            status: VerificationStatus::DeadlockDetected,
            violated_property: Some("DeadlockFreedom".to_string()),
            counterexample: Some(trace),
            liveness_prefix: None,
            liveness_cycle: None,
            stats: CheckerStats {
                states_found: 5,
                distinct_states: 5,
                initial_states: 1,
                duration_ms: 42,
            },
        };

        assert_eq!(report.status, VerificationStatus::DeadlockDetected);
        assert_eq!(report.stats.duration_ms, 42);

        let cx = report
            .counterexample
            .as_ref()
            .expect("deadlock report should have counterexample");
        assert_eq!(cx.steps.len(), 3);

        // Step 0: initial -- no source location
        assert_eq!(cx.steps[0].process, "init");
        assert!(cx.steps[0].rust_location.is_none());

        // Step 1: thread_a locks mu_x at src/main.rs:10:5
        assert_eq!(cx.steps[1].process, "thread_a");
        assert_eq!(cx.steps[1].transition_tag, "lock");
        let loc1 = cx.steps[1].rust_location.as_ref()
            .expect("thread_a lock should have source location");
        assert_eq!(loc1.file, "src/main.rs");
        assert_eq!(loc1.line, 10);

        // Step 2: thread_b locks mu_y at src/main.rs:20:5
        assert_eq!(cx.steps[2].process, "thread_b");
        let loc2 = cx.steps[2].rust_location.as_ref()
            .expect("thread_b lock should have source location");
        assert_eq!(loc2.file, "src/main.rs");
        assert_eq!(loc2.line, 20);

        // Human-readable output should contain both source locations
        let readable = cx.format_human_readable();
        assert!(
            readable.contains("src/main.rs:10:5"),
            "readable should contain thread_a source, got: {readable}"
        );
        assert!(
            readable.contains("src/main.rs:20:5"),
            "readable should contain thread_b source, got: {readable}"
        );
        assert!(
            readable.contains("[thread_a]"),
            "readable should contain process name, got: {readable}"
        );

        // JSON round-trip preserves source locations
        let json = serde_json::to_string(&report)
            .expect("report with trace should serialize");
        let parsed: VerificationReport = serde_json::from_str(&json)
            .expect("report with trace should deserialize");
        let parsed_cx = parsed.counterexample
            .expect("parsed report should have counterexample");
        assert_eq!(parsed_cx.steps[1].rust_location.as_ref().unwrap().line, 10);
        assert_eq!(parsed_cx.steps[2].rust_location.as_ref().unwrap().line, 20);
    }

    #[test]
    fn test_liveness_report_has_prefix_and_cycle() {
        let prefix = MappedTrace {
            steps: vec![MappedStep {
                process: "init".to_string(),
                transition_tag: "initial".to_string(),
                rust_location: None,
                state_snapshot: BTreeMap::new(),
            }],
        };
        let cycle = MappedTrace {
            steps: vec![
                MappedStep {
                    process: "worker".to_string(),
                    transition_tag: "park".to_string(),
                    rust_location: Some(SourceSpan {
                        file: "src/worker.rs".to_string(),
                        line: 55,
                        col: 9,
                        end_line: 55,
                        end_col: 20,
                    }),
                    state_snapshot: BTreeMap::new(),
                },
                MappedStep {
                    process: "worker".to_string(),
                    transition_tag: "park".to_string(),
                    rust_location: Some(SourceSpan {
                        file: "src/worker.rs".to_string(),
                        line: 55,
                        col: 9,
                        end_line: 55,
                        end_col: 20,
                    }),
                    state_snapshot: BTreeMap::new(),
                },
            ],
        };

        let report = VerificationReport {
            status: VerificationStatus::LivenessViolation,
            violated_property: Some("EventuallyDone".to_string()),
            counterexample: None,
            liveness_prefix: Some(prefix),
            liveness_cycle: Some(cycle),
            stats: CheckerStats {
                states_found: 20,
                distinct_states: 20,
                initial_states: 1,
                duration_ms: 300,
            },
        };

        assert_eq!(report.status, VerificationStatus::LivenessViolation);
        assert!(report.counterexample.is_none());
        assert!(report.liveness_prefix.is_some());
        assert!(report.liveness_cycle.is_some());

        let cycle_trace = report.liveness_cycle.as_ref().unwrap();
        assert_eq!(cycle_trace.steps.len(), 2);
        assert_eq!(
            cycle_trace.steps[0].rust_location.as_ref().unwrap().file,
            "src/worker.rs"
        );
    }
}
