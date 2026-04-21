// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
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
pub(crate) fn check_result_to_report(
    result: &tla_check::CheckResult,
    model: &ConcurrentModel,
) -> VerificationReport {
    let stats = result.stats();
    let checker_stats = CheckerStats {
        states_found: stats.states_found,
        distinct_states: stats.states_found, // TODO: extract distinct from CheckStats
        initial_states: stats.initial_states,
        duration_ms: 0, // TODO: extract duration
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
