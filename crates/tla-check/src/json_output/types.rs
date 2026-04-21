// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Type definitions for the JSON output format.
//!
//! All struct/enum types used in the structured JSON output for AI agents
//! and automated tooling.

use serde::{Deserialize, Deserializer, Serialize};
use std::collections::{HashMap, HashSet};
use std::path::Path;

pub use super::trace_types::{
    ActionRef, CounterexampleInfo, JsonValue, StateDiff, StateInfo, ValueChange,
};

/// Version of the JSON output format
pub const OUTPUT_VERSION: &str = "1.3";

/// Soundness classification for the run path (engine parity / experimental status).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum SoundnessMode {
    /// Claimed TLC-equivalent semantics for the selected engine path.
    Sound,
    /// Intended to be sound, but not yet proven / validated for parity.
    Experimental,
    /// Heuristic / incomplete engine (e.g., abstraction, subset support).
    Heuristic,
}

/// Soundness provenance record for CLI outputs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub struct SoundnessProvenance {
    pub mode: SoundnessMode,
    pub features_used: Vec<String>,
    pub deviations: Vec<String>,
    pub assumptions: Vec<String>,
}

impl SoundnessProvenance {
    pub fn sound() -> Self {
        Self {
            mode: SoundnessMode::Sound,
            features_used: Vec::new(),
            deviations: Vec::new(),
            assumptions: Vec::new(),
        }
    }
}

/// Search completeness classification (exhaustive vs user-configured bounds).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum SearchCompleteness {
    Exhaustive,
    BoundedDepth { max_depth: usize },
    BoundedStates { max_states: usize },
    Bounded { max_depth: usize, max_states: usize },
}

impl SearchCompleteness {
    pub fn from_bounds(max_states: usize, max_depth: usize) -> Self {
        match (max_states, max_depth) {
            (0, 0) => SearchCompleteness::Exhaustive,
            (0, d) => SearchCompleteness::BoundedDepth { max_depth: d },
            (s, 0) => SearchCompleteness::BoundedStates { max_states: s },
            (s, d) => SearchCompleteness::Bounded {
                max_depth: d,
                max_states: s,
            },
        }
    }

    pub fn is_exhaustive(self) -> bool {
        matches!(self, SearchCompleteness::Exhaustive)
    }

    pub fn format_human(self) -> String {
        match self {
            SearchCompleteness::Exhaustive => "exhaustive".to_string(),
            SearchCompleteness::BoundedDepth { max_depth } => {
                format!("bounded (max_depth={})", max_depth)
            }
            SearchCompleteness::BoundedStates { max_states } => {
                format!("bounded (max_states={})", max_states)
            }
            SearchCompleteness::Bounded {
                max_depth,
                max_states,
            } => format!(
                "bounded (max_states={}, max_depth={})",
                max_states, max_depth
            ),
        }
    }
}

/// Complete JSON output for model checking results
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct JsonOutput {
    /// Schema version
    pub version: String,
    /// Tool identifier
    pub tool: String,
    /// ISO 8601 timestamp
    pub timestamp: String,
    /// Input files and configuration
    pub input: InputInfo,
    /// Specification details
    pub specification: SpecInfo,
    /// Soundness provenance
    pub soundness: SoundnessProvenance,
    /// Search completeness (exhaustive vs bounded)
    pub completeness: SearchCompleteness,
    /// Model checking result
    pub result: ResultInfo,
    /// Counterexample trace (if any)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample: Option<CounterexampleInfo>,
    /// Statistics
    pub statistics: StatisticsInfo,
    /// Diagnostic messages
    pub diagnostics: DiagnosticsInfo,
    /// Action coverage information
    #[serde(
        skip_serializing_if = "Vec::is_empty",
        default,
        deserialize_with = "deserialize_actions_detected"
    )]
    pub actions_detected: Vec<ActionInfo>,
}

/// Input file information
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct InputInfo {
    pub spec_file: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub config_file: Option<String>,
    pub module: String,
    pub workers: usize,
}

/// Specification structure
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct SpecInfo {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub init: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub next: Option<String>,
    pub invariants: Vec<String>,
    pub properties: Vec<String>,
    pub constants: HashMap<String, JsonValue>,
    pub variables: Vec<String>,
}

/// Model checking result
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ResultInfo {
    /// Status: "ok", "error", "timeout", "interrupted", "limit_reached"
    pub status: String,
    /// Error type if status is "error"
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error_type: Option<String>,
    /// Structured error code for programmatic handling
    ///
    /// Error codes follow a prefix convention:
    /// - `TLC_` - Model checker errors (deadlock, invariant violation, etc.)
    /// - `CFG_` - Configuration file parsing errors
    /// - `TLA_` - TLA+ source parsing errors
    /// - `SYS_` - System/runtime errors
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error_code: Option<String>,
    /// Human-readable error message
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error_message: Option<String>,
    /// Details about violated property
    #[serde(skip_serializing_if = "Option::is_none")]
    pub violated_property: Option<ViolatedProperty>,
    /// Actionable suggestion for fixing the error
    #[serde(skip_serializing_if = "Option::is_none")]
    pub suggestion: Option<ErrorSuggestion>,
}

/// Actionable suggestion for fixing an error
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ErrorSuggestion {
    /// Brief description of the suggested action
    pub action: String,
    /// Example code or configuration fix
    #[serde(skip_serializing_if = "Option::is_none")]
    pub example: Option<String>,
    /// Alternative options if applicable
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub options: Vec<String>,
}

impl ErrorSuggestion {
    pub fn new(action: impl Into<String>) -> Self {
        Self {
            action: action.into(),
            example: None,
            options: Vec::new(),
        }
    }

    pub fn with_example(mut self, example: impl Into<String>) -> Self {
        self.example = Some(example.into());
        self
    }

    pub fn with_options(mut self, options: Vec<String>) -> Self {
        self.options = options;
        self
    }
}

/// Information about a violated property
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ViolatedProperty {
    pub name: String,
    /// Type: "invariant", "liveness", "assertion"
    #[serde(rename = "type")]
    pub prop_type: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expression: Option<String>,
}

/// Source code location
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct SourceLocation {
    pub file: String,
    pub line: usize,
    pub column: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end_line: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub end_column: Option<usize>,
}

/// Statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct StatisticsInfo {
    pub states_found: usize,
    pub states_initial: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub states_distinct: Option<usize>,
    pub transitions: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub suppressed_guard_errors: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max_depth: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max_queue_depth: Option<usize>,
    pub time_seconds: f64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub states_per_second: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub memory_mb: Option<f64>,
    /// Fingerprint storage backend counters. Present when disk-tier activity or
    /// reserved-memory usage is worth surfacing to downstream tooling.
    /// Part of #2665.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub storage: Option<StorageStatsInfo>,
}

/// Fingerprint storage backend statistics.
///
/// Provides visibility into the two-tier (memory + disk) fingerprint storage
/// system's behavior during model checking. Part of #2665.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct StorageStatsInfo {
    pub memory_count: usize,
    pub disk_count: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub memory_bytes: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub disk_lookups: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub disk_hits: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub eviction_count: Option<usize>,
}

/// Diagnostic messages
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct DiagnosticsInfo {
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub warnings: Vec<DiagnosticMessage>,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub info: Vec<DiagnosticMessage>,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub print_outputs: Vec<PrintOutput>,
}

/// A diagnostic message
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct DiagnosticMessage {
    pub code: String,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub suggestion: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub payload: Option<serde_json::Value>,
}

/// Print statement output
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct PrintOutput {
    pub value: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
}

/// Action coverage information
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ActionInfo {
    #[serde(default)]
    pub id: String,
    pub name: String,
    pub occurrences: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub percentage: Option<f64>,
}

pub(super) fn canonicalize_action_ids(actions: &mut [ActionInfo]) {
    let base_ids: Vec<String> = actions
        .iter()
        .enumerate()
        .map(|(idx, action)| {
            if action.id.is_empty() {
                format!("detected:{idx}")
            } else {
                action.id.clone()
            }
        })
        .collect();

    let mut counts = HashMap::<String, usize>::new();
    for id in &base_ids {
        *counts.entry(id.clone()).or_insert(0) += 1;
    }

    let mut used = HashSet::<String>::new();
    for (idx, action) in actions.iter_mut().enumerate() {
        let base = &base_ids[idx];
        let mut candidate = if counts[base] == 1 {
            base.clone()
        } else {
            // Repair duplicate recorded ids deterministically. This keeps the
            // original span-backed id visible while making the JSON payload
            // usable by downstream consumers that require unique action ids.
            format!("{base}#dup{idx}")
        };
        while !used.insert(candidate.clone()) {
            candidate.push('#');
        }
        action.id = candidate;
    }
}

fn deserialize_actions_detected<'de, D>(deserializer: D) -> Result<Vec<ActionInfo>, D::Error>
where
    D: Deserializer<'de>,
{
    let mut actions = Vec::<ActionInfo>::deserialize(deserializer)?;
    canonicalize_action_ids(&mut actions);
    Ok(actions)
}

impl JsonOutput {
    /// Create a new JSON output structure
    pub fn new(
        spec_file: &Path,
        config_file: Option<&Path>,
        module_name: &str,
        workers: usize,
    ) -> Self {
        let now = chrono::Utc::now();
        Self {
            version: OUTPUT_VERSION.to_string(),
            tool: "tla2".to_string(),
            timestamp: now.to_rfc3339(),
            input: InputInfo {
                spec_file: spec_file.display().to_string(),
                config_file: config_file.map(|p| p.display().to_string()),
                module: module_name.to_string(),
                workers,
            },
            specification: SpecInfo {
                init: None,
                next: None,
                invariants: Vec::new(),
                properties: Vec::new(),
                constants: HashMap::new(),
                variables: Vec::new(),
            },
            soundness: SoundnessProvenance::sound(),
            completeness: SearchCompleteness::Exhaustive,
            result: ResultInfo {
                status: "ok".to_string(),
                error_type: None,
                error_code: None,
                error_message: None,
                violated_property: None,
                suggestion: None,
            },
            counterexample: None,
            statistics: StatisticsInfo {
                states_found: 0,
                states_initial: 0,
                states_distinct: None,
                transitions: 0,
                suppressed_guard_errors: None,
                max_depth: None,
                max_queue_depth: None,
                time_seconds: 0.0,
                states_per_second: None,
                memory_mb: None,
                storage: None,
            },
            diagnostics: DiagnosticsInfo {
                warnings: Vec::new(),
                info: Vec::new(),
                print_outputs: Vec::new(),
            },
            actions_detected: Vec::new(),
        }
    }

    /// Add an info diagnostic
    pub fn add_info(&mut self, code: &str, message: &str) {
        self.diagnostics.info.push(DiagnosticMessage {
            code: code.to_string(),
            message: message.to_string(),
            location: None,
            suggestion: None,
            payload: None,
        });
    }

    /// Add a warning diagnostic
    pub fn add_warning(&mut self, code: &str, message: &str) {
        self.diagnostics.warnings.push(DiagnosticMessage {
            code: code.to_string(),
            message: message.to_string(),
            location: None,
            suggestion: None,
            payload: None,
        });
    }

    /// Serialize to JSON string
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Serialize to compact JSON string
    pub fn to_json_compact(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
}
