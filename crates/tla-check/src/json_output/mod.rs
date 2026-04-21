// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! JSON output format for AI agents and automated tooling.
//!
//! This module provides structured JSON output designed for machine consumption,
//! with explicit types, source locations, and state diffs.

mod conversion;
mod diagnostics;
mod dot;
mod error_mapping;
mod jsonl;
mod trace_types;
mod types;

#[cfg(test)]
mod tests;

// Re-export all public types from types.rs
pub use types::{
    ActionInfo, ActionRef, CounterexampleInfo, DiagnosticMessage, DiagnosticsInfo, ErrorSuggestion,
    InputInfo, JsonOutput, JsonValue, PrintOutput, ResultInfo, SearchCompleteness, SoundnessMode,
    SoundnessProvenance, SourceLocation, SpecInfo, StateDiff, StateInfo, StatisticsInfo,
    StorageStatsInfo, ValueChange, ViolatedProperty, OUTPUT_VERSION,
};

// Re-export error codes from diagnostics.rs
pub use diagnostics::error_codes;

// Re-export conversion utilities
pub use conversion::value_to_json;

// Re-export DOT format functions
pub use dot::{liveness_trace_to_dot, trace_to_dot};

// Re-export JSONL streaming types
pub use jsonl::JsonlEvent;
