// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trace validation input parsing (JSON + JSONL).
//!
//! This is an IO layer that incrementally emits a header and ordered steps to a sink, without
//! coupling to the trace validation engine itself.

mod parse;
#[cfg(test)]
mod tests;

use std::collections::HashMap;
use std::path::Path;

use serde::{Deserialize, Serialize};

use crate::json_output::JsonValue;

pub use parse::{read_trace_events, read_trace_json, read_trace_jsonl};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceInputFormatSelection {
    /// Automatically select a format.
    ///
    /// Resolution uses a best-effort heuristic based on a `TraceSourceHint`:
    /// - `.jsonl` extension => JSONL
    /// - otherwise => JSON
    ///
    /// Use `resolve_trace_input_format()` to map this into a resolved `TraceInputFormat`.
    Auto,
    /// JSON object form `{ version, module, variables, steps: [...] }`.
    ///
    /// Note: this currently deserializes the full `steps` array into memory.
    Json,
    /// JSON Lines form: one event object per line (`header` then `step`).
    Jsonl,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceInputFormat {
    /// JSON object form `{ version, module, variables, steps: [...] }`.
    ///
    /// Note: this currently deserializes the full `steps` array into memory.
    Json,
    /// JSON Lines form: one event object per line (`header` then `step`).
    Jsonl,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TraceSourceHint<'a> {
    Path(&'a Path),
    Stdin,
    Unknown,
}

pub fn resolve_trace_input_format(
    selection: TraceInputFormatSelection,
    hint: TraceSourceHint<'_>,
) -> TraceInputFormat {
    match selection {
        TraceInputFormatSelection::Json => TraceInputFormat::Json,
        TraceInputFormatSelection::Jsonl => TraceInputFormat::Jsonl,
        TraceInputFormatSelection::Auto => match hint {
            TraceSourceHint::Path(p) if is_jsonl_extension(p) => TraceInputFormat::Jsonl,
            TraceSourceHint::Path(_) | TraceSourceHint::Stdin | TraceSourceHint::Unknown => {
                TraceInputFormat::Json
            }
        },
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TraceHeader {
    pub version: String,
    pub module: String,
    pub variables: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceActionLabel {
    pub name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub params: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceStep {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub index: Option<usize>,
    pub state: HashMap<String, JsonValue>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub action: Option<TraceActionLabel>,
}

pub trait TraceEventSink {
    fn on_header(&mut self, header: TraceHeader);
    fn on_step(&mut self, step: TraceStep);
}

#[derive(Debug, thiserror::Error)]
pub enum TraceParseError {
    #[error("trace input IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("trace JSON decode failed: {0}")]
    JsonDecode(#[from] serde_json::Error),

    #[error("trace JSON decode failed at {path} (line {line}, column {column}): {source}")]
    JsonDecodePath {
        path: String,
        line: usize,
        column: usize,
        #[source]
        source: serde_json::Error,
    },

    #[error(
        "trace JSONL decode failed at {path} (line {line_no}, column {column}): {source} (line prefix: {raw_line_prefix})"
    )]
    JsonlDecode {
        line_no: usize,
        path: String,
        column: usize,
        #[source]
        source: serde_json::Error,
        raw_line_prefix: String,
    },

    #[error("trace JSONL encountered unknown event type {ty:?} (line {line_no})")]
    JsonlUnknownEventType { line_no: usize, ty: String },

    #[error("trace JSONL missing header before first step (line {line_no})")]
    JsonlMissingHeader { line_no: usize },

    #[error("trace JSONL missing header (no events found)")]
    JsonlMissingHeaderAtEof,

    #[error("trace JSONL encountered a second header (line {line_no})")]
    JsonlUnexpectedHeader { line_no: usize },

    #[error("trace JSONL internal error: buffered header unexpectedly missing before step (line {line_no})")]
    JsonlMissingBufferedHeader { line_no: usize },

    #[error("trace input missing any steps (expected step 0) ({where_})")]
    MissingAnySteps { where_: String },

    #[error("trace step index mismatch at {where_}: expected {expected}, got {got}")]
    StepIndexMismatch {
        where_: String,
        expected: usize,
        got: usize,
    },

    #[error("trace step references unknown variable {var:?} at {where_}")]
    UnknownVariable { where_: String, var: String },

    #[error("trace step 0 must not have an action label ({where_})")]
    ActionOnInitialStep { where_: String },

    #[error("trace header contains duplicate variable {var:?} ({where_})")]
    DuplicateVariable { where_: String, var: String },
}

fn is_jsonl_extension(path: &Path) -> bool {
    path.extension()
        .and_then(|s| s.to_str())
        .is_some_and(|s| s.eq_ignore_ascii_case("jsonl"))
}
