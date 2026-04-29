// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! JSON Lines (JSONL) streaming output for model checking events.

use super::types::JsonValue;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// JSONL event types for streaming output
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
#[non_exhaustive]
pub enum JsonlEvent {
    /// Model checking started
    #[serde(rename = "start")]
    Start { spec: String, timestamp: String },
    /// Progress update
    #[serde(rename = "progress")]
    Progress {
        states: usize,
        depth: usize,
        time: f64,
    },
    /// Error detected
    #[serde(rename = "error")]
    Error {
        error_type: String,
        #[serde(skip_serializing_if = "Option::is_none")]
        state_index: Option<usize>,
    },
    /// State in counterexample
    #[serde(rename = "state")]
    State {
        index: usize,
        action: String,
        variables: HashMap<String, JsonValue>,
        #[serde(skip_serializing_if = "Option::is_none")]
        diff: Option<HashMap<String, (JsonValue, JsonValue)>>,
    },
    /// Model checking complete
    #[serde(rename = "done")]
    Done { status: String, time: f64 },
}

impl JsonlEvent {
    /// Serialize to single JSON line
    pub fn to_jsonl(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
}
