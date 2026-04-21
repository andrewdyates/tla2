// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Counterexample trace and value types for JSON output.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

use super::types::SourceLocation;

/// Counterexample trace
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct CounterexampleInfo {
    pub length: usize,
    pub states: Vec<StateInfo>,
    /// For liveness violations: index where the cycle begins
    #[serde(skip_serializing_if = "Option::is_none")]
    pub loop_start: Option<usize>,
}

/// A single state in a trace
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct StateInfo {
    pub index: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fingerprint: Option<String>,
    pub action: ActionRef,
    pub variables: HashMap<String, JsonValue>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub diff_from_previous: Option<StateDiff>,
}

/// Reference to an action
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ActionRef {
    pub name: String,
    /// Type: "initial", "next"
    #[serde(rename = "type")]
    pub action_type: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
}

/// Diff between two states
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct StateDiff {
    pub changed: HashMap<String, ValueChange>,
    pub unchanged: Vec<String>,
}

/// A value change
#[derive(Debug, Clone, Serialize, Deserialize)]
#[non_exhaustive]
pub struct ValueChange {
    pub from: JsonValue,
    pub to: JsonValue,
}

/// Typed JSON value representation
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "type", content = "value")]
#[non_exhaustive]
pub enum JsonValue {
    #[serde(rename = "bool")]
    Bool(bool),
    #[serde(rename = "int")]
    Int(i64),
    #[serde(rename = "big_int")]
    BigInt(String),
    #[serde(rename = "string")]
    String(String),
    #[serde(rename = "set")]
    Set(Vec<JsonValue>),
    #[serde(rename = "seq")]
    Seq(Vec<JsonValue>),
    #[serde(rename = "record")]
    Record(HashMap<String, JsonValue>),
    #[serde(rename = "function")]
    Function {
        domain: Vec<JsonValue>,
        mapping: Vec<(JsonValue, JsonValue)>,
    },
    #[serde(rename = "tuple")]
    Tuple(Vec<JsonValue>),
    #[serde(rename = "model_value")]
    ModelValue(String),
    #[serde(rename = "interval")]
    Interval { lo: String, hi: String },
    #[serde(rename = "undefined")]
    Undefined,
}
