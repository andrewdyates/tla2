// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Informal Trace Format (ITF) JSON serialization for counterexample traces.
//!
//! ITF is a JSON-based community standard used by Apalache and other TLA+ tooling
//! for counterexample trace interchange. Specification:
//! <https://apalache.informal.systems/docs/adr/015adr-trace.html>
//!
//! Value-level conversion (`value_to_itf`) lives in `tla_value::itf`.
//! This module provides trace-level serialization: converting `State` and `Trace`
//! objects into complete ITF JSON documents.
//!
//! Part of #3753, #3781.

use serde_json::{json, Value as JsonValue};
use tla_value::value_to_itf;

use crate::{State, Trace};

/// Convert a `State` (variable name -> Value mapping) to an ITF JSON state object.
///
/// The resulting JSON object has a `#meta` key with the state index, plus one
/// key per variable with the ITF-encoded value.
fn state_to_itf(state: &State, index: usize) -> JsonValue {
    let mut obj = serde_json::Map::new();
    obj.insert("#meta".to_string(), json!({ "index": index }));
    for (name, value) in state.vars() {
        obj.insert(name.to_string(), value_to_itf(value));
    }
    JsonValue::Object(obj)
}

/// Extract variable names from the first state of a trace.
fn extract_var_names(trace: &Trace) -> Vec<String> {
    trace
        .states
        .first()
        .map(|state| state.vars().map(|(name, _)| name.to_string()).collect())
        .unwrap_or_default()
}

/// Convert a safety/deadlock counterexample `Trace` into a complete ITF JSON document.
///
/// The returned JSON follows the ITF ADR-015 schema:
/// ```json
/// {
///   "#meta": { "format": "ITF", ... },
///   "params": [],
///   "vars": ["x", "y"],
///   "states": [
///     { "#meta": { "index": 0 }, "x": { "#bigint": "0" }, "y": true },
///     ...
///   ]
/// }
/// ```
#[must_use]
pub fn trace_to_itf(trace: &Trace) -> JsonValue {
    let vars = extract_var_names(trace);
    let states: Vec<JsonValue> = trace
        .states
        .iter()
        .enumerate()
        .map(|(i, s)| state_to_itf(s, i))
        .collect();

    json!({
        "#meta": {
            "format": "ITF",
            "format-description": "https://apalache.informal.systems/docs/adr/015adr-trace.html",
            "source": "tla2",
            "description": "Counterexample trace"
        },
        "params": [],
        "vars": vars,
        "states": states
    })
}

/// Convert a liveness counterexample (prefix + cycle) into a complete ITF JSON document.
///
/// The ITF format does not natively distinguish prefix from cycle, so all states
/// are emitted sequentially. Each state's `#meta` includes a `"phase"` field
/// (`"prefix"` or `"cycle"`) to preserve the lasso structure.
#[must_use]
pub fn liveness_trace_to_itf(prefix: &Trace, cycle: &Trace) -> JsonValue {
    let vars = if !prefix.is_empty() {
        extract_var_names(prefix)
    } else {
        extract_var_names(cycle)
    };

    let mut states = Vec::new();
    let mut index = 0usize;

    for state in &prefix.states {
        let mut itf_state = state_to_itf(state, index);
        if let Some(obj) = itf_state.as_object_mut() {
            if let Some(meta) = obj.get_mut("#meta") {
                if let Some(meta_obj) = meta.as_object_mut() {
                    meta_obj.insert("phase".to_string(), json!("prefix"));
                }
            }
        }
        states.push(itf_state);
        index += 1;
    }

    for state in &cycle.states {
        let mut itf_state = state_to_itf(state, index);
        if let Some(obj) = itf_state.as_object_mut() {
            if let Some(meta) = obj.get_mut("#meta") {
                if let Some(meta_obj) = meta.as_object_mut() {
                    meta_obj.insert("phase".to_string(), json!("cycle"));
                }
            }
        }
        states.push(itf_state);
        index += 1;
    }

    json!({
        "#meta": {
            "format": "ITF",
            "format-description": "https://apalache.informal.systems/docs/adr/015adr-trace.html",
            "source": "tla2",
            "description": "Liveness counterexample (prefix + cycle)"
        },
        "params": [],
        "vars": vars,
        "states": states
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use tla_value::Value;

    /// Shorthand for creating a `Value::SmallInt` in tests.
    fn int(n: i64) -> Value {
        Value::SmallInt(n)
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_trace_to_itf_empty() {
        let trace = Trace::from_states(vec![]);
        let itf = trace_to_itf(&trace);
        assert_eq!(itf["vars"], json!([]));
        assert_eq!(itf["states"], json!([]));
        assert_eq!(itf["#meta"]["format"], "ITF");
        assert_eq!(itf["#meta"]["source"], "tla2");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_trace_to_itf_two_states() {
        let s0 = State::from_pairs(vec![("x", int(0)), ("y", int(1))]);
        let s1 = State::from_pairs(vec![("x", int(1)), ("y", int(2))]);
        let trace = Trace::from_states(vec![s0, s1]);
        let itf = trace_to_itf(&trace);

        assert_eq!(itf["vars"], json!(["x", "y"]));

        assert_eq!(itf["states"][0]["#meta"]["index"], 0);
        assert_eq!(itf["states"][0]["x"], json!({"#bigint": "0"}));
        assert_eq!(itf["states"][0]["y"], json!({"#bigint": "1"}));

        assert_eq!(itf["states"][1]["#meta"]["index"], 1);
        assert_eq!(itf["states"][1]["x"], json!({"#bigint": "1"}));
        assert_eq!(itf["states"][1]["y"], json!({"#bigint": "2"}));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_liveness_trace_to_itf_phases() {
        let s0 = State::from_pairs(vec![("pc", Value::String(Arc::from("init")))]);
        let s1 = State::from_pairs(vec![("pc", Value::String(Arc::from("loop")))]);
        let prefix = Trace::from_states(vec![s0]);
        let cycle = Trace::from_states(vec![s1]);

        let itf = liveness_trace_to_itf(&prefix, &cycle);

        assert_eq!(itf["states"][0]["#meta"]["phase"], "prefix");
        assert_eq!(itf["states"][1]["#meta"]["phase"], "cycle");
        assert_eq!(
            itf["#meta"]["description"],
            "Liveness counterexample (prefix + cycle)"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_trace_to_itf_with_set_and_bool() {
        use tla_value::SetBuilder;

        let mut builder = SetBuilder::new();
        builder.insert(int(1));
        builder.insert(int(2));
        let set_val = builder.build_value();

        let s0 = State::from_pairs(vec![("flag", Value::Bool(true)), ("nums", set_val.clone())]);
        let s1 = State::from_pairs(vec![("flag", Value::Bool(false)), ("nums", set_val)]);
        let trace = Trace::from_states(vec![s0, s1]);
        let itf = trace_to_itf(&trace);

        assert_eq!(itf["#meta"]["format"], "ITF");
        assert_eq!(itf["params"], json!([]));

        let vars = itf["vars"].as_array().expect("vars should be array");
        assert!(vars.contains(&json!("flag")));
        assert!(vars.contains(&json!("nums")));

        assert_eq!(itf["states"][0]["flag"], json!(true));
        assert_eq!(
            itf["states"][0]["nums"],
            json!({"#set": [{"#bigint": "1"}, {"#bigint": "2"}]})
        );

        assert_eq!(itf["states"][1]["flag"], json!(false));
        assert_eq!(itf["states"][1]["#meta"]["index"], 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_trace_to_itf_round_trip() {
        let s0 = State::from_pairs(vec![("x", int(0))]);
        let s1 = State::from_pairs(vec![("x", int(1))]);
        let trace = Trace::from_states(vec![s0, s1]);
        let itf = trace_to_itf(&trace);

        let json_str = serde_json::to_string_pretty(&itf).expect("ITF JSON should serialize");
        let parsed: serde_json::Value =
            serde_json::from_str(&json_str).expect("ITF JSON should parse back");
        assert_eq!(parsed["states"].as_array().expect("states array").len(), 2);
        assert_eq!(parsed["vars"], json!(["x"]));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_liveness_trace_to_itf_empty_prefix() {
        let s0 = State::from_pairs(vec![("x", int(0))]);
        let s1 = State::from_pairs(vec![("x", int(1))]);
        let prefix = Trace::from_states(vec![]);
        let cycle = Trace::from_states(vec![s0, s1]);

        let itf = liveness_trace_to_itf(&prefix, &cycle);

        assert_eq!(itf["vars"], json!(["x"]));
        assert_eq!(itf["states"][0]["#meta"]["phase"], "cycle");
        assert_eq!(itf["states"][1]["#meta"]["phase"], "cycle");
        assert_eq!(itf["states"][0]["#meta"]["index"], 0);
        assert_eq!(itf["states"][1]["#meta"]["index"], 1);
    }
}
