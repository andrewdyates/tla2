// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! ITF (Informal Trace Format) emission helpers for the CLI.
//!
//! Core ITF conversion (`trace_to_itf`, `liveness_trace_to_itf`, `value_to_itf`)
//! lives in `tla_check::itf` and `tla_value::itf`. This module provides thin
//! wrappers that emit the serialized JSON to stdout.
//!
//! Part of #3753, #3781.

use anyhow::{bail, Result};
use serde_json::json;
use tla_check::{CheckResult, Trace};

// Re-export the canonical value_to_itf from tla-value for callers that need it.
#[allow(unused_imports)]
pub(crate) use tla_value::value_to_itf;

/// Format a safety/deadlock trace as ITF JSON and emit to stdout.
pub(crate) fn emit_itf_trace(trace: &Trace) {
    let itf = tla_check::trace_to_itf(trace);
    // ITF output goes to stdout (machine-readable), not stderr.
    println!(
        "{}",
        serde_json::to_string_pretty(&itf)
            .expect("invariant: ITF JSON serialization is infallible")
    );
}

/// Format a liveness trace as ITF JSON and emit to stdout.
pub(crate) fn emit_itf_liveness_trace(prefix: &Trace, cycle: &Trace) {
    let itf = tla_check::liveness_trace_to_itf(prefix, cycle);
    println!(
        "{}",
        serde_json::to_string_pretty(&itf)
            .expect("invariant: ITF JSON serialization is infallible")
    );
}

/// Emit a minimal ITF document for successful checks (no counterexample trace).
///
/// The document has the standard ITF `#meta` header with `"description"` indicating
/// success, and an empty `states` array.
fn emit_itf_success() {
    let itf = json!({
        "#meta": {
            "format": "ITF",
            "format-description": "https://apalache.informal.systems/docs/adr/015adr-trace.html",
            "source": "tla2",
            "description": "No errors found"
        },
        "params": [],
        "vars": [],
        "states": []
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&itf)
            .expect("invariant: ITF JSON serialization is infallible")
    );
}

/// Report model checking results in ITF (Informal Trace Format) JSON.
///
/// For error results with traces, the counterexample trace is emitted in ITF format.
/// For successful checks or results without traces, a minimal ITF document is emitted.
/// Error exit codes mirror the JSON output path for tooling consistency.
///
/// Part of #3781.
pub(crate) fn report_check_itf(result: &CheckResult) -> Result<()> {
    match result {
        CheckResult::Success(_) | CheckResult::LimitReached { .. } => {
            emit_itf_success();
            Ok(())
        }
        CheckResult::InvariantViolation { trace, .. } => {
            if trace.is_empty() {
                emit_itf_success();
            } else {
                emit_itf_trace(trace);
            }
            std::process::exit(1);
        }
        CheckResult::PropertyViolation { trace, .. } => {
            if trace.is_empty() {
                emit_itf_success();
            } else {
                emit_itf_trace(trace);
            }
            std::process::exit(1);
        }
        CheckResult::LivenessViolation {
            prefix, cycle, ..
        } => {
            emit_itf_liveness_trace(prefix, cycle);
            std::process::exit(1);
        }
        CheckResult::Deadlock { trace, .. } => {
            if trace.is_empty() {
                emit_itf_success();
            } else {
                emit_itf_trace(trace);
            }
            std::process::exit(1);
        }
        CheckResult::Error { error, .. } => {
            // Errors without traces get a minimal ITF document.
            // The error message is not representable in ITF format, so we
            // emit it to stderr for diagnostic purposes.
            eprintln!("Error: {}", error);
            emit_itf_success();
            std::process::exit(1);
        }
        _ => bail!(
            "Model checking produced a result variant unsupported by this tla2 version; upgrade tla2"
        ),
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;
    use std::sync::Arc;
    use tla_check::{liveness_trace_to_itf, trace_to_itf, State, Trace, Value};

    /// Shorthand for creating a `Value::SmallInt` in tests.
    fn int(n: i64) -> Value {
        Value::SmallInt(n)
    }

    // Value-level ITF tests live in tla_value::itf::tests.
    // Trace-level ITF tests live in tla_check::itf::tests.
    // Only CLI-integration-level tests remain here.

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_trace_empty() {
        let trace = Trace::from_states(vec![]);
        let itf = trace_to_itf(&trace);
        assert_eq!(itf["vars"], json!([]));
        assert_eq!(itf["states"], json!([]));
        assert_eq!(itf["#meta"]["format"], "ITF");
        assert_eq!(itf["#meta"]["source"], "tla2");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_itf_trace_two_states() {
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
    fn test_itf_liveness_trace_phases() {
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
}
