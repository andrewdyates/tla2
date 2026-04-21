// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLA2-format JSONL trace writer for runtime verification.
//!
//! Emits traces in the JSONL format consumed by TLA2's `tla-check trace validate`:
//!
//! ```jsonl
//! {"type":"header","version":"1","module":"cdcl_test","variables":["assignment","trail","state","decisionLevel","learnedClauses"]}
//! {"type":"step","index":0,"state":{"assignment":{"type":"string","value":"..."},...}}
//! {"type":"step","index":1,"state":{...},"action":{"name":"Propagate"}}
//! ```
//!
//! This writer is used by the CDCL solver when the `Z4_TRACE_FILE` env var
//! is set.  It is **not** a tracing subscriber — it writes directly to a file
//! to avoid routing every tracing event through JSON serialization.

use std::fs::File;
use std::io::{BufWriter, Write};
use std::sync::Mutex;

/// Writer that emits TLA2-format JSONL trace files.
///
/// Thread-safe via interior `Mutex`.  The typical usage is to store an
/// `Option<TlaTraceWriter>` on the solver struct — when `None`, no trace
/// overhead is incurred beyond the `if let` branch.
pub struct TlaTraceWriter {
    inner: Mutex<TlaTraceInner>,
}

struct TlaTraceInner {
    writer: BufWriter<File>,
    step_index: usize,
}

impl TlaTraceWriter {
    /// Create a new trace writer.
    ///
    /// Writes the TLA2 header line immediately.  Panics if the file cannot be
    /// created (this is a developer-facing debugging tool, not user-facing).
    pub fn new(path: &str, module: &str, variables: &[&str]) -> Self {
        let file = File::create(path).expect("cannot create TLA trace file");
        let mut writer = BufWriter::new(file);

        // Write TLA2-format header
        let header = serde_json::json!({
            "type": "header",
            "version": "1",
            "module": module,
            "variables": variables,
        });
        writeln!(writer, "{header}").expect("failed to write TLA trace header");
        writer.flush().expect("failed to flush TLA trace header");

        Self {
            inner: Mutex::new(TlaTraceInner {
                writer,
                step_index: 0,
            }),
        }
    }

    /// Write a single trace step.
    ///
    /// `state` must be a JSON object whose keys match the `variables` declared
    /// in the header, with values encoded in TLA2's `JsonValue` format
    /// (e.g. `{"type":"int","value":42}`).
    ///
    /// `action` is `None` for the initial state (step 0) and `Some("ActionName")`
    /// for subsequent steps.
    #[allow(clippy::needless_pass_by_value)]
    pub fn write_step(&self, state: serde_json::Value, action: Option<&str>) {
        self.write_step_with_telemetry(state, action, None);
    }

    /// Write a single trace step with optional `telemetry` payload.
    ///
    /// The `telemetry` object is attached at the top-level of the step and is
    /// consumed by CHC/PDR trace validation tests.
    #[allow(clippy::needless_pass_by_value)]
    pub fn write_step_with_telemetry(
        &self,
        state: serde_json::Value,
        action: Option<&str>,
        telemetry: Option<serde_json::Value>,
    ) {
        let mut inner = self.inner.lock().expect("tla trace mutex poisoned");
        let mut step = serde_json::json!({
            "type": "step",
            "index": inner.step_index,
            "state": state,
        });
        if let Some(a) = action {
            step["action"] = serde_json::json!({"name": a});
        }
        if let Some(payload) = telemetry {
            step["telemetry"] = payload;
        }
        writeln!(inner.writer, "{step}").expect("failed to write TLA trace step");
        // Flush periodically (every 64 steps) to avoid data loss on crash
        if inner.step_index.is_multiple_of(64) {
            let _ = inner.writer.flush();
        }
        inner.step_index += 1;
    }

    /// Flush any buffered output and return the number of steps written.
    pub fn finish(&self) -> usize {
        let mut inner = self.inner.lock().expect("tla trace mutex poisoned");
        let _ = inner.writer.flush();
        inner.step_index
    }
}

#[cfg(test)]
#[path = "tla_trace_tests.rs"]
mod tests;
