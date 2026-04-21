// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structured decision logging for the adaptive portfolio solver.
//!
//! When the `Z4_DECISION_LOG` environment variable is set to a file path,
//! every adaptive strategy decision is written as a JSON line to that file.
//! When unset, all operations are no-ops with zero overhead.
//!
//! Part of #7918 - Adaptive portfolio observability.

use std::fs::File;
use std::io::{BufWriter, Write};
use std::sync::Mutex;

/// A single decision entry logged by the adaptive portfolio.
pub(crate) struct DecisionEntry {
    /// The adaptive stage name (e.g., "trivial_synthesis", "non_inlined_pdr").
    pub stage: &'static str,
    /// Whether the gate check passed (true = stage was attempted).
    pub gate_result: bool,
    /// Human-readable reason for the gate decision.
    pub gate_reason: String,
    /// Budget allocated to this stage in seconds.
    pub budget_secs: f64,
    /// Wall-clock time consumed by this stage in seconds.
    pub elapsed_secs: f64,
    /// Outcome of the stage ("safe", "unsafe", "unknown", "skipped", "not_applicable").
    pub result: &'static str,
    /// Number of lemmas learned during this stage (0 if not applicable).
    pub lemmas_learned: usize,
    /// Maximum PDR frame reached (0 if not applicable).
    pub max_frame: usize,
}

/// Structured decision logger for the adaptive portfolio.
///
/// Holds an optional writer protected by a `Mutex` for `&self` compatibility
/// with `AdaptivePortfolio` methods. When `Z4_DECISION_LOG` is not set, the
/// inner `Option` is `None` and all methods are effectively no-ops.
pub(crate) struct DecisionLog {
    writer: Mutex<Option<BufWriter<File>>>,
}

impl DecisionLog {
    /// Create a `DecisionLog` from the `Z4_DECISION_LOG` environment variable.
    ///
    /// Returns a log that writes JSON lines to the specified path, or a no-op
    /// log if the variable is unset or the file cannot be opened.
    pub(crate) fn from_env() -> Self {
        let writer = std::env::var("Z4_DECISION_LOG").ok().and_then(|path| {
            File::create(&path)
                .map(|f| BufWriter::new(f))
                .map_err(|e| {
                    // Use eprintln directly here — this runs once at startup.
                    eprintln!("Warning: Z4_DECISION_LOG={path}: could not open for writing: {e}");
                    e
                })
                .ok()
        });
        Self {
            writer: Mutex::new(writer),
        }
    }

    /// Returns true if decision logging is active.
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn is_active(&self) -> bool {
        // Fast path: if the Mutex is poisoned or None, return false.
        self.writer
            .lock()
            .map(|guard| guard.is_some())
            .unwrap_or(false)
    }

    /// Log a decision entry as a JSON line.
    ///
    /// No-op if the logger is inactive (env var unset).
    pub(crate) fn log_decision(&self, entry: DecisionEntry) {
        let mut guard = match self.writer.lock() {
            Ok(g) => g,
            Err(_) => return, // Mutex poisoned — silently skip.
        };
        let writer = match guard.as_mut() {
            Some(w) => w,
            None => return, // Logging disabled — no-op.
        };

        let json = serde_json::json!({
            "stage": entry.stage,
            "gate_result": entry.gate_result,
            "gate_reason": entry.gate_reason,
            "budget_secs": entry.budget_secs,
            "elapsed_secs": entry.elapsed_secs,
            "result": entry.result,
            "lemmas_learned": entry.lemmas_learned,
            "max_frame": entry.max_frame,
        });

        // Write JSON line. Ignore write errors — logging must not affect solving.
        let _ = writeln!(writer, "{json}");
        let _ = writer.flush();
    }
}
