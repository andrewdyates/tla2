// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Canonical statistics output for the Z4 binary.
//!
//! All solve paths (SMT, DIMACS SAT, CHC) populate a [`RunStatistics`] envelope
//! with a common key namespace, then render through one shared function. This
//! ensures `--stats` emits a stable schema regardless of mode.
//!
//! Part of #4723 — cross-mode stats schema contract.

use std::collections::BTreeMap;
use std::time::Duration;

/// Controls which stats format(s) to emit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct StatsConfig {
    /// Human-readable stats (--stats / -st).
    pub(crate) human: bool,
    /// JSON stats to stderr (--stats-json).
    pub(crate) json: bool,
}

impl StatsConfig {
    /// True if any stats output is requested.
    pub(crate) fn any(&self) -> bool {
        self.human || self.json
    }
}

/// Solve mode tag included in every stats envelope.
#[derive(Debug, Clone, Copy)]
pub(crate) enum SolveMode {
    Smt,
    DimacsSat,
    Chc,
    Portfolio,
}

impl SolveMode {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Smt => "smt",
            Self::DimacsSat => "dimacs-sat",
            Self::Chc => "chc",
            Self::Portfolio => "portfolio",
        }
    }
}

/// Canonical statistics envelope populated by every solve path.
///
/// The `counters` map uses a stable key namespace:
/// - Common keys: `conflicts`, `decisions`, `propagations`, `restarts`
/// - SAT-specific: `sat.chrono_bt`, `sat.learned_cls`, `sat.bve_eliminated`, etc.
/// - CHC-specific: `chc.iterations`, `chc.lemmas_learned`, `chc.max_frame`, etc.
/// - SMT-specific: `smt.theory_conflicts`, `smt.theory_propagations`, etc.
pub(crate) struct RunStatistics {
    pub(crate) mode: SolveMode,
    pub(crate) result: String,
    pub(crate) wall_time_ms: u64,
    pub(crate) counters: BTreeMap<String, u64>,
}

impl RunStatistics {
    pub(crate) fn new(mode: SolveMode, result: &str, elapsed: Duration) -> Self {
        Self {
            mode,
            result: result.to_string(),
            wall_time_ms: elapsed.as_millis() as u64,
            counters: BTreeMap::new(),
        }
    }

    /// Insert a counter value. Key should use the stable namespace (e.g., `"conflicts"`).
    pub(crate) fn insert(&mut self, key: &str, value: u64) {
        self.counters.insert(key.to_string(), value);
    }

    /// Print statistics to stderr in the canonical format.
    ///
    /// Format:
    /// ```text
    /// c
    /// c --- Z4 statistics ---
    /// c z4.mode:          dimacs-sat
    /// c z4.result:               sat
    /// c z4.wall_time_ms:          42
    /// c conflicts:              1234
    /// c decisions:              5678
    /// ...
    /// c
    /// ```
    pub(crate) fn print_to_stderr(&self) {
        safe_eprintln!("c");
        safe_eprintln!("c --- Z4 statistics ---");
        safe_eprintln!("c z4.mode:          {:>12}", self.mode.as_str());
        safe_eprintln!("c z4.result:        {:>12}", self.result);
        safe_eprintln!("c z4.wall_time_ms:  {:>12}", self.wall_time_ms);
        for (key, value) in &self.counters {
            // Pad key to align values
            let padded = format!("c {key}:");
            safe_eprintln!("{padded:<20} {value:>12}");
        }
        safe_eprintln!("c");
    }

    /// Serialize statistics as a single-line JSON object.
    ///
    /// The output includes `mode`, `result`, `wall_time_ms`, and all counters
    /// as a flat object. Designed for machine consumption (CI pipelines,
    /// benchmarking scripts, LLM tool-use).
    pub(crate) fn to_json(&self) -> String {
        let mut map = serde_json::Map::new();
        map.insert(
            "mode".to_string(),
            serde_json::Value::String(self.mode.as_str().to_string()),
        );
        map.insert(
            "result".to_string(),
            serde_json::Value::String(self.result.clone()),
        );
        map.insert(
            "wall_time_ms".to_string(),
            serde_json::json!(self.wall_time_ms),
        );
        for (key, value) in &self.counters {
            map.insert(key.clone(), serde_json::json!(value));
        }
        serde_json::Value::Object(map).to_string()
    }

    /// Print JSON statistics to stderr.
    pub(crate) fn print_json_to_stderr(&self) {
        safe_eprintln!("{}", self.to_json());
    }

    /// Emit stats according to the given config.
    pub(crate) fn emit(&self, config: StatsConfig) {
        if config.human {
            self.print_to_stderr();
        }
        if config.json {
            self.print_json_to_stderr();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_json_contains_required_fields() {
        let mut stats = RunStatistics::new(SolveMode::DimacsSat, "sat", Duration::from_millis(42));
        stats.insert("conflicts", 1234);
        stats.insert("decisions", 5678);

        let json_str = stats.to_json();
        let parsed: serde_json::Value = serde_json::from_str(&json_str)
            .expect("to_json output should be valid JSON");

        assert_eq!(parsed["mode"], "dimacs-sat");
        assert_eq!(parsed["result"], "sat");
        assert_eq!(parsed["wall_time_ms"], 42);
        assert_eq!(parsed["conflicts"], 1234);
        assert_eq!(parsed["decisions"], 5678);
    }

    #[test]
    fn test_to_json_single_line() {
        let stats = RunStatistics::new(SolveMode::Smt, "done", Duration::from_millis(100));
        let json_str = stats.to_json();
        assert!(
            !json_str.contains('\n'),
            "JSON stats should be a single line for easy grep/parse"
        );
    }

    #[test]
    fn test_to_json_all_modes() {
        for (mode, expected) in [
            (SolveMode::Smt, "smt"),
            (SolveMode::DimacsSat, "dimacs-sat"),
            (SolveMode::Chc, "chc"),
            (SolveMode::Portfolio, "portfolio"),
        ] {
            let stats = RunStatistics::new(mode, "unknown", Duration::ZERO);
            let json_str = stats.to_json();
            let parsed: serde_json::Value = serde_json::from_str(&json_str).unwrap();
            assert_eq!(parsed["mode"], expected);
        }
    }

    #[test]
    fn test_stats_config_any() {
        assert!(!StatsConfig { human: false, json: false }.any());
        assert!(StatsConfig { human: true, json: false }.any());
        assert!(StatsConfig { human: false, json: true }.any());
        assert!(StatsConfig { human: true, json: true }.any());
    }
}
