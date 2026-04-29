// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 summary` -- compact summary table of model checking results.
//!
//! Generates a formatted table summarizing model checking outcomes across
//! multiple TLA+ specifications. For each spec, reads a `.tla2-check.json`
//! sidecar file (produced by `tla2 check --output json`) and extracts key
//! metrics: status, distinct/total states, wall-clock time, invariants
//! checked, and deadlock status.
//!
//! Supports three output formats: aligned ASCII table (human), JSON array,
//! and CSV. Results can be sorted by name, state count, time, or status,
//! and filtered by status (pass/fail/error).
//!
//! ```text
//! | Spec              | Status | Distinct   |      Total | Time(s) | Inv | Deadlock |
//! ------------------------------------------------------------------------------------
//! | MCBakery          | pass   |      6,016 |     12,032 |    0.50 |   2 | none     |
//! | MCDining          | fail   |      1,234 |      2,468 |    0.20 |   1 | FOUND    |
//! | MCBuffer          | pass   |     89,012 |    178,024 |    2.10 |   2 | none     |
//! ------------------------------------------------------------------------------------
//! 3 specs: 2 pass, 1 fail, 0 error | 96,262 distinct states | 2.8s total
//! ```

use std::cmp::Ordering;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Public enums
// ---------------------------------------------------------------------------

/// Output format for the summary command.
#[derive(Debug, Clone, Copy, Default, clap::ValueEnum, Serialize)]
pub(crate) enum SummaryOutputFormat {
    /// Human-readable aligned ASCII table (default).
    #[default]
    Human,
    /// Structured JSON array.
    Json,
    /// Comma-separated values.
    Csv,
}

/// Sort field for summary rows.
#[derive(Debug, Clone, Copy, Default, clap::ValueEnum, Serialize)]
pub(crate) enum SummarySortField {
    /// Sort alphabetically by spec name (default).
    #[default]
    Name,
    /// Sort by distinct state count (descending).
    States,
    /// Sort by wall-clock time (descending).
    Time,
    /// Sort by status (pass < fail < error).
    Status,
}

/// Status classification for summary rows. Also used as a filter value.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, clap::ValueEnum, Serialize, Deserialize,
)]
#[serde(rename_all = "snake_case")]
pub(crate) enum SummaryStatus {
    /// Model checking completed with no violations.
    Pass,
    /// Model checking found an invariant/property violation or deadlock.
    Fail,
    /// Model checking could not complete (parse error, crash, timeout, etc.).
    Error,
}

impl std::fmt::Display for SummaryStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Pass => write!(f, "pass"),
            Self::Fail => write!(f, "fail"),
            Self::Error => write!(f, "error"),
        }
    }
}

// ---------------------------------------------------------------------------
// Summary row
// ---------------------------------------------------------------------------

/// One row in the summary table representing a single spec's check result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct SummaryRow {
    /// Spec file stem (e.g. "MCBakery").
    pub name: String,
    /// Check status.
    pub status: SummaryStatus,
    /// Number of distinct states found.
    pub distinct_states: u64,
    /// Total number of states found (including duplicates).
    pub total_states: u64,
    /// Wall-clock time in seconds.
    pub time_seconds: f64,
    /// Number of invariants checked.
    pub invariants_checked: usize,
    /// Deadlock check outcome.
    pub deadlock: DeadlockStatus,
    /// Source file path.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_path: Option<String>,
    /// Error message (if status is fail or error).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error_message: Option<String>,
}

/// Deadlock check outcome for a single spec.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum DeadlockStatus {
    /// No deadlock detected.
    None,
    /// Deadlock checking was disabled or status unknown.
    Disabled,
    /// A deadlock was found.
    Found,
}

impl std::fmt::Display for DeadlockStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::None => write!(f, "none"),
            Self::Disabled => write!(f, "off"),
            Self::Found => write!(f, "FOUND"),
        }
    }
}

// ---------------------------------------------------------------------------
// Sidecar JSON schema (subset of tla-check JsonOutput)
// ---------------------------------------------------------------------------

/// Subset of the `tla2 check --output json` format needed for summary.
#[derive(Deserialize)]
struct CheckSidecar {
    result: SidecarResult,
    statistics: SidecarStats,
    #[serde(default)]
    specification: Option<SidecarSpec>,
}

#[derive(Deserialize)]
struct SidecarResult {
    status: String,
    #[serde(default)]
    error_type: Option<String>,
    #[serde(default)]
    error_message: Option<String>,
}

#[derive(Deserialize)]
struct SidecarStats {
    states_found: u64,
    #[serde(default)]
    states_distinct: Option<u64>,
    #[serde(default)]
    time_seconds: Option<f64>,
}

#[derive(Deserialize)]
struct SidecarSpec {
    #[serde(default)]
    invariants: Vec<String>,
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Generate a summary table from model checking results.
///
/// Scans `paths` for `.tla` files, reads their `.tla2-check.json` sidecar
/// files (produced by `tla2 check --output json`), and outputs a formatted
/// summary table. When no sidecar is found for a spec, the row is marked
/// as `error` with an explanatory message.
pub(crate) fn cmd_summary(
    paths: &[PathBuf],
    _config: Option<&Path>,
    _workers: usize,
    format: SummaryOutputFormat,
    sort_by: SummarySortField,
    filter_status: Option<&str>,
) -> Result<()> {
    if paths.is_empty() {
        bail!("at least one path (file or directory) is required");
    }

    // Collect all .tla files from the provided paths.
    let tla_files = collect_tla_files(paths)?;
    if tla_files.is_empty() {
        bail!("no .tla files found in the provided paths");
    }

    // Build summary rows from sidecar files.
    let mut rows: Vec<SummaryRow> = tla_files.iter().map(|path| build_row(path)).collect();

    // Apply status filter.
    let parsed_filter = filter_status.and_then(|s| match s {
        "pass" => Some(SummaryStatus::Pass),
        "fail" => Some(SummaryStatus::Fail),
        "error" => Some(SummaryStatus::Error),
        _ => None,
    });
    if let Some(status) = parsed_filter {
        rows.retain(|r| r.status == status);
    }

    // Sort rows.
    sort_rows(&mut rows, sort_by);

    // Output in the requested format.
    match format {
        SummaryOutputFormat::Human => print_human(&rows),
        SummaryOutputFormat::Json => print_json(&rows)?,
        SummaryOutputFormat::Csv => print_csv(&rows),
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// File collection
// ---------------------------------------------------------------------------

/// Collect all `.tla` files from the provided paths. Directories are scanned
/// recursively. Individual `.tla` files are passed through directly.
fn collect_tla_files(paths: &[PathBuf]) -> Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    for path in paths {
        if path.is_dir() {
            collect_tla_from_dir(path, &mut files)?;
        } else if path.extension().is_some_and(|e| e == "tla") {
            files.push(path.clone());
        } else {
            bail!("expected a .tla file or directory, got: {}", path.display());
        }
    }
    // Sort by file name for stable ordering before user-requested sort.
    files.sort_by(|a, b| a.file_name().cmp(&b.file_name()));
    files.dedup();
    Ok(files)
}

/// Recursively collect `.tla` files from a directory.
fn collect_tla_from_dir(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    let mut entries: Vec<_> = fs::read_dir(dir)
        .with_context(|| format!("read directory {}", dir.display()))?
        .filter_map(|e| e.ok())
        .collect();
    entries.sort_by_key(|e| e.file_name());

    for entry in entries {
        let path = entry.path();
        if path.is_dir() {
            collect_tla_from_dir(&path, out)?;
        } else if path.extension().is_some_and(|e| e == "tla") {
            out.push(path);
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Row construction from sidecar JSON
// ---------------------------------------------------------------------------

/// Build a summary row for a single `.tla` file by reading its sidecar JSON.
fn build_row(tla_path: &Path) -> SummaryRow {
    let spec_name = spec_name_from_path(tla_path);
    let sidecar_path = sidecar_path_for(tla_path);

    match read_sidecar(&sidecar_path) {
        Some(sidecar) => row_from_sidecar(&spec_name, tla_path, &sidecar),
        None => SummaryRow {
            name: spec_name,
            status: SummaryStatus::Error,
            distinct_states: 0,
            total_states: 0,
            time_seconds: 0.0,
            invariants_checked: 0,
            deadlock: DeadlockStatus::Disabled,
            source_path: Some(tla_path.display().to_string()),
            error_message: Some(format!("no sidecar file: {}", sidecar_path.display())),
        },
    }
}

/// Determine the sidecar JSON path for a given `.tla` file.
/// Convention: `<stem>.tla2-check.json` in the same directory.
fn sidecar_path_for(tla_path: &Path) -> PathBuf {
    let stem = tla_path
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_default();
    let parent = tla_path.parent().unwrap_or(Path::new("."));
    parent.join(format!("{stem}.tla2-check.json"))
}

/// Attempt to read and parse a sidecar JSON file.
fn read_sidecar(path: &Path) -> Option<CheckSidecar> {
    let text = fs::read_to_string(path).ok()?;
    serde_json::from_str(&text).ok()
}

/// Convert a parsed sidecar into a `SummaryRow`.
fn row_from_sidecar(spec_name: &str, tla_path: &Path, sidecar: &CheckSidecar) -> SummaryRow {
    let status = classify_status(&sidecar.result.status, &sidecar.result.error_type);
    let deadlock = classify_deadlock(&sidecar.result.error_type);
    let invariants_checked = sidecar
        .specification
        .as_ref()
        .map(|s| s.invariants.len())
        .unwrap_or(0);

    SummaryRow {
        name: spec_name.to_string(),
        status,
        distinct_states: sidecar.statistics.states_distinct.unwrap_or(0),
        total_states: sidecar.statistics.states_found,
        time_seconds: sidecar.statistics.time_seconds.unwrap_or(0.0),
        invariants_checked,
        deadlock,
        source_path: Some(tla_path.display().to_string()),
        error_message: sidecar.result.error_message.clone(),
    }
}

/// Map the JSON status string to a `SummaryStatus`.
fn classify_status(status: &str, error_type: &Option<String>) -> SummaryStatus {
    match status {
        "ok" => SummaryStatus::Pass,
        "error" => {
            // Distinguish violations (fail) from infrastructure errors.
            if let Some(et) = error_type {
                match et.as_str() {
                    "invariant_violation"
                    | "deadlock"
                    | "liveness_violation"
                    | "assertion_failure"
                    | "property_violation" => SummaryStatus::Fail,
                    _ => SummaryStatus::Error,
                }
            } else {
                SummaryStatus::Error
            }
        }
        _ => SummaryStatus::Error,
    }
}

/// Determine deadlock status from error_type.
fn classify_deadlock(error_type: &Option<String>) -> DeadlockStatus {
    match error_type.as_deref() {
        Some("deadlock") => DeadlockStatus::Found,
        _ => DeadlockStatus::None,
    }
}

/// Extract a human-readable spec name from a file path.
fn spec_name_from_path(path: &Path) -> String {
    path.file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| path.display().to_string())
}

// ---------------------------------------------------------------------------
// Sorting
// ---------------------------------------------------------------------------

/// Sort summary rows by the requested field.
fn sort_rows(rows: &mut [SummaryRow], sort_by: SummarySortField) {
    match sort_by {
        SummarySortField::Name => {
            rows.sort_by(|a, b| a.name.to_lowercase().cmp(&b.name.to_lowercase()));
        }
        SummarySortField::States => {
            rows.sort_by(|a, b| {
                b.distinct_states
                    .cmp(&a.distinct_states)
                    .then_with(|| a.name.cmp(&b.name))
            });
        }
        SummarySortField::Time => {
            rows.sort_by(|a, b| {
                b.time_seconds
                    .partial_cmp(&a.time_seconds)
                    .unwrap_or(Ordering::Equal)
                    .then_with(|| a.name.cmp(&b.name))
            });
        }
        SummarySortField::Status => {
            rows.sort_by(|a, b| a.status.cmp(&b.status).then_with(|| a.name.cmp(&b.name)));
        }
    }
}

// ---------------------------------------------------------------------------
// Output: Human-readable aligned table
// ---------------------------------------------------------------------------

/// Computed column widths for the aligned ASCII table.
struct ColumnWidths {
    name: usize,
    status: usize,
    distinct: usize,
    total: usize,
    time: usize,
    inv: usize,
    deadlock: usize,
}

impl ColumnWidths {
    /// Compute column widths from data, clamped to header minimums.
    fn from_rows(rows: &[SummaryRow]) -> Self {
        let mut w = Self {
            name: "Spec".len(),
            status: "Status".len(),
            distinct: "Distinct".len(),
            total: "Total".len(),
            time: "Time(s)".len(),
            inv: "Inv".len(),
            deadlock: "Deadlock".len(),
        };
        for r in rows {
            w.name = w.name.max(r.name.len()).min(40);
            w.status = w.status.max(r.status.to_string().len());
            w.distinct = w.distinct.max(format_u64(r.distinct_states).len());
            w.total = w.total.max(format_u64(r.total_states).len());
            w.time = w.time.max(format_time(r.time_seconds).len());
            w.inv = w.inv.max(r.invariants_checked.to_string().len());
            w.deadlock = w.deadlock.max(r.deadlock.to_string().len());
        }
        w
    }

    /// Total separator line width including border characters.
    fn separator_width(&self) -> usize {
        // "| col1 | col2 | ... | colN |"
        // Each column: width + 2 padding (space before+after) + 1 pipe
        // Plus leading "| " and trailing " |" == +4
        // 7 columns => 6 inner " | " (3 chars each) => 18
        // Edges: "| " (2) + " |" (2) => 4
        self.name + self.status + self.distinct + self.total + self.time + self.inv + self.deadlock
            + 6 * 3 // 6 inner separators " | "
            + 4 // edge "| " + " |"
    }
}

/// Print the human-readable aligned ASCII table to stdout.
fn print_human(rows: &[SummaryRow]) {
    if rows.is_empty() {
        println!("No specs to summarize.");
        return;
    }

    let w = ColumnWidths::from_rows(rows);
    let sep = "-".repeat(w.separator_width());

    // Header row.
    println!(
        "| {:<nw$} | {:<sw$} | {:>dw$} | {:>tw$} | {:>tmw$} | {:>iw$} | {:<dlw$} |",
        "Spec",
        "Status",
        "Distinct",
        "Total",
        "Time(s)",
        "Inv",
        "Deadlock",
        nw = w.name,
        sw = w.status,
        dw = w.distinct,
        tw = w.total,
        tmw = w.time,
        iw = w.inv,
        dlw = w.deadlock,
    );
    println!("{sep}");

    // Data rows.
    for r in rows {
        let status_colored = status_ansi(&r.status);
        let status_plain = r.status.to_string();
        let status_pad = w.status.saturating_sub(status_plain.len());

        println!(
            "| {:<nw$} | {}{} | {:>dw$} | {:>tw$} | {:>tmw$} | {:>iw$} | {:<dlw$} |",
            truncate_str(&r.name, w.name),
            status_colored,
            " ".repeat(status_pad),
            format_u64(r.distinct_states),
            format_u64(r.total_states),
            format_time(r.time_seconds),
            r.invariants_checked,
            r.deadlock,
            nw = w.name,
            dw = w.distinct,
            tw = w.total,
            tmw = w.time,
            iw = w.inv,
            dlw = w.deadlock,
        );
    }
    println!("{sep}");

    // Footer: aggregate summary.
    let total = rows.len();
    let pass = rows
        .iter()
        .filter(|r| r.status == SummaryStatus::Pass)
        .count();
    let fail = rows
        .iter()
        .filter(|r| r.status == SummaryStatus::Fail)
        .count();
    let error = rows
        .iter()
        .filter(|r| r.status == SummaryStatus::Error)
        .count();
    let total_distinct: u64 = rows.iter().map(|r| r.distinct_states).sum();
    let total_time: f64 = rows.iter().map(|r| r.time_seconds).sum();

    println!(
        "{total} specs: {pass} pass, {fail} fail, {error} error | \
         {states} distinct states | {time:.1}s total",
        states = format_u64(total_distinct),
        time = total_time,
    );
}

/// Return an ANSI-colored status string for terminal output.
fn status_ansi(status: &SummaryStatus) -> String {
    match status {
        SummaryStatus::Pass => format!("\x1b[32m{status}\x1b[0m"),
        SummaryStatus::Fail => format!("\x1b[31m{status}\x1b[0m"),
        SummaryStatus::Error => format!("\x1b[33m{status}\x1b[0m"),
    }
}

/// Format a `u64` with thousands separators (e.g. `1,234,567`).
fn format_u64(n: u64) -> String {
    if n == 0 {
        return "0".to_string();
    }
    let s = n.to_string();
    let mut result = String::with_capacity(s.len() + s.len() / 3);
    for (i, ch) in s.chars().rev().enumerate() {
        if i > 0 && i % 3 == 0 {
            result.push(',');
        }
        result.push(ch);
    }
    result.chars().rev().collect()
}

/// Format seconds with appropriate precision for display.
fn format_time(secs: f64) -> String {
    if secs < 0.01 {
        format!("{secs:.4}")
    } else if secs < 1.0 {
        format!("{secs:.3}")
    } else if secs < 100.0 {
        format!("{secs:.2}")
    } else if secs < 3600.0 {
        let total = secs as u64;
        format!("{}m{:02}s", total / 60, total % 60)
    } else {
        let total = secs as u64;
        format!("{}h{}m", total / 3600, (total % 3600) / 60)
    }
}

/// Truncate a string to fit within `max_len`, appending "..." if needed.
fn truncate_str(s: &str, max_len: usize) -> String {
    if s.len() <= max_len {
        s.to_string()
    } else if max_len <= 3 {
        s[..max_len].to_string()
    } else {
        format!("{}...", &s[..max_len.saturating_sub(3)])
    }
}

// ---------------------------------------------------------------------------
// Output: JSON
// ---------------------------------------------------------------------------

/// Print summary rows as a pretty-printed JSON array to stdout.
fn print_json(rows: &[SummaryRow]) -> Result<()> {
    let json = serde_json::to_string_pretty(rows).context("serialize summary JSON")?;
    println!("{json}");
    Ok(())
}

// ---------------------------------------------------------------------------
// Output: CSV
// ---------------------------------------------------------------------------

/// Print summary rows as CSV to stdout.
fn print_csv(rows: &[SummaryRow]) {
    println!("name,status,distinct_states,total_states,time_seconds,invariants_checked,deadlock");
    for r in rows {
        println!(
            "{},{},{},{},{:.4},{},{}",
            csv_escape(&r.name),
            r.status,
            r.distinct_states,
            r.total_states,
            r.time_seconds,
            r.invariants_checked,
            r.deadlock,
        );
    }
}

/// Escape a string value for safe CSV embedding (RFC 4180).
fn csv_escape(s: &str) -> String {
    if s.contains(',') || s.contains('"') || s.contains('\n') {
        format!("\"{}\"", s.replace('"', "\"\""))
    } else {
        s.to_string()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- Test helpers -------------------------------------------------------

    /// Write a sidecar JSON file in a temp dir and return the `.tla` path.
    fn write_sidecar(dir: &Path, stem: &str, json: &str) -> PathBuf {
        let tla_path = dir.join(format!("{stem}.tla"));
        fs::write(&tla_path, "---- MODULE Dummy ----\n====\n").expect("write tla");
        let sidecar = dir.join(format!("{stem}.tla2-check.json"));
        fs::write(&sidecar, json).expect("write sidecar");
        tla_path
    }

    fn minimal_sidecar_json(
        status: &str,
        error_type: Option<&str>,
        distinct: u64,
        total: u64,
        time: f64,
    ) -> String {
        let et = match error_type {
            Some(t) => format!("\"error_type\": \"{t}\","),
            None => String::new(),
        };
        format!(
            r#"{{
  "version": "1.3",
  "tool": "tla2",
  "timestamp": "2026-03-30T00:00:00Z",
  "input": {{ "spec_file": "test.tla", "module": "Test", "workers": 1 }},
  "specification": {{
    "invariants": ["TypeOK", "Safety"],
    "properties": [],
    "constants": {{}},
    "variables": ["x"]
  }},
  "soundness": {{ "mode": "sound", "features_used": [], "deviations": [], "assumptions": [] }},
  "completeness": "exhaustive",
  "result": {{ "status": "{status}", {et} "error_message": null }},
  "statistics": {{
    "states_found": {total},
    "states_distinct": {distinct},
    "time_seconds": {time},
    "transitions": 0,
    "states_initial": 1
  }},
  "diagnostics": {{ "warnings": [], "infos": [] }}
}}"#,
        )
    }

    fn make_test_row(name: &str, status: SummaryStatus, states: u64, time: f64) -> SummaryRow {
        SummaryRow {
            name: name.to_string(),
            status,
            distinct_states: states,
            total_states: states * 2,
            time_seconds: time,
            invariants_checked: 1,
            deadlock: DeadlockStatus::None,
            source_path: None,
            error_message: None,
        }
    }

    // -- Status classification tests ----------------------------------------

    #[test]
    fn test_classify_status_ok() {
        assert_eq!(classify_status("ok", &None), SummaryStatus::Pass);
    }

    #[test]
    fn test_classify_status_invariant_violation() {
        assert_eq!(
            classify_status("error", &Some("invariant_violation".to_string())),
            SummaryStatus::Fail,
        );
    }

    #[test]
    fn test_classify_status_deadlock() {
        assert_eq!(
            classify_status("error", &Some("deadlock".to_string())),
            SummaryStatus::Fail,
        );
    }

    #[test]
    fn test_classify_status_liveness_violation() {
        assert_eq!(
            classify_status("error", &Some("liveness_violation".to_string())),
            SummaryStatus::Fail,
        );
    }

    #[test]
    fn test_classify_status_assertion_failure() {
        assert_eq!(
            classify_status("error", &Some("assertion_failure".to_string())),
            SummaryStatus::Fail,
        );
    }

    #[test]
    fn test_classify_status_parse_error() {
        assert_eq!(
            classify_status("error", &Some("parse_error".to_string())),
            SummaryStatus::Error,
        );
    }

    #[test]
    fn test_classify_status_error_no_type() {
        assert_eq!(classify_status("error", &None), SummaryStatus::Error);
    }

    #[test]
    fn test_classify_status_unknown_status() {
        assert_eq!(classify_status("timeout", &None), SummaryStatus::Error);
    }

    // -- Deadlock classification tests --------------------------------------

    #[test]
    fn test_classify_deadlock_found() {
        assert_eq!(
            classify_deadlock(&Some("deadlock".to_string())),
            DeadlockStatus::Found,
        );
    }

    #[test]
    fn test_classify_deadlock_none() {
        assert_eq!(classify_deadlock(&None), DeadlockStatus::None);
    }

    #[test]
    fn test_classify_deadlock_other_error() {
        assert_eq!(
            classify_deadlock(&Some("invariant_violation".to_string())),
            DeadlockStatus::None,
        );
    }

    // -- Formatting tests ---------------------------------------------------

    #[test]
    fn test_format_u64_zero() {
        assert_eq!(format_u64(0), "0");
    }

    #[test]
    fn test_format_u64_small() {
        assert_eq!(format_u64(42), "42");
        assert_eq!(format_u64(999), "999");
    }

    #[test]
    fn test_format_u64_thousands() {
        assert_eq!(format_u64(1_000), "1,000");
        assert_eq!(format_u64(1_234_567), "1,234,567");
    }

    #[test]
    fn test_format_u64_large() {
        assert_eq!(format_u64(1_000_000_000), "1,000,000,000");
        assert_eq!(format_u64(123_456_789), "123,456,789");
    }

    #[test]
    fn test_format_time_very_fast() {
        let s = format_time(0.001);
        assert_eq!(s, "0.0010");
    }

    #[test]
    fn test_format_time_sub_second() {
        let s = format_time(0.5);
        assert_eq!(s, "0.500");
    }

    #[test]
    fn test_format_time_seconds() {
        let s = format_time(12.345);
        assert_eq!(s, "12.35");
    }

    #[test]
    fn test_format_time_minutes() {
        let s = format_time(125.0);
        assert_eq!(s, "2m05s");
    }

    #[test]
    fn test_format_time_hours() {
        let s = format_time(3700.0);
        assert_eq!(s, "1h01m");
    }

    #[test]
    fn test_truncate_str_short() {
        assert_eq!(truncate_str("Foo", 30), "Foo");
    }

    #[test]
    fn test_truncate_str_exact() {
        assert_eq!(truncate_str("abcde", 5), "abcde");
    }

    #[test]
    fn test_truncate_str_long() {
        let result = truncate_str("VeryLongSpecificationName", 10);
        assert!(result.len() <= 10, "got len {}: {result}", result.len());
        assert!(result.ends_with("..."));
    }

    #[test]
    fn test_truncate_str_tiny_max() {
        assert_eq!(truncate_str("abcdef", 3), "abc");
    }

    // -- CSV escaping tests -------------------------------------------------

    #[test]
    fn test_csv_escape_plain() {
        assert_eq!(csv_escape("hello"), "hello");
    }

    #[test]
    fn test_csv_escape_with_comma() {
        assert_eq!(csv_escape("a,b"), "\"a,b\"");
    }

    #[test]
    fn test_csv_escape_with_quotes() {
        assert_eq!(csv_escape("say \"hi\""), "\"say \"\"hi\"\"\"");
    }

    #[test]
    fn test_csv_escape_with_newline() {
        assert_eq!(csv_escape("line1\nline2"), "\"line1\nline2\"");
    }

    // -- Path utility tests -------------------------------------------------

    #[test]
    fn test_spec_name_from_path() {
        assert_eq!(
            spec_name_from_path(Path::new("/foo/bar/MCBakery.tla")),
            "MCBakery",
        );
        assert_eq!(spec_name_from_path(Path::new("Spec.tla")), "Spec");
    }

    #[test]
    fn test_sidecar_path_for() {
        let tla = PathBuf::from("/specs/MCBakery.tla");
        assert_eq!(
            sidecar_path_for(&tla),
            PathBuf::from("/specs/MCBakery.tla2-check.json"),
        );
    }

    #[test]
    fn test_sidecar_path_for_relative() {
        let tla = PathBuf::from("Spec.tla");
        assert_eq!(
            sidecar_path_for(&tla),
            PathBuf::from("Spec.tla2-check.json"),
        );
    }

    // -- Sidecar reading tests ----------------------------------------------

    #[test]
    fn test_read_sidecar_pass() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let json = minimal_sidecar_json("ok", None, 1234, 5678, 1.5);
        let tla = write_sidecar(dir.path(), "TestSpec", &json);

        let sidecar = read_sidecar(&sidecar_path_for(&tla));
        assert!(sidecar.is_some());
        let s = sidecar.unwrap();
        assert_eq!(s.result.status, "ok");
        assert_eq!(s.statistics.states_distinct, Some(1234));
        assert_eq!(s.statistics.states_found, 5678);
    }

    #[test]
    fn test_read_sidecar_missing() {
        let path = PathBuf::from("/nonexistent/path.tla2-check.json");
        assert!(read_sidecar(&path).is_none());
    }

    #[test]
    fn test_read_sidecar_malformed() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let bad_path = dir.path().join("Bad.tla2-check.json");
        fs::write(&bad_path, "not json at all").expect("write");
        assert!(read_sidecar(&bad_path).is_none());
    }

    // -- Row construction tests ---------------------------------------------

    #[test]
    fn test_build_row_with_sidecar() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let json = minimal_sidecar_json("ok", None, 100, 200, 0.5);
        let tla = write_sidecar(dir.path(), "GoodSpec", &json);

        let row = build_row(&tla);
        assert_eq!(row.name, "GoodSpec");
        assert_eq!(row.status, SummaryStatus::Pass);
        assert_eq!(row.distinct_states, 100);
        assert_eq!(row.total_states, 200);
        assert!((row.time_seconds - 0.5).abs() < 0.001);
        assert_eq!(row.invariants_checked, 2); // TypeOK + Safety from json
        assert_eq!(row.deadlock, DeadlockStatus::None);
    }

    #[test]
    fn test_build_row_no_sidecar() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let tla = dir.path().join("NoSidecar.tla");
        fs::write(&tla, "---- MODULE NoSidecar ----\n====\n").expect("write");

        let row = build_row(&tla);
        assert_eq!(row.name, "NoSidecar");
        assert_eq!(row.status, SummaryStatus::Error);
        assert!(row.error_message.is_some());
        assert!(
            row.error_message.as_ref().unwrap().contains("no sidecar"),
            "error_message: {:?}",
            row.error_message,
        );
    }

    #[test]
    fn test_build_row_fail_invariant() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let json = minimal_sidecar_json("error", Some("invariant_violation"), 50, 100, 0.2);
        let tla = write_sidecar(dir.path(), "BadSpec", &json);

        let row = build_row(&tla);
        assert_eq!(row.status, SummaryStatus::Fail);
    }

    #[test]
    fn test_build_row_fail_deadlock() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let json = minimal_sidecar_json("error", Some("deadlock"), 50, 100, 0.1);
        let tla = write_sidecar(dir.path(), "Deadlocked", &json);

        let row = build_row(&tla);
        assert_eq!(row.status, SummaryStatus::Fail);
        assert_eq!(row.deadlock, DeadlockStatus::Found);
    }

    // -- Sorting tests ------------------------------------------------------

    #[test]
    fn test_sort_by_name() {
        let mut rows = vec![
            make_test_row("Zebra", SummaryStatus::Pass, 100, 1.0),
            make_test_row("Alpha", SummaryStatus::Pass, 200, 2.0),
            make_test_row("Middle", SummaryStatus::Fail, 50, 0.5),
        ];
        sort_rows(&mut rows, SummarySortField::Name);
        assert_eq!(rows[0].name, "Alpha");
        assert_eq!(rows[1].name, "Middle");
        assert_eq!(rows[2].name, "Zebra");
    }

    #[test]
    fn test_sort_by_name_case_insensitive() {
        let mut rows = vec![
            make_test_row("zebra", SummaryStatus::Pass, 100, 1.0),
            make_test_row("Alpha", SummaryStatus::Pass, 200, 2.0),
        ];
        sort_rows(&mut rows, SummarySortField::Name);
        assert_eq!(rows[0].name, "Alpha");
        assert_eq!(rows[1].name, "zebra");
    }

    #[test]
    fn test_sort_by_states_descending() {
        let mut rows = vec![
            make_test_row("Small", SummaryStatus::Pass, 10, 1.0),
            make_test_row("Big", SummaryStatus::Pass, 1000, 2.0),
            make_test_row("Medium", SummaryStatus::Pass, 100, 0.5),
        ];
        sort_rows(&mut rows, SummarySortField::States);
        assert_eq!(rows[0].name, "Big");
        assert_eq!(rows[1].name, "Medium");
        assert_eq!(rows[2].name, "Small");
    }

    #[test]
    fn test_sort_by_time_descending() {
        let mut rows = vec![
            make_test_row("Fast", SummaryStatus::Pass, 100, 0.1),
            make_test_row("Slow", SummaryStatus::Pass, 100, 10.0),
            make_test_row("Mid", SummaryStatus::Pass, 100, 1.0),
        ];
        sort_rows(&mut rows, SummarySortField::Time);
        assert_eq!(rows[0].name, "Slow");
        assert_eq!(rows[1].name, "Mid");
        assert_eq!(rows[2].name, "Fast");
    }

    #[test]
    fn test_sort_by_status() {
        let mut rows = vec![
            make_test_row("Err", SummaryStatus::Error, 0, 0.0),
            make_test_row("OK", SummaryStatus::Pass, 100, 1.0),
            make_test_row("Bad", SummaryStatus::Fail, 50, 0.5),
        ];
        sort_rows(&mut rows, SummarySortField::Status);
        // Derived PartialOrd: Pass < Fail < Error
        assert_eq!(rows[0].status, SummaryStatus::Pass);
        assert_eq!(rows[1].status, SummaryStatus::Fail);
        assert_eq!(rows[2].status, SummaryStatus::Error);
    }

    #[test]
    fn test_sort_by_status_tiebreak_by_name() {
        let mut rows = vec![
            make_test_row("B", SummaryStatus::Pass, 100, 1.0),
            make_test_row("A", SummaryStatus::Pass, 200, 2.0),
        ];
        sort_rows(&mut rows, SummarySortField::Status);
        assert_eq!(rows[0].name, "A");
        assert_eq!(rows[1].name, "B");
    }

    // -- File collection tests ----------------------------------------------

    #[test]
    fn test_collect_tla_files_from_dir() {
        let dir = tempfile::tempdir().expect("create tempdir");
        fs::write(dir.path().join("A.tla"), "").expect("write");
        fs::write(dir.path().join("B.tla"), "").expect("write");
        fs::write(dir.path().join("C.cfg"), "").expect("write");

        let files = collect_tla_files(&[dir.path().to_path_buf()]).expect("collect");
        assert_eq!(files.len(), 2);
        let names: Vec<_> = files
            .iter()
            .map(|p| p.file_name().unwrap().to_str().unwrap().to_string())
            .collect();
        assert!(names.contains(&"A.tla".to_string()));
        assert!(names.contains(&"B.tla".to_string()));
    }

    #[test]
    fn test_collect_tla_files_recursive() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let sub = dir.path().join("sub");
        fs::create_dir(&sub).expect("mkdir");
        fs::write(dir.path().join("Top.tla"), "").expect("write");
        fs::write(sub.join("Nested.tla"), "").expect("write");

        let files = collect_tla_files(&[dir.path().to_path_buf()]).expect("collect");
        assert_eq!(files.len(), 2);
    }

    #[test]
    fn test_collect_tla_files_single_file() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let tla = dir.path().join("Spec.tla");
        fs::write(&tla, "").expect("write");

        let files = collect_tla_files(&[tla.clone()]).expect("collect");
        assert_eq!(files.len(), 1);
        assert_eq!(files[0], tla);
    }

    #[test]
    fn test_collect_tla_files_invalid_extension() {
        let result = collect_tla_files(&[PathBuf::from("foo.txt")]);
        assert!(result.is_err());
    }

    #[test]
    fn test_collect_tla_files_dedup() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let tla = dir.path().join("Spec.tla");
        fs::write(&tla, "").expect("write");

        let files = collect_tla_files(&[tla.clone(), tla.clone()]).expect("collect");
        assert_eq!(files.len(), 1);
    }

    // -- Integration: cmd_summary entry point tests -------------------------

    #[test]
    fn test_cmd_summary_empty_paths() {
        let result = cmd_summary(
            &[],
            None,
            1,
            SummaryOutputFormat::Human,
            SummarySortField::Name,
            None,
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_cmd_summary_no_tla_files() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let result = cmd_summary(
            &[dir.path().to_path_buf()],
            None,
            1,
            SummaryOutputFormat::Human,
            SummarySortField::Name,
            None,
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_cmd_summary_json_output() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let json = minimal_sidecar_json("ok", None, 42, 84, 0.1);
        write_sidecar(dir.path(), "MySpec", &json);

        let result = cmd_summary(
            &[dir.path().to_path_buf()],
            None,
            1,
            SummaryOutputFormat::Json,
            SummarySortField::Name,
            None,
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_cmd_summary_csv_output() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let json = minimal_sidecar_json("ok", None, 42, 84, 0.1);
        write_sidecar(dir.path(), "MySpec", &json);

        let result = cmd_summary(
            &[dir.path().to_path_buf()],
            None,
            1,
            SummaryOutputFormat::Csv,
            SummarySortField::Name,
            None,
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_cmd_summary_human_output() {
        let dir = tempfile::tempdir().expect("create tempdir");
        let json = minimal_sidecar_json("ok", None, 42, 84, 0.1);
        write_sidecar(dir.path(), "MySpec", &json);

        let result = cmd_summary(
            &[dir.path().to_path_buf()],
            None,
            1,
            SummaryOutputFormat::Human,
            SummarySortField::Name,
            None,
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_cmd_summary_with_status_filter_pass() {
        let dir = tempfile::tempdir().expect("create tempdir");
        write_sidecar(
            dir.path(),
            "Good",
            &minimal_sidecar_json("ok", None, 100, 200, 1.0),
        );
        write_sidecar(
            dir.path(),
            "Bad",
            &minimal_sidecar_json("error", Some("invariant_violation"), 50, 100, 0.5),
        );

        // Filter to pass only.
        let result = cmd_summary(
            &[dir.path().to_path_buf()],
            None,
            1,
            SummaryOutputFormat::Json,
            SummarySortField::Name,
            Some("pass"),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_cmd_summary_with_status_filter_fail() {
        let dir = tempfile::tempdir().expect("create tempdir");
        write_sidecar(
            dir.path(),
            "Good",
            &minimal_sidecar_json("ok", None, 100, 200, 1.0),
        );
        write_sidecar(
            dir.path(),
            "Bad",
            &minimal_sidecar_json("error", Some("invariant_violation"), 50, 100, 0.5),
        );

        let result = cmd_summary(
            &[dir.path().to_path_buf()],
            None,
            1,
            SummaryOutputFormat::Json,
            SummarySortField::Name,
            Some("fail"),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_cmd_summary_multiple_specs() {
        let dir = tempfile::tempdir().expect("create tempdir");
        write_sidecar(
            dir.path(),
            "Spec1",
            &minimal_sidecar_json("ok", None, 100, 200, 1.0),
        );
        write_sidecar(
            dir.path(),
            "Spec2",
            &minimal_sidecar_json("ok", None, 500, 1000, 3.0),
        );
        write_sidecar(
            dir.path(),
            "Spec3",
            &minimal_sidecar_json("error", Some("deadlock"), 25, 50, 0.1),
        );

        let result = cmd_summary(
            &[dir.path().to_path_buf()],
            None,
            1,
            SummaryOutputFormat::Human,
            SummarySortField::States,
            None,
        );
        assert!(result.is_ok());
    }

    // -- Serialization roundtrip tests --------------------------------------

    #[test]
    fn test_summary_row_serialization_roundtrip() {
        let row = SummaryRow {
            name: "TestSpec".to_string(),
            status: SummaryStatus::Pass,
            distinct_states: 1234,
            total_states: 5678,
            time_seconds: 1.5,
            invariants_checked: 2,
            deadlock: DeadlockStatus::None,
            source_path: Some("/path/to/TestSpec.tla".to_string()),
            error_message: None,
        };
        let json = serde_json::to_string(&row).expect("serialize");
        let parsed: SummaryRow = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(parsed.name, "TestSpec");
        assert_eq!(parsed.status, SummaryStatus::Pass);
        assert_eq!(parsed.distinct_states, 1234);
        assert_eq!(parsed.total_states, 5678);
        assert_eq!(parsed.deadlock, DeadlockStatus::None);
        assert!(parsed.error_message.is_none());
    }

    #[test]
    fn test_summary_row_with_error_serialization() {
        let row = SummaryRow {
            name: "BadSpec".to_string(),
            status: SummaryStatus::Fail,
            distinct_states: 50,
            total_states: 100,
            time_seconds: 0.2,
            invariants_checked: 1,
            deadlock: DeadlockStatus::Found,
            source_path: None,
            error_message: Some("deadlock detected".to_string()),
        };
        let json = serde_json::to_string_pretty(&row).expect("serialize");
        let parsed: SummaryRow = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(parsed.status, SummaryStatus::Fail);
        assert_eq!(parsed.deadlock, DeadlockStatus::Found);
        assert_eq!(parsed.error_message.as_deref(), Some("deadlock detected"));
    }

    // -- Display trait tests ------------------------------------------------

    #[test]
    fn test_summary_status_display() {
        assert_eq!(SummaryStatus::Pass.to_string(), "pass");
        assert_eq!(SummaryStatus::Fail.to_string(), "fail");
        assert_eq!(SummaryStatus::Error.to_string(), "error");
    }

    #[test]
    fn test_deadlock_status_display() {
        assert_eq!(DeadlockStatus::None.to_string(), "none");
        assert_eq!(DeadlockStatus::Disabled.to_string(), "off");
        assert_eq!(DeadlockStatus::Found.to_string(), "FOUND");
    }

    // -- Human output smoke tests -------------------------------------------

    #[test]
    fn test_human_output_empty() {
        // Smoke test: verifies no panic on empty input and that column widths
        // handle the empty case gracefully.
        let widths = ColumnWidths::from_rows(&[]);
        assert_eq!(
            widths.name,
            "Spec".len(),
            "empty rows should use header-minimum column widths"
        );
        print_human(&[]);
    }

    #[test]
    fn test_human_output_single_row() {
        let rows = vec![make_test_row("Spec", SummaryStatus::Pass, 42, 0.1)];
        // Smoke test: verifies no panic and correct column width calculation.
        let widths = ColumnWidths::from_rows(&rows);
        assert!(
            widths.name >= 4,
            "name column should be at least as wide as 'Spec'"
        );
        print_human(&rows);
    }

    // -- CSV output smoke tests ---------------------------------------------

    #[test]
    fn test_csv_escapes_commas_in_name() {
        // Verify csv_escape correctly quotes names containing commas
        assert_eq!(
            csv_escape("Has,Comma"),
            "\"Has,Comma\"",
            "csv_escape should wrap comma-containing strings in quotes"
        );
        assert_eq!(
            csv_escape("NoPunctuation"),
            "NoPunctuation",
            "csv_escape should not quote strings without special chars"
        );

        let rows = vec![SummaryRow {
            name: "Has,Comma".to_string(),
            status: SummaryStatus::Pass,
            distinct_states: 1,
            total_states: 1,
            time_seconds: 0.0,
            invariants_checked: 0,
            deadlock: DeadlockStatus::None,
            source_path: None,
            error_message: None,
        }];
        // Smoke test: verifies no panic on comma-containing name.
        print_csv(&rows);
    }

    // -- Column width tests -------------------------------------------------

    #[test]
    fn test_column_widths_minimum() {
        let w = ColumnWidths::from_rows(&[]);
        assert!(w.name >= 4); // "Spec"
        assert!(w.status >= 6); // "Status"
        assert!(w.distinct >= 8); // "Distinct"
    }

    #[test]
    fn test_column_widths_grow_with_data() {
        let rows = vec![make_test_row(
            "VeryLongSpecificationName",
            SummaryStatus::Pass,
            1_234_567,
            999.9,
        )];
        let w = ColumnWidths::from_rows(&rows);
        assert!(w.name >= "VeryLongSpecificationName".len().min(40));
        assert!(w.distinct >= "1,234,567".len());
    }

    #[test]
    fn test_separator_width_positive() {
        let rows = vec![make_test_row("Spec", SummaryStatus::Pass, 100, 1.0)];
        let w = ColumnWidths::from_rows(&rows);
        assert!(w.separator_width() > 0);
    }
}
