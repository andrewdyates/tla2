// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The `bisect` subcommand: binary search over a CONSTANT integer value to find
//! the minimal configuration that triggers an invariant violation.
//!
//! Usage:
//!   tla2 bisect Spec.tla --config Spec.cfg --constant N --low 1 --high 100
//!
//! At each step, creates a temporary .cfg with the constant set to the mid value,
//! runs `tla2 check --output json --continue-on-error --workers 1`, and narrows
//! the search range based on whether a violation was found.

use std::io::Write as _;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};

use crate::cli_schema::BisectOutputFormat;

// ── Bisect modes ─────────────────────────────────────────────────────────────

/// What the bisect is searching for.
#[derive(Debug, Clone, Copy)]
pub(crate) enum BisectMode {
    /// Find the minimal constant value that triggers an invariant violation.
    Violation,
    /// Find the minimal constant value where state count exceeds a threshold.
    StateCount { threshold: u64 },
}

// ── Result types ─────────────────────────────────────────────────────────────

/// Outcome of a single probe (one model-checker run at a specific constant value).
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ProbeResult {
    /// The constant value tested.
    value: i64,
    /// Whether a violation was found.
    violation: bool,
    /// Number of states found by the checker.
    states_found: u64,
    /// Number of distinct states.
    distinct_states: u64,
    /// Wall-clock time for this probe in milliseconds.
    wall_time_ms: u64,
    /// Violation description, if any.
    #[serde(skip_serializing_if = "Option::is_none")]
    violation_info: Option<String>,
}

/// Final bisect report.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct BisectReport {
    /// The constant name being bisected.
    constant: String,
    /// Original search range.
    low: i64,
    high: i64,
    /// The minimal value that triggers the condition (None if never triggered).
    #[serde(skip_serializing_if = "Option::is_none")]
    minimal_value: Option<i64>,
    /// All probes executed during the search.
    probes: Vec<ProbeResult>,
    /// Total wall-clock time in milliseconds.
    total_time_ms: u64,
    /// The bisect mode used.
    mode: String,
}

// ── Subset of JSON output we parse from `tla2 check --output json` ───────────

#[derive(Deserialize)]
struct CheckJsonOutput {
    result: CheckJsonResult,
    statistics: CheckJsonStats,
}

#[derive(Deserialize)]
struct CheckJsonResult {
    status: String,
    #[serde(default)]
    violation: Option<CheckJsonViolation>,
}

#[derive(Deserialize)]
struct CheckJsonViolation {
    #[serde(default, rename = "type")]
    kind: Option<String>,
    #[serde(default)]
    invariant: Option<String>,
    #[serde(default)]
    depth: Option<u64>,
}

#[derive(Deserialize)]
struct CheckJsonStats {
    states_found: u64,
    #[serde(default)]
    states_distinct: Option<u64>,
}

// ── Entry point ──────────────────────────────────────────────────────────────

pub(crate) fn cmd_bisect(
    file: &Path,
    config: &Path,
    constant: &str,
    low: i64,
    high: i64,
    mode: BisectMode,
    format: BisectOutputFormat,
    timeout: u64,
) -> Result<()> {
    if low > high {
        bail!("--low ({low}) must be <= --high ({high})");
    }
    if !file.exists() {
        bail!("spec file not found: {}", file.display());
    }
    if !config.exists() {
        bail!("config file not found: {}", config.display());
    }

    let cfg_text = std::fs::read_to_string(config)
        .with_context(|| format!("read config {}", config.display()))?;

    let exe = std::env::current_exe().context("resolve current exe path")?;
    let total_start = Instant::now();

    let mode_str = match mode {
        BisectMode::Violation => "violation".to_string(),
        BisectMode::StateCount { threshold } => format!("state-count (threshold: {threshold})"),
    };

    if matches!(format, BisectOutputFormat::Human) {
        eprintln!(
            "Bisecting {} in [{}, {}] on {} (mode: {})",
            constant,
            low,
            high,
            file.display(),
            mode_str,
        );
        eprintln!();
    }

    let mut probes = Vec::new();
    let mut lo = low;
    let mut hi = high;
    let mut best_fail: Option<i64> = None;

    while lo <= hi {
        let mid = lo + (hi - lo) / 2;

        let probe = run_probe(
            &exe, file, &cfg_text, constant, mid, timeout, format,
        )?;

        let triggered = match mode {
            BisectMode::Violation => probe.violation,
            BisectMode::StateCount { threshold } => probe.states_found > threshold,
        };

        if triggered {
            best_fail = Some(mid);
            hi = mid - 1;
        } else {
            lo = mid + 1;
        }

        probes.push(probe);
    }

    let total_time_ms = total_start.elapsed().as_millis() as u64;

    let report = BisectReport {
        constant: constant.to_string(),
        low,
        high,
        minimal_value: best_fail,
        probes,
        total_time_ms,
        mode: match mode {
            BisectMode::Violation => "violation".to_string(),
            BisectMode::StateCount { threshold } => {
                format!("state-count:{threshold}")
            }
        },
    };

    match format {
        BisectOutputFormat::Human => print_human_report(&report),
        BisectOutputFormat::Json => print_json_report(&report)?,
    }

    Ok(())
}

// ── Single probe execution ───────────────────────────────────────────────────

/// Run the model checker with the constant set to `value`, return the probe result.
fn run_probe(
    exe: &Path,
    tla_path: &Path,
    cfg_text: &str,
    constant: &str,
    value: i64,
    timeout_secs: u64,
    format: BisectOutputFormat,
) -> Result<ProbeResult> {
    // Create a temporary .cfg file with the constant override.
    let tmp_dir = std::env::temp_dir().join(format!(
        "tla2-bisect-{}-{}",
        std::process::id(),
        value,
    ));
    std::fs::create_dir_all(&tmp_dir)
        .with_context(|| format!("create temp dir {}", tmp_dir.display()))?;
    let tmp_cfg = tmp_dir.join("bisect.cfg");
    let modified_cfg = override_constant_in_cfg(cfg_text, constant, value);
    std::fs::write(&tmp_cfg, &modified_cfg)
        .with_context(|| format!("write temp cfg {}", tmp_cfg.display()))?;

    let start = Instant::now();

    if matches!(format, BisectOutputFormat::Human) {
        eprint!("  Checking {}={} ... ", constant, value);
        std::io::stderr().flush().ok();
    }

    let mut cmd = std::process::Command::new(exe);
    cmd.arg("check")
        .arg(tla_path)
        .arg("--config")
        .arg(&tmp_cfg)
        .arg("--output")
        .arg("json")
        .arg("--continue-on-error")
        .arg("--workers")
        .arg("1")
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());

    let output = if timeout_secs > 0 {
        run_with_timeout(&mut cmd, timeout_secs)?
    } else {
        cmd.output().context("spawn tla2 check subprocess")?
    };

    let elapsed_ms = start.elapsed().as_millis() as u64;
    let stdout = String::from_utf8_lossy(&output.stdout);

    let result = match serde_json::from_str::<CheckJsonOutput>(&stdout) {
        Ok(parsed) => {
            let violation = parsed.result.status == "error";
            let violation_info = parsed.result.violation.as_ref().map(|v| {
                let kind = v.kind.as_deref().unwrap_or("unknown");
                let inv = v.invariant.as_deref().unwrap_or("?");
                let depth = v.depth.map(|d| format!(" at depth {d}")).unwrap_or_default();
                format!("{kind}: {inv}{depth}")
            });

            let states_found = parsed.statistics.states_found;
            let distinct_states = parsed.statistics.states_distinct.unwrap_or(states_found);

            if matches!(format, BisectOutputFormat::Human) {
                if violation {
                    eprintln!(
                        "FAIL ({} states, {}ms) - {}",
                        format_count(states_found),
                        elapsed_ms,
                        violation_info.as_deref().unwrap_or("violation"),
                    );
                } else {
                    eprintln!(
                        "PASS ({} states, {}ms)",
                        format_count(states_found),
                        elapsed_ms,
                    );
                }
            }

            Ok(ProbeResult {
                value,
                violation,
                states_found,
                distinct_states,
                wall_time_ms: elapsed_ms,
                violation_info,
            })
        }
        Err(parse_err) => {
            if matches!(format, BisectOutputFormat::Human) {
                eprintln!("ERROR ({}ms) - failed to parse output", elapsed_ms);
            }

            let stderr = String::from_utf8_lossy(&output.stderr);
            Err(parse_err).with_context(|| {
                format!(
                    "parse JSON from tla2 check (exit={}, {}={}):\nstdout: {}\nstderr: {}",
                    output.status, constant, value, stdout, stderr,
                )
            })
        }
    };

    // Clean up temp directory.
    let _ = std::fs::remove_dir_all(&tmp_dir);

    result
}

/// Run a command with a timeout. Returns the Output if the process completes
/// within the deadline, or kills it and returns an error.
fn run_with_timeout(
    cmd: &mut std::process::Command,
    timeout_secs: u64,
) -> Result<std::process::Output> {
    use std::sync::mpsc;

    let mut child = cmd.spawn().context("spawn tla2 check subprocess")?;
    let deadline = std::time::Duration::from_secs(timeout_secs);

    // Collect stdout/stderr from the child in a background thread so the
    // pipes don't block while we wait.
    let child_stdout = child.stdout.take();
    let child_stderr = child.stderr.take();

    let (tx, rx) = mpsc::channel();
    let wait_thread = std::thread::spawn(move || {
        let stdout = child_stdout
            .map(|mut r| {
                let mut buf = Vec::new();
                std::io::Read::read_to_end(&mut r, &mut buf).ok();
                buf
            })
            .unwrap_or_default();
        let stderr = child_stderr
            .map(|mut r| {
                let mut buf = Vec::new();
                std::io::Read::read_to_end(&mut r, &mut buf).ok();
                buf
            })
            .unwrap_or_default();
        let _ = tx.send((stdout, stderr));
    });

    // Poll the child for completion within the timeout.
    let start = Instant::now();
    let poll_interval = std::time::Duration::from_millis(50);
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                // Process finished. Collect output from the background thread.
                let (stdout, stderr) = rx
                    .recv()
                    .expect("stdout/stderr reader thread dropped sender");
                wait_thread.join().ok();
                return Ok(std::process::Output {
                    status,
                    stdout,
                    stderr,
                });
            }
            Ok(None) => {
                // Still running — check timeout.
                if start.elapsed() >= deadline {
                    child.kill().ok();
                    child.wait().ok();
                    // Drain the reader thread.
                    drop(rx);
                    wait_thread.join().ok();
                    bail!("tla2 check timed out after {timeout_secs}s");
                }
                std::thread::sleep(poll_interval);
            }
            Err(e) => return Err(e).context("wait on tla2 check subprocess"),
        }
    }
}

// ── .cfg constant override ──────────────────────────────────────────────────

/// Produce a modified .cfg text with the given constant set to `value`.
///
/// Strategy: if there is already a line `CONSTANT <name> = <old>` or
/// `<name> = <old>` in a CONSTANT block, replace it. Otherwise, append
/// a CONSTANT section at the end.
fn override_constant_in_cfg(cfg_text: &str, constant: &str, value: i64) -> String {
    let mut lines: Vec<String> = cfg_text.lines().map(String::from).collect();
    let mut found = false;

    // Pattern 1: `CONSTANT name = value` on a single line.
    // Pattern 2: `name = value` (inside a CONSTANT block) or
    //            `name <- value` (model value substitution — less common for integers).
    for line in &mut lines {
        let trimmed = line.trim();
        // Match: `CONSTANT name = <something>`
        if trimmed.starts_with("CONSTANT") || trimmed.starts_with("CONSTANTS") {
            // Could be `CONSTANT N = 3` on one line, or just the section header.
            if let Some(rest) = trimmed
                .strip_prefix("CONSTANTS")
                .or_else(|| trimmed.strip_prefix("CONSTANT"))
            {
                let rest = rest.trim();
                if let Some(after_name) = rest.strip_prefix(constant) {
                    let after_name = after_name.trim_start();
                    if after_name.starts_with('=') {
                        *line = format!("CONSTANT {} = {}", constant, value);
                        found = true;
                    }
                }
            }
        } else {
            // Match bare `name = <something>` inside a CONSTANT block.
            if let Some(after_name) = trimmed.strip_prefix(constant) {
                let after_name = after_name.trim_start();
                if after_name.starts_with('=') {
                    *line = format!("{} = {}", constant, value);
                    found = true;
                }
            }
        }
    }

    if !found {
        // Append a new CONSTANT line.
        lines.push(format!("CONSTANT {} = {}", constant, value));
    }

    let mut result = lines.join("\n");
    if !result.ends_with('\n') {
        result.push('\n');
    }
    result
}

// ── Output formatting ────────────────────────────────────────────────────────

fn print_human_report(report: &BisectReport) {
    eprintln!();
    println!("=== Bisect Result ===");
    println!(
        "Constant: {}  Range: [{}, {}]  Mode: {}",
        report.constant, report.low, report.high, report.mode,
    );
    println!("Probes: {}  Total time: {}ms", report.probes.len(), report.total_time_ms);
    println!();

    match report.minimal_value {
        Some(val) => {
            println!("Minimal failing value: {} = {}", report.constant, val);
            // Find the probe for this value and show violation info.
            if let Some(probe) = report.probes.iter().find(|p| p.value == val) {
                if let Some(ref info) = probe.violation_info {
                    println!("Violation: {info}");
                }
                println!(
                    "States: {}  Time: {}ms",
                    format_count(probe.states_found),
                    probe.wall_time_ms,
                );
            }
        }
        None => {
            println!(
                "No failing value found in [{}, {}].",
                report.low, report.high,
            );
        }
    }

    // Probe summary table.
    println!();
    println!(
        "{:>8} {:>8} {:>12} {:>10}",
        "Value", "Result", "States", "Time"
    );
    println!("{}", "-".repeat(42));
    for probe in &report.probes {
        let result_str = if probe.violation { "FAIL" } else { "PASS" };
        println!(
            "{:>8} {:>8} {:>12} {:>8}ms",
            probe.value,
            result_str,
            format_count(probe.states_found),
            probe.wall_time_ms,
        );
    }
}

fn print_json_report(report: &BisectReport) -> Result<()> {
    let json = serde_json::to_string_pretty(report).context("serialize bisect report")?;
    println!("{json}");
    Ok(())
}

fn format_count(n: u64) -> String {
    if n >= 1_000_000 {
        format!("{:.2}M", n as f64 / 1_000_000.0)
    } else if n >= 1_000 {
        format!("{:.1}K", n as f64 / 1_000.0)
    } else {
        format!("{n}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_override_constant_existing_inline() {
        let cfg = "INIT Init\nNEXT Next\nCONSTANT N = 3\nINVARIANT TypeOK\n";
        let result = override_constant_in_cfg(cfg, "N", 42);
        assert!(
            result.contains("CONSTANT N = 42"),
            "expected override: {result}"
        );
        assert!(
            !result.contains("N = 3"),
            "old value should be gone: {result}"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_override_constant_bare_assignment() {
        let cfg = "INIT Init\nNEXT Next\nCONSTANT\nN = 3\nINVARIANT TypeOK\n";
        let result = override_constant_in_cfg(cfg, "N", 7);
        assert!(
            result.contains("N = 7"),
            "expected override: {result}"
        );
        assert!(
            !result.contains("N = 3"),
            "old value should be gone: {result}"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_override_constant_not_present_appends() {
        let cfg = "INIT Init\nNEXT Next\nINVARIANT TypeOK\n";
        let result = override_constant_in_cfg(cfg, "M", 99);
        assert!(
            result.contains("CONSTANT M = 99"),
            "expected appended constant: {result}"
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_override_constant_does_not_touch_other_constants() {
        let cfg = "CONSTANT\nN = 3\nM = 5\n";
        let result = override_constant_in_cfg(cfg, "N", 10);
        assert!(result.contains("N = 10"), "N should be overridden: {result}");
        assert!(result.contains("M = 5"), "M should be untouched: {result}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_count_small() {
        assert_eq!(format_count(42), "42");
        assert_eq!(format_count(999), "999");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_count_thousands() {
        assert_eq!(format_count(1_234), "1.2K");
        assert_eq!(format_count(50_000), "50.0K");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_count_millions() {
        assert_eq!(format_count(6_016_610), "6.02M");
        assert_eq!(format_count(1_000_000), "1.00M");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_probe_result_serialization_roundtrip() {
        let probe = ProbeResult {
            value: 17,
            violation: true,
            states_found: 1234,
            distinct_states: 1234,
            wall_time_ms: 500,
            violation_info: Some("invariant: Inv at depth 12".to_string()),
        };
        let json = serde_json::to_string(&probe).expect("serialize");
        let parsed: ProbeResult = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(parsed.value, 17);
        assert!(parsed.violation);
        assert_eq!(parsed.states_found, 1234);
        assert!(parsed.violation_info.is_some());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bisect_report_serialization_roundtrip() {
        let report = BisectReport {
            constant: "N".to_string(),
            low: 1,
            high: 100,
            minimal_value: Some(17),
            probes: vec![
                ProbeResult {
                    value: 50,
                    violation: true,
                    states_found: 5000,
                    distinct_states: 5000,
                    wall_time_ms: 300,
                    violation_info: Some("invariant: TypeOK at depth 5".to_string()),
                },
                ProbeResult {
                    value: 25,
                    violation: false,
                    states_found: 2000,
                    distinct_states: 2000,
                    wall_time_ms: 200,
                    violation_info: None,
                },
            ],
            total_time_ms: 1500,
            mode: "violation".to_string(),
        };
        let json = serde_json::to_string_pretty(&report).expect("serialize");
        let parsed: BisectReport = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(parsed.constant, "N");
        assert_eq!(parsed.minimal_value, Some(17));
        assert_eq!(parsed.probes.len(), 2);
    }
}
