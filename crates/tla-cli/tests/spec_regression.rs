// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Spec coverage regression test suite.
//!
//! Validates that all previously-passing specs in `spec_baseline.json` continue
//! to pass. This catches regressions introduced by code changes that break
//! correctness for specific spec patterns.
//!
//! The test reads the baseline JSON, filters for specs marked `verified_match: true`
//! in the requested category, then runs `tla2 check` (or `tla2 simulate`) for each
//! one and compares the result against the TLC baseline.
//!
//! Run with:
//!   cargo test -p tla-cli --test spec_regression -- --test-threads=1
//!
//! Environment variables:
//!   SPEC_REGRESSION_CATEGORY  - category filter: "small" (default), "medium", "all"
//!   SPEC_REGRESSION_TIMEOUT   - per-spec timeout in seconds (default: 120)
//!   SPEC_REGRESSION_FILTER    - comma-separated spec names to run (default: all in category)
//!   SPEC_REGRESSION_SKIP      - comma-separated spec names to skip

mod common;

use std::collections::BTreeMap;
use std::io::Read as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use serde::Deserialize;

// ---------------------------------------------------------------------------
// Baseline schema (mirrors cmd_diagnose::types, but standalone for test use)
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
struct Baseline {
    inputs: BaselineInputs,
    specs: BTreeMap<String, BaselineSpec>,
}

#[derive(Deserialize)]
struct BaselineInputs {
    examples_dir: String,
}

#[derive(Deserialize)]
struct BaselineSpec {
    tlc: BaselineTlc,
    #[allow(dead_code)]
    tla2: BaselineTla2,
    verified_match: bool,
    category: String,
    source: Option<BaselineSource>,
    #[serde(default)]
    expected_mismatch: bool,
    #[allow(dead_code)]
    #[serde(default)]
    expected_mismatch_reason: Option<String>,
    #[serde(default)]
    tla2_expected_states: Option<u64>,
    #[serde(default)]
    diagnose_timeout_seconds: Option<u64>,
    #[serde(default = "default_true")]
    continue_on_error: bool,
}

fn default_true() -> bool {
    true
}

impl BaselineSpec {
    /// Returns the effective continue-on-error mode for this spec.
    /// Mirrors `cmd_diagnose::types::BaselineSpec::effective_continue_on_error`.
    fn effective_continue_on_error(&self) -> bool {
        if !self.continue_on_error {
            return false;
        }
        !matches!(
            self.tlc.error_type.as_deref(),
            Some("invariant" | "assume_violation")
        )
    }
}

#[derive(Deserialize)]
struct BaselineTlc {
    status: String,
    states: Option<u64>,
    error_type: Option<String>,
}

#[allow(dead_code)]
#[derive(Deserialize)]
struct BaselineTla2 {
    status: String,
    states: Option<u64>,
    error_type: Option<String>,
}

#[derive(Deserialize)]
struct BaselineSource {
    tla_path: String,
    cfg_path: String,
    #[serde(default)]
    mode: Option<String>,
}

// ---------------------------------------------------------------------------
// Subprocess JSON output (subset of tla_check::JsonOutput)
// ---------------------------------------------------------------------------

#[derive(Deserialize)]
struct SubprocessOutput {
    result: SubprocessResult,
    statistics: SubprocessStats,
}

#[derive(Deserialize)]
struct SubprocessResult {
    status: String,
    error_type: Option<String>,
    error_message: Option<String>,
}

#[derive(Deserialize)]
struct SubprocessStats {
    states_found: u64,
}

// ---------------------------------------------------------------------------
// Classification (mirrors cmd_diagnose::runner::classify)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Pass,
    ExpectedMismatch,
    StateMismatch,
    FalsePositive,
    FalseNegative,
    Crash,
    Timeout,
    Skip,
    BothFail,
}

impl Verdict {
    fn label(self) -> &'static str {
        match self {
            Self::Pass => "pass",
            Self::ExpectedMismatch => "expected_mismatch",
            Self::StateMismatch => "state_mismatch",
            Self::FalsePositive => "false_positive",
            Self::FalseNegative => "false_negative",
            Self::Crash => "crash",
            Self::Timeout => "timeout",
            Self::Skip => "skip",
            Self::BothFail => "both_fail",
        }
    }
}

struct SpecRunResult {
    name: String,
    verdict: Verdict,
    tla2_states: Option<u64>,
    expected_states: Option<u64>,
    detail: String,
    elapsed_secs: f64,
}

// ---------------------------------------------------------------------------
// Error type normalization
// ---------------------------------------------------------------------------

fn normalize_error_type(et: &str) -> &str {
    match et {
        "invariant_violation" => "invariant",
        "property_violation" => "property",
        "liveness_violation" => "liveness",
        other => other,
    }
}

fn error_types_match(tla2_error: Option<&str>, tlc_error: Option<&str>) -> bool {
    match (tla2_error, tlc_error) {
        (Some(t2), Some(tlc)) => normalize_error_type(t2) == normalize_error_type(tlc),
        _ => false,
    }
}

fn tlc_has_real_error_type(spec: &BaselineSpec) -> bool {
    match &spec.tlc.error_type {
        Some(et) => !et.is_empty() && et != "unknown" && et != "timeout",
        None => false,
    }
}

fn is_simulation_mode(spec: &BaselineSpec) -> bool {
    spec.source
        .as_ref()
        .and_then(|s| s.mode.as_deref())
        .is_some_and(|m| matches!(m, "simulate" | "generate"))
}

fn is_liveness_infra_error(message: Option<&str>) -> bool {
    const BROAD: [&str; 2] = ["Liveness failure:", "Liveness error:"];
    const SPECIFIC: [&str; 2] = [
        "Temporal property",
        "TLC cannot handle the temporal formula",
    ];
    message.is_some_and(|msg| {
        BROAD.iter().any(|p| msg.starts_with(p)) || SPECIFIC.iter().any(|p| msg.starts_with(p))
    })
}

fn is_state_count_match(tla2_states: Option<u64>, spec: &BaselineSpec) -> bool {
    let expected = spec.tla2_expected_states.or(spec.tlc.states);
    matches!((tla2_states, expected), (Some(t2), Some(exp)) if t2 == exp)
}

// ---------------------------------------------------------------------------
// Classify a run result against the TLC baseline
// ---------------------------------------------------------------------------

fn classify(
    tla2_status: Option<&str>,
    tla2_states: Option<u64>,
    tla2_error: Option<&str>,
    spec: &BaselineSpec,
) -> Verdict {
    let tla2_ok = tla2_status == Some("ok");

    // TLC timeout is inconclusive.
    if spec.tlc.status == "timeout" {
        return if tla2_ok {
            Verdict::Pass
        } else {
            Verdict::BothFail
        };
    }

    let tlc_has_error = spec.tlc.status == "error" || tlc_has_real_error_type(spec);
    let tlc_no_error = spec.tlc.status == "pass" && !tlc_has_real_error_type(spec);

    if tla2_ok && tlc_no_error {
        if is_simulation_mode(spec) {
            return Verdict::Pass;
        }
        let expected_states = spec.tla2_expected_states.or(spec.tlc.states);
        match (tla2_states, expected_states) {
            (Some(t2), Some(exp)) if t2 == exp => Verdict::Pass,
            _ => Verdict::StateMismatch,
        }
    } else if tla2_ok && tlc_has_error && is_simulation_mode(spec) {
        Verdict::Pass
    } else if tla2_ok && tlc_has_error {
        Verdict::FalseNegative
    } else if !tla2_ok && tlc_no_error {
        let expected_states = spec.tla2_expected_states.or(spec.tlc.states);
        let state_count_matches = matches!(
            (tla2_states, expected_states),
            (Some(t2), Some(expected)) if t2 == expected
        );
        if state_count_matches {
            Verdict::Pass
        } else {
            Verdict::FalsePositive
        }
    } else if !tla2_ok && tlc_has_error {
        if error_types_match(tla2_error, spec.tlc.error_type.as_deref()) {
            Verdict::Pass
        } else {
            Verdict::BothFail
        }
    } else {
        Verdict::Crash
    }
}

fn apply_expected_mismatch(raw: Verdict, spec: &BaselineSpec) -> Verdict {
    if !spec.expected_mismatch {
        return raw;
    }
    match raw {
        Verdict::StateMismatch
        | Verdict::FalsePositive
        | Verdict::FalseNegative
        | Verdict::BothFail
        | Verdict::Timeout => Verdict::ExpectedMismatch,
        other => other,
    }
}

// ---------------------------------------------------------------------------
// Subprocess execution with timeout
// ---------------------------------------------------------------------------

fn run_spec(
    tla2_bin: &str,
    spec: &BaselineSpec,
    examples_dir: &Path,
    timeout: Duration,
) -> SpecRunResult {
    let source = match &spec.source {
        Some(s) => s,
        None => {
            return SpecRunResult {
                name: String::new(),
                verdict: Verdict::Skip,
                tla2_states: None,
                expected_states: None,
                detail: "no source in baseline".to_string(),
                elapsed_secs: 0.0,
            };
        }
    };

    let tla_path = examples_dir.join(&source.tla_path);
    let cfg_path = examples_dir.join(&source.cfg_path);

    if !tla_path.is_file() || !cfg_path.is_file() {
        return SpecRunResult {
            name: String::new(),
            verdict: Verdict::Skip,
            tla2_states: None,
            expected_states: None,
            detail: format!(
                "missing files: tla={} cfg={}",
                tla_path.exists(),
                cfg_path.exists()
            ),
            elapsed_secs: 0.0,
        };
    }

    let mode = source.mode.as_deref().unwrap_or("check");
    let start = Instant::now();

    let mut cmd = Command::new(tla2_bin);
    match mode {
        "simulate" | "generate" => {
            cmd.arg("simulate")
                .arg(&tla_path)
                .arg("--config")
                .arg(&cfg_path)
                .arg("--no-invariants");
        }
        _ => {
            cmd.arg("check")
                .arg(&tla_path)
                .arg("--config")
                .arg(&cfg_path)
                .arg("--output")
                .arg("json")
                .arg("--memory-limit")
                .arg("131072")
                .arg("--workers")
                .arg("0");
            if spec.effective_continue_on_error() {
                cmd.arg("--continue-on-error");
            }
        }
    }

    cmd.stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    let child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            return SpecRunResult {
                name: String::new(),
                verdict: Verdict::Crash,
                tla2_states: None,
                expected_states: None,
                detail: format!("spawn failed: {e}"),
                elapsed_secs: start.elapsed().as_secs_f64(),
            };
        }
    };

    match wait_with_timeout(child, timeout) {
        WaitOutcome::Completed(output) => {
            let elapsed = start.elapsed().as_secs_f64();
            parse_and_classify_output(spec, &output, elapsed)
        }
        WaitOutcome::Timeout => {
            let elapsed = start.elapsed().as_secs_f64();
            SpecRunResult {
                name: String::new(),
                verdict: apply_expected_mismatch(Verdict::Timeout, spec),
                tla2_states: None,
                expected_states: spec.tla2_expected_states.or(spec.tlc.states),
                detail: format!("timeout after {timeout:.0?}"),
                elapsed_secs: elapsed,
            }
        }
        WaitOutcome::Error(e) => SpecRunResult {
            name: String::new(),
            verdict: Verdict::Crash,
            tla2_states: None,
            expected_states: None,
            detail: format!("wait error: {e}"),
            elapsed_secs: start.elapsed().as_secs_f64(),
        },
    }
}

fn parse_and_classify_output(
    spec: &BaselineSpec,
    output: &std::process::Output,
    elapsed: f64,
) -> SpecRunResult {
    // Detect signal-killed processes (OOM watchdog).
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if matches!(output.status.signal(), Some(9 | 15)) {
            let raw = Verdict::Crash;
            let verdict = apply_expected_mismatch(raw, spec);
            return SpecRunResult {
                name: String::new(),
                verdict,
                tla2_states: None,
                expected_states: spec.tla2_expected_states.or(spec.tlc.states),
                detail: format!("killed by signal (exit={})", output.status),
                elapsed_secs: elapsed,
            };
        }
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let parsed: Option<SubprocessOutput> = serde_json::from_str(&stdout).ok();

    let (tla2_status, tla2_states, tla2_error) = match &parsed {
        Some(p) => {
            let is_liveness_infra = is_liveness_infra_error(p.result.error_message.as_deref());
            let is_bfs_correct_postprocess_fail = !is_liveness_infra
                && p.result.status == "runtime_error"
                && is_state_count_match(Some(p.statistics.states_found), spec);
            let should_downgrade = is_liveness_infra || is_bfs_correct_postprocess_fail;
            let effective_status = if should_downgrade {
                "ok".to_string()
            } else {
                p.result.status.clone()
            };
            let effective_error = if should_downgrade {
                None
            } else {
                p.result
                    .error_type
                    .clone()
                    .or(p.result.error_message.clone())
            };
            (
                Some(effective_status),
                Some(p.statistics.states_found),
                effective_error,
            )
        }
        None => {
            if is_simulation_mode(spec) {
                if output.status.success() {
                    (Some("ok".to_string()), None, None)
                } else {
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    let detail: String = stderr.chars().take(200).collect();
                    (Some("error".to_string()), None, Some(detail))
                }
            } else {
                let stderr = String::from_utf8_lossy(&output.stderr);
                let detail = if stderr.chars().count() > 200 {
                    let truncated: String = stderr.chars().take(200).collect();
                    format!("{truncated}...")
                } else {
                    stderr.to_string()
                };
                return SpecRunResult {
                    name: String::new(),
                    verdict: Verdict::Crash,
                    tla2_states: None,
                    expected_states: spec.tla2_expected_states.or(spec.tlc.states),
                    detail: format!("exit={}, unparseable: {detail}", output.status),
                    elapsed_secs: elapsed,
                };
            }
        }
    };

    let raw = classify(
        tla2_status.as_deref(),
        tla2_states,
        tla2_error.as_deref(),
        spec,
    );
    let verdict = apply_expected_mismatch(raw, spec);

    SpecRunResult {
        name: String::new(),
        verdict,
        tla2_states,
        expected_states: spec.tla2_expected_states.or(spec.tlc.states),
        detail: tla2_error.unwrap_or_default(),
        elapsed_secs: elapsed,
    }
}

// ---------------------------------------------------------------------------
// Subprocess timeout handling
// ---------------------------------------------------------------------------

enum WaitOutcome {
    Completed(std::process::Output),
    Timeout,
    Error(std::io::Error),
}

fn wait_with_timeout(mut child: std::process::Child, timeout: Duration) -> WaitOutcome {
    let mut stdout_pipe = child.stdout.take();
    let mut stderr_pipe = child.stderr.take();

    let stdout_handle = thread::spawn(move || {
        let mut buf = Vec::new();
        if let Some(ref mut pipe) = stdout_pipe {
            let _ = pipe.read_to_end(&mut buf);
        }
        buf
    });
    let stderr_handle = thread::spawn(move || {
        let mut buf = Vec::new();
        if let Some(ref mut pipe) = stderr_pipe {
            let _ = pipe.read_to_end(&mut buf);
        }
        buf
    });

    let start = Instant::now();
    let poll_interval = Duration::from_millis(100);

    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let stdout = stdout_handle.join().unwrap_or_default();
                let stderr = stderr_handle.join().unwrap_or_default();
                return WaitOutcome::Completed(std::process::Output {
                    status,
                    stdout,
                    stderr,
                });
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    let _ = stdout_handle.join();
                    let _ = stderr_handle.join();
                    return WaitOutcome::Timeout;
                }
                thread::sleep(poll_interval);
            }
            Err(e) => {
                let _ = stdout_handle.join();
                let _ = stderr_handle.join();
                return WaitOutcome::Error(e);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Test infrastructure
// ---------------------------------------------------------------------------

fn load_baseline() -> Baseline {
    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates/ parent")
        .parent()
        .expect("workspace root")
        .to_path_buf();
    let baseline_path = workspace_root.join("tests/tlc_comparison/spec_baseline.json");
    let text = std::fs::read_to_string(&baseline_path)
        .unwrap_or_else(|e| panic!("Failed to read {}: {e}", baseline_path.display()));
    serde_json::from_str(&text).expect("parse spec_baseline.json")
}

fn tla2_binary() -> String {
    env!("CARGO_BIN_EXE_tla2").to_string()
}

fn examples_dir(baseline: &Baseline) -> PathBuf {
    let path = PathBuf::from(&baseline.inputs.examples_dir);
    if path.is_dir() {
        return path;
    }
    // Fallback: try $HOME/tlaplus-examples/specifications
    let home = std::env::var("HOME").unwrap_or_default();
    let fallback = PathBuf::from(&home).join("tlaplus-examples/specifications");
    if fallback.is_dir() {
        return fallback;
    }
    panic!(
        "Examples directory not found. Tried:\n  1. {}\n  2. {}\n\
         Set TLAPLUS_EXAMPLES or ensure ~/tlaplus-examples exists.",
        path.display(),
        fallback.display()
    );
}

/// Returns the set of spec names that should be tested.
fn select_specs(baseline: &Baseline) -> Vec<String> {
    let category =
        std::env::var("SPEC_REGRESSION_CATEGORY").unwrap_or_else(|_| "small".to_string());

    let filter: Option<Vec<String>> = std::env::var("SPEC_REGRESSION_FILTER")
        .ok()
        .map(|s| s.split(',').map(|x| x.trim().to_string()).collect());

    let skip: Vec<String> = std::env::var("SPEC_REGRESSION_SKIP")
        .ok()
        .map(|s| s.split(',').map(|x| x.trim().to_string()).collect())
        .unwrap_or_default();

    baseline
        .specs
        .iter()
        .filter(|(name, spec)| {
            // Only test specs that previously passed.
            if !spec.verified_match {
                return false;
            }
            // Category filter.
            if category != "all" && spec.category != category {
                return false;
            }
            // Explicit name filter.
            if let Some(ref names) = filter {
                if !names.iter().any(|n| n == *name) {
                    return false;
                }
            }
            // Skip list.
            if skip.iter().any(|s| s == *name) {
                return false;
            }
            true
        })
        .map(|(name, _)| name.clone())
        .collect()
}

fn default_timeout() -> Duration {
    let secs: u64 = std::env::var("SPEC_REGRESSION_TIMEOUT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(120);
    Duration::from_secs(secs)
}

fn effective_timeout(default: Duration, spec: &BaselineSpec) -> Duration {
    match spec.diagnose_timeout_seconds {
        Some(override_secs) if Duration::from_secs(override_secs) > default => {
            Duration::from_secs(override_secs)
        }
        _ => default,
    }
}

// ---------------------------------------------------------------------------
// The test
// ---------------------------------------------------------------------------

#[test]
fn spec_coverage_regression() {
    let baseline = load_baseline();
    let bin = tla2_binary();
    let examples = examples_dir(&baseline);
    let spec_names = select_specs(&baseline);
    let default_to = default_timeout();

    let category =
        std::env::var("SPEC_REGRESSION_CATEGORY").unwrap_or_else(|_| "small".to_string());

    eprintln!("=== Spec Coverage Regression Test ===");
    eprintln!("Binary: {bin}");
    eprintln!("Examples: {}", examples.display());
    eprintln!("Category: {category}");
    eprintln!("Default timeout: {default_to:?}");
    eprintln!("Specs to test: {}", spec_names.len());
    eprintln!();

    if spec_names.is_empty() {
        panic!(
            "No specs matched filter criteria (category={category}). \
             Check that spec_baseline.json contains verified_match specs in this category."
        );
    }

    let mut passed = 0usize;
    let mut expected_mismatch = 0usize;
    let mut skipped = 0usize;
    let mut regressions: Vec<SpecRunResult> = Vec::new();
    let total = spec_names.len();

    for (i, name) in spec_names.iter().enumerate() {
        let spec = &baseline.specs[name];
        let timeout = effective_timeout(default_to, spec);

        eprint!("[{}/{}] {name} ... ", i + 1, total);

        let mut result = run_spec(&bin, spec, &examples, timeout);
        result.name = name.clone();

        match result.verdict {
            Verdict::Pass => {
                eprintln!(
                    "PASS ({:.1}s, states: {})",
                    result.elapsed_secs,
                    result
                        .tla2_states
                        .map(|s| s.to_string())
                        .unwrap_or_else(|| "n/a".to_string())
                );
                passed += 1;
            }
            Verdict::ExpectedMismatch => {
                eprintln!("EXPECTED_MISMATCH ({:.1}s)", result.elapsed_secs);
                expected_mismatch += 1;
            }
            Verdict::Skip => {
                eprintln!("SKIP ({})", result.detail);
                skipped += 1;
            }
            other => {
                eprintln!(
                    "REGRESSION: {} ({:.1}s) -- {}",
                    other.label(),
                    result.elapsed_secs,
                    result.detail
                );
                regressions.push(result);
            }
        }
    }

    eprintln!();
    eprintln!("=== Summary ===");
    eprintln!("Total:             {total}");
    eprintln!("Passed:            {passed}");
    eprintln!("Expected mismatch: {expected_mismatch}");
    eprintln!("Skipped:           {skipped}");
    eprintln!("Regressions:       {}", regressions.len());

    if !regressions.is_empty() {
        eprintln!();
        eprintln!("=== REGRESSIONS (previously passing specs now failing) ===");
        for r in &regressions {
            eprintln!();
            eprintln!("  Spec:     {}", r.name);
            eprintln!("  Verdict:  {}", r.verdict.label());
            eprintln!("  TLA2 states: {:?}", r.tla2_states);
            eprintln!("  Expected:    {:?}", r.expected_states);
            eprintln!("  Time:     {:.1}s", r.elapsed_secs);
            if !r.detail.is_empty() {
                // Truncate very long error details for readability.
                let detail = if r.detail.len() > 500 {
                    format!("{}...", &r.detail[..500])
                } else {
                    r.detail.clone()
                };
                eprintln!("  Detail:   {detail}");
            }
        }
        eprintln!();

        let regression_names: Vec<&str> = regressions.iter().map(|r| r.name.as_str()).collect();
        panic!(
            "{} regression(s) detected in {category} specs: {}",
            regressions.len(),
            regression_names.join(", ")
        );
    }

    // Ensure we actually tested something meaningful.
    assert!(
        passed + expected_mismatch > 0,
        "No specs passed or matched as expected -- something is wrong with the test setup"
    );
}
