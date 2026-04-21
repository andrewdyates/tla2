// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Output formatting for the `diagnose` subcommand: human-readable and JSON.

use std::collections::BTreeMap;
use std::path::Path;

use anyhow::{Context, Result};

use super::types::*;

/// Print human-readable summary to stdout.
pub(super) fn emit_human(
    results: &[SpecResult],
    tally: &Tally,
    total_baseline: usize,
    baseline_path: &Path,
    exe: &Path,
) {
    // CLI tool — println! is the correct output method.
    println!("============================================================");
    println!("SUMMARY");
    println!("============================================================");
    println!(
        "{}      {:>4}  ({:.1}%)",
        pass_summary_label(),
        tally.pass,
        tally.coverage * 100.0
    );
    if tally.expected_mismatch > 0 {
        println!("EXPECTED MISMATCH:       {:>4}", tally.expected_mismatch);
    }
    if tally.flaky_timeout > 0 {
        println!(
            "FLAKY TIMEOUT:           {:>4}  (passed on retry)",
            tally.flaky_timeout
        );
    }
    if tally.mismatch > 0 {
        println!("STATE COUNT MISMATCH:    {:>4}", tally.mismatch);
    }
    if tally.false_pos > 0 {
        println!(
            "FALSE POSITIVE:          {:>4}  (TLA2 error, TLC pass)",
            tally.false_pos
        );
    }
    if tally.false_neg > 0 {
        println!(
            "FALSE NEGATIVE:          {:>4}  (TLC error, TLA2 pass)",
            tally.false_neg
        );
    }
    if tally.crash > 0 {
        println!("CRASH:                   {:>4}", tally.crash);
    }
    if tally.oom_killed > 0 {
        println!(
            "OOM KILLED:              {:>4}  (signal killed)",
            tally.oom_killed
        );
    }
    if tally.timeout > 0 {
        println!("TIMEOUT:                 {:>4}", tally.timeout);
    }
    if tally.skip > 0 {
        println!("SKIP (files missing):    {:>4}", tally.skip);
    }
    if tally.both_fail > 0 {
        println!("BOTH FAIL:               {:>4}", tally.both_fail);
    }
    println!();
    println!(
        "Baseline: {} ({} specs)",
        baseline_path.display(),
        total_baseline
    );
    println!("Binary: {}", exe.display());

    print_detail_section(
        "STATE COUNT MISMATCHES",
        SpecVerdict::StateMismatch,
        results,
    );
    print_detail_section(
        "EXPECTED MISMATCHES",
        SpecVerdict::ExpectedMismatch,
        results,
    );
    print_detail_section(
        "FALSE POSITIVES (TLA2 reports error, TLC passes)",
        SpecVerdict::FalsePositive,
        results,
    );
    print_detail_section(
        "FALSE NEGATIVES (TLC reports error, TLA2 passes)",
        SpecVerdict::FalseNegative,
        results,
    );
    print_detail_section("CRASHES", SpecVerdict::Crash, results);
    print_detail_section(
        "OOM KILLED (signal killed by memory watchdog)",
        SpecVerdict::OomKilled,
        results,
    );
    print_detail_section("TIMEOUTS", SpecVerdict::Timeout, results);
    print_detail_section(
        "FLAKY TIMEOUTS (passed on retry)",
        SpecVerdict::FlakyTimeout,
        results,
    );
    print_detail_section("BOTH FAIL", SpecVerdict::BothFail, results);
}

fn pass_summary_label() -> &'static str {
    "PASS (baseline match):"
}

/// Print JSON report to stdout.
pub(super) fn emit_json(
    results: &[SpecResult],
    tally: &Tally,
    total_baseline: usize,
    total_to_run: usize,
    exe: &Path,
    run_conditions: RunConditions,
) -> Result<()> {
    let report = build_json_report(
        results,
        tally,
        total_baseline,
        total_to_run,
        exe,
        run_conditions,
    );
    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}

/// Write metrics JSON report to a file.
pub(super) fn emit_metrics_file(
    results: &[SpecResult],
    tally: &Tally,
    total_baseline: usize,
    total_to_run: usize,
    exe: &Path,
    run_conditions: RunConditions,
    path: &Path,
) -> Result<()> {
    let report = build_json_report(
        results,
        tally,
        total_baseline,
        total_to_run,
        exe,
        run_conditions,
    );
    let json = serde_json::to_string_pretty(&report)?;
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .with_context(|| format!("create directory {}", parent.display()))?;
    }
    std::fs::write(path, format!("{json}\n"))
        .with_context(|| format!("write metrics to {}", path.display()))?;
    println!("Metrics written to: {}", path.display());
    Ok(())
}

fn build_json_report(
    results: &[SpecResult],
    tally: &Tally,
    total_baseline: usize,
    total_to_run: usize,
    exe: &Path,
    run_conditions: RunConditions,
) -> JsonReport {
    let git_commit = option_env!("TLA2_GIT_COMMIT")
        .unwrap_or("unknown")
        .to_string();
    let build_timestamp = exe_mtime(exe);

    let mut json_specs = BTreeMap::new();
    for r in results {
        json_specs.insert(
            r.name.clone(),
            JsonSpecResult {
                status: r.verdict.label().to_string(),
                tla2_states: r.tla2_states,
                tlc_states: r.tlc_states,
                tla2_error: if matches!(
                    r.verdict,
                    SpecVerdict::Crash | SpecVerdict::OomKilled | SpecVerdict::FlakyTimeout
                ) {
                    // For crashes/oom/flaky, error_details has diagnostic info, not an error type.
                    None
                } else {
                    r.error_details.clone()
                },
                tlc_error_type: r.tlc_error_type.clone(),
                error_details: if matches!(
                    r.verdict,
                    SpecVerdict::Crash | SpecVerdict::OomKilled | SpecVerdict::FlakyTimeout
                ) {
                    r.error_details.clone()
                } else {
                    None
                },
                expected_mismatch_reason: r.expected_mismatch_reason.clone(),
                time_seconds: r.time_seconds,
                timeout_seconds: r.timeout_seconds,
                timeout_source: r.timeout_source,
            },
        );
    }

    JsonReport {
        schema_version: 7,
        generated_at: chrono::Utc::now().to_rfc3339(),
        binary_info: BinaryInfo {
            path: exe.display().to_string(),
            git_commit,
            build_timestamp,
        },
        run_conditions,
        summary: JsonSummary {
            total_specs: total_baseline,
            specs_ran: total_to_run,
            pass: tally.pass,
            coverage: (tally.coverage * 10000.0).round() / 10000.0,
            expected_mismatch: tally.expected_mismatch,
            state_mismatch: tally.mismatch,
            false_positive: tally.false_pos,
            false_negative: tally.false_neg,
            crash: tally.crash,
            oom_killed: tally.oom_killed,
            timeout: tally.timeout,
            flaky_timeout: tally.flaky_timeout,
            skip: tally.skip,
            both_fail: tally.both_fail,
        },
        specs: json_specs,
    }
}

fn print_detail_section(header: &str, verdict: SpecVerdict, results: &[SpecResult]) {
    let matching: Vec<&SpecResult> = results.iter().filter(|r| r.verdict == verdict).collect();
    if matching.is_empty() {
        return;
    }
    println!();
    println!("{}:", header);
    for r in &matching {
        print_result_detail(verdict, r);
    }
}

fn exe_mtime(path: &Path) -> Option<String> {
    let meta = std::fs::metadata(path).ok()?;
    let modified = meta.modified().ok()?;
    let datetime: chrono::DateTime<chrono::Utc> = modified.into();
    Some(datetime.to_rfc3339())
}

#[cfg(test)]
mod tests {
    use super::pass_summary_label;

    #[test]
    fn test_pass_summary_label_describes_baseline_contract() {
        assert_eq!(pass_summary_label(), "PASS (baseline match):");
    }
}

#[cfg(test)]
#[path = "output_tests.rs"]
mod output_tests;

fn print_result_detail(verdict: SpecVerdict, result: &SpecResult) {
    match verdict {
        SpecVerdict::ExpectedMismatch => print_expected_mismatch_detail(result),
        SpecVerdict::StateMismatch => print_state_mismatch_detail(result),
        SpecVerdict::FalsePositive | SpecVerdict::FalseNegative => {
            print_boolean_mismatch_detail(result)
        }
        SpecVerdict::BothFail => print_both_fail_detail(result),
        _ => print_default_detail(result),
    }
}

fn print_expected_mismatch_detail(result: &SpecResult) {
    println!(
        "  {}: TLA2={} TLC={}",
        result.name,
        result.tla2_status.as_deref().unwrap_or("?"),
        result.tlc_status,
    );
    if let Some(reason) = result.expected_mismatch_reason.as_deref() {
        println!("    reason: {reason}");
    }
}

fn print_state_mismatch_detail(result: &SpecResult) {
    println!(
        "  {}: TLA2={} TLC={}",
        result.name,
        result
            .tla2_states
            .map(|n| n.to_string())
            .unwrap_or_else(|| "?".to_string()),
        result
            .tlc_states
            .map(|n| n.to_string())
            .unwrap_or_else(|| "?".to_string()),
    );
}

fn print_boolean_mismatch_detail(result: &SpecResult) {
    println!(
        "  {}: TLA2={} TLC={} ({})",
        result.name,
        result.tla2_status.as_deref().unwrap_or("?"),
        result.tlc_status,
        result.error_details.as_deref().unwrap_or(""),
    );
}

fn print_both_fail_detail(result: &SpecResult) {
    println!(
        "  {}: TLA2={}, TLC={}",
        result.name,
        result.error_details.as_deref().unwrap_or("error"),
        result.tlc_error_type.as_deref().unwrap_or("error"),
    );
}

fn print_default_detail(result: &SpecResult) {
    if let Some(ref detail) = result.error_details {
        println!("  {}: {}", result.name, detail);
    } else {
        println!("  {}", result.name);
    }
}
