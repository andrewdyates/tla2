// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `diagnose` subcommand: spec coverage analysis against the TLC baseline.
//!
//! Tests the current binary against known TLC results from `spec_baseline.json`.
//! The binary tests itself via `std::env::current_exe()`, so the binary being
//! measured is always the binary doing the measuring.

mod baseline_update;
mod output;
mod runner;
mod types;

use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

use crate::cli_schema::{DiagnoseArgs, DiagnoseOutputFormat};
use anyhow::{bail, Context, Result};
use runner::{run_one_spec, Semaphore};
use types::{Baseline, DiagnoseCheckPolicy, RunConditions, SpecResult, Tally, TimeoutSource};

pub(crate) fn cmd_diagnose(mut args: DiagnoseArgs) -> Result<()> {
    if args.parallel == 0 {
        bail!("--parallel must be >= 1");
    }

    // Load --spec-list file into args.spec if provided.
    if let Some(ref list_path) = args.spec_list {
        let content = std::fs::read_to_string(list_path)
            .with_context(|| format!("read spec list {}", list_path.display()))?;
        for line in content.lines() {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            args.spec.push(trimmed.to_string());
        }
        if args.spec.is_empty() {
            bail!(
                "spec list file {} contains no spec names",
                list_path.display()
            );
        }
    }

    let baseline_path = &args.baseline;
    let baseline_text = std::fs::read_to_string(baseline_path)
        .with_context(|| format!("read baseline {}", baseline_path.display()))?;
    let baseline: Baseline =
        serde_json::from_str(&baseline_text).context("parse spec_baseline.json")?;

    let examples_dir = match &args.examples_dir {
        Some(d) => d.clone(),
        None => PathBuf::from(&baseline.inputs.examples_dir),
    };
    if !examples_dir.is_dir() {
        bail!(
            "examples directory not found: {}\nUse --examples-dir to override.",
            examples_dir.display()
        );
    }

    let exe = std::env::current_exe().context("resolve current exe path")?;
    let spec_names = filter_specs(&baseline, &args);
    let total_baseline = baseline.specs.len();
    let total_to_run = spec_names.len();

    if total_to_run == 0 {
        bail!("no specs matched the filter criteria");
    }

    let checker_policy = DiagnoseCheckPolicy::from_checker_workers(args.checker_workers);
    let run_conditions = capture_run_conditions(args.timeout, args.retries, checker_policy);
    let fail_on_mismatch = args.fail_on_mismatch;
    let fail_on_non_pass = args.fail_on_non_pass;
    let output_metrics_path = args.output_metrics.clone();

    if matches!(args.output, DiagnoseOutputFormat::Human) {
        // CLI tool — eprintln is the correct progress output method.
        eprintln!(
            "TLA2 diagnose: {} specs to test (of {} in baseline)",
            total_to_run, total_baseline
        );
        eprintln!("Binary: {}", exe.display());
        eprintln!("Examples: {}", examples_dir.display());
        eprintln!("Timeout default: {}s", args.timeout);
        eprintln!("Checker policy: {}", checker_policy.human_description());
        // Show per-spec overrides from baseline.
        let overrides: Vec<(&str, u64)> = spec_names
            .iter()
            .filter_map(|name| {
                baseline
                    .specs
                    .get(name)?
                    .diagnose_timeout_seconds
                    .filter(|&t| t > args.timeout)
                    .map(|t| (name.as_str(), t))
            })
            .collect();
        if !overrides.is_empty() {
            eprintln!("Per-spec timeout overrides:");
            for (name, secs) in &overrides {
                eprintln!("  {} => {}s (baseline)", name, secs);
            }
        }
        // Part of #3236: show specs running in first-error mode.
        let first_error_specs: Vec<&str> = spec_names
            .iter()
            .filter_map(|name| {
                let spec = baseline.specs.get(name)?;
                if !spec.effective_continue_on_error() {
                    Some(name.as_str())
                } else {
                    None
                }
            })
            .collect();
        if !first_error_specs.is_empty() {
            eprintln!("First-error mode (no --continue-on-error):");
            for name in &first_error_specs {
                eprintln!("  {}", name);
            }
        }
        if args.retries > 0 {
            eprintln!("Retries: {} (timeout specs retried)", args.retries);
        }
        if args.parallel > 1 {
            eprintln!("Parallel: {} concurrent", args.parallel);
        }
        eprintln!(
            "Load: {:.2} / {:.2} / {:.2} ({} CPUs)",
            run_conditions.load_avg_1m,
            run_conditions.load_avg_5m,
            run_conditions.load_avg_15m,
            run_conditions.cpu_count,
        );
        eprintln!();
    }

    let results = run_all_specs(
        &spec_names,
        &baseline,
        &exe,
        &examples_dir,
        args.timeout,
        checker_policy,
        &args,
    );
    let tally = Tally::from_results(&results, total_baseline);

    match args.output {
        DiagnoseOutputFormat::Human => {
            output::emit_human(&results, &tally, total_baseline, baseline_path, &exe);
        }
        DiagnoseOutputFormat::Json => {
            output::emit_json(
                &results,
                &tally,
                total_baseline,
                total_to_run,
                &exe,
                run_conditions.clone(),
            )?;
        }
    }

    if let Some(ref metrics_path) = output_metrics_path {
        output::emit_metrics_file(
            &results,
            &tally,
            total_baseline,
            total_to_run,
            &exe,
            run_conditions,
            metrics_path,
        )?;
    }

    if args.update_baseline {
        baseline_update::update_baseline_file(baseline_path, &baseline_text, &results)?;
        eprintln!("Updated baseline: {}", baseline_path.display());
    }

    // --fail-on-mismatch / --fail-on-non-pass exit logic.
    // FlakyTimeout and Skip do NOT trigger failure.
    if fail_on_non_pass {
        let failing = results.iter().any(|r| {
            !matches!(
                r.verdict,
                types::SpecVerdict::Pass
                    | types::SpecVerdict::FlakyTimeout
                    | types::SpecVerdict::Skip
            )
        });
        if failing {
            std::process::exit(1);
        }
    } else if fail_on_mismatch {
        let has_mismatch = results
            .iter()
            .any(|r| r.verdict == types::SpecVerdict::StateMismatch);
        if has_mismatch {
            std::process::exit(1);
        }
    }

    Ok(())
}

fn filter_specs(baseline: &Baseline, args: &DiagnoseArgs) -> Vec<String> {
    baseline
        .specs
        .keys()
        .filter(|name| {
            if !args.spec.is_empty() {
                return args.spec.iter().any(|s| s == *name);
            }
            if let Some(ref cat) = args.category {
                if let Some(spec) = baseline.specs.get(*name) {
                    return spec.category == *cat;
                }
            }
            true
        })
        .cloned()
        .collect()
}

/// Compute the effective timeout for a spec: `max(cli_default, baseline_override)`.
///
/// Per-spec `diagnose_timeout_seconds` in the baseline extends the timeout for
/// slow specs beyond the CLI default. This ensures large specs that need more
/// time than the default are not prematurely killed. The CLI `--timeout` sets
/// the default for specs without an override.
fn effective_timeout(
    cli_default: u64,
    spec: &types::BaselineSpec,
) -> (Duration, u64, TimeoutSource) {
    match spec.diagnose_timeout_seconds {
        Some(override_secs) if override_secs > cli_default => (
            Duration::from_secs(override_secs),
            override_secs,
            TimeoutSource::Baseline,
        ),
        _ => (
            Duration::from_secs(cli_default),
            cli_default,
            TimeoutSource::Cli,
        ),
    }
}

fn run_all_specs(
    spec_names: &[String],
    baseline: &Baseline,
    exe: &std::path::Path,
    examples_dir: &std::path::Path,
    cli_timeout_default: u64,
    checker_policy: DiagnoseCheckPolicy,
    args: &DiagnoseArgs,
) -> Vec<SpecResult> {
    let done_count = AtomicUsize::new(0);
    let total = spec_names.len();
    let retries = args.retries;

    if args.parallel <= 1 {
        spec_names
            .iter()
            .map(|name| {
                let spec = &baseline.specs[name];
                let (timeout, timeout_secs, timeout_src) =
                    effective_timeout(cli_timeout_default, spec);
                let mut r = run_one_spec(
                    name,
                    spec,
                    exe,
                    examples_dir,
                    timeout,
                    retries,
                    checker_policy,
                );
                r.timeout_seconds = timeout_secs;
                r.timeout_source = timeout_src;
                let done = done_count.fetch_add(1, Ordering::Relaxed) + 1;
                if matches!(args.output, DiagnoseOutputFormat::Human) {
                    eprint!(
                        "\r[{}/{}] {} => {}     ",
                        done,
                        total,
                        name,
                        r.verdict.label()
                    );
                    let _ = std::io::stderr().flush();
                }
                r
            })
            .collect()
    } else {
        let results = std::sync::Mutex::new(Vec::with_capacity(total));
        let semaphore = Semaphore::new(args.parallel);
        std::thread::scope(|s| {
            for name in spec_names {
                let spec = &baseline.specs[name];
                let (timeout, timeout_secs, timeout_src) =
                    effective_timeout(cli_timeout_default, spec);
                let semaphore = &semaphore;
                let done_count = &done_count;
                let results = &results;
                let output_fmt = args.output;
                s.spawn(move || {
                    let _permit = semaphore.acquire();
                    let mut r = run_one_spec(
                        name,
                        spec,
                        exe,
                        examples_dir,
                        timeout,
                        retries,
                        checker_policy,
                    );
                    r.timeout_seconds = timeout_secs;
                    r.timeout_source = timeout_src;
                    let done = done_count.fetch_add(1, Ordering::Relaxed) + 1;
                    if matches!(output_fmt, DiagnoseOutputFormat::Human) {
                        eprint!(
                            "\r[{}/{}] {} => {}     ",
                            done,
                            total,
                            name,
                            r.verdict.label()
                        );
                        let _ = std::io::stderr().flush();
                    }
                    results.lock().expect("results lock poisoned").push(r);
                });
            }
        });
        let mut out = results.into_inner().expect("results lock poisoned");
        out.sort_by(|a, b| {
            spec_names
                .iter()
                .position(|n| *n == a.name)
                .cmp(&spec_names.iter().position(|n| *n == b.name))
        });
        if matches!(args.output, DiagnoseOutputFormat::Human) {
            eprintln!();
        }
        out
    }
}

fn capture_run_conditions(
    timeout_seconds: u64,
    retries: u32,
    checker_policy: DiagnoseCheckPolicy,
) -> RunConditions {
    let (load_1, load_5, load_15) = get_load_avg();
    RunConditions {
        cpu_count: std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1),
        load_avg_1m: load_1,
        load_avg_5m: load_5,
        load_avg_15m: load_15,
        timeout_floor_seconds: timeout_seconds,
        timeout_seconds,
        retries,
        checker_policy: checker_policy.label(),
        checker_workers: checker_policy.checker_workers(),
    }
}

#[cfg(unix)]
fn get_load_avg() -> (f64, f64, f64) {
    // SAFETY: libc::getloadavg writes into a caller-provided buffer of known size.
    // The buffer is stack-allocated with exactly 3 elements, matching the count argument.
    let mut loads = [0.0f64; 3];
    let ret = unsafe { libc::getloadavg(loads.as_mut_ptr(), 3) };
    if ret == 3 {
        (loads[0], loads[1], loads[2])
    } else {
        (0.0, 0.0, 0.0)
    }
}

#[cfg(not(unix))]
fn get_load_avg() -> (f64, f64, f64) {
    (0.0, 0.0, 0.0)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_spec(timeout_override: Option<u64>) -> types::BaselineSpec {
        types::BaselineSpec {
            tlc: types::BaselineTlc {
                status: "pass".to_string(),
                states: Some(10),
                error_type: None,
            },
            tla2: types::BaselineTla2 {
                status: "untested".to_string(),
                states: None,
                error_type: None,
                last_run: None,
                git_commit: None,
            },
            verified_match: false,
            category: "small".to_string(),
            source: None,
            expected_mismatch: false,
            expected_mismatch_reason: None,
            tla2_expected_states: None,
            diagnose_timeout_seconds: timeout_override,
            continue_on_error: true,
        }
    }

    #[test]
    fn test_effective_timeout_no_override_uses_cli_default() {
        let spec = make_spec(None);
        let (dur, secs, src) = effective_timeout(120, &spec);
        assert_eq!(dur, Duration::from_secs(120));
        assert_eq!(secs, 120);
        assert_eq!(src, types::TimeoutSource::Cli);
    }

    #[test]
    fn test_effective_timeout_override_above_default_uses_baseline() {
        // Part of #3741: override 450 > default 120 → baseline wins (extends timeout).
        let spec = make_spec(Some(450));
        let (dur, secs, src) = effective_timeout(120, &spec);
        assert_eq!(dur, Duration::from_secs(450));
        assert_eq!(secs, 450);
        assert_eq!(src, types::TimeoutSource::Baseline);
    }

    #[test]
    fn test_effective_timeout_override_at_default_uses_cli() {
        let spec = make_spec(Some(120));
        let (dur, secs, src) = effective_timeout(120, &spec);
        assert_eq!(dur, Duration::from_secs(120));
        assert_eq!(secs, 120);
        assert_eq!(src, types::TimeoutSource::Cli);
    }

    #[test]
    fn test_effective_timeout_override_below_default_uses_cli() {
        // Part of #3741: override 60 < default 120 → CLI default wins (no shrinking).
        let spec = make_spec(Some(60));
        let (dur, secs, src) = effective_timeout(120, &spec);
        assert_eq!(dur, Duration::from_secs(120));
        assert_eq!(secs, 120);
        assert_eq!(src, types::TimeoutSource::Cli);
    }
}
