// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `bench` subcommand: benchmark TLA+ specs with precise timing and baseline comparison.
//!
//! Runs specs through the model checker as subprocesses, captures timing and state counts
//! from JSON output, and optionally compares against TLC baselines or saved benchmark data.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};

use crate::cli_schema::BenchOutputFormat;

// ── Configuration ────────────────────────────────────────────────────────────

/// Configuration for the bench subcommand, built from CLI args.
pub(crate) struct BenchConfig {
    pub files: Vec<PathBuf>,
    pub config: Option<PathBuf>,
    pub iterations: usize,
    pub workers: usize,
    pub baseline: Option<PathBuf>,
    pub save_baseline: Option<PathBuf>,
    pub format: BenchOutputFormat,
}

// ── Result types ─────────────────────────────────────────────────────────────

/// Status of a single benchmark run.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum BenchStatus {
    Pass,
    Fail,
    Timeout,
    Error,
}

impl std::fmt::Display for BenchStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Pass => write!(f, "pass"),
            Self::Fail => write!(f, "FAIL"),
            Self::Timeout => write!(f, "TIMEOUT"),
            Self::Error => write!(f, "ERROR"),
        }
    }
}

/// Result of benchmarking a single spec (possibly averaged over multiple iterations).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct BenchResult {
    pub spec_name: String,
    pub states_found: u64,
    pub distinct_states: u64,
    pub wall_time_ms: u64,
    pub states_per_sec: f64,
    pub peak_memory_mb: Option<f64>,
    pub status: BenchStatus,
    /// Individual iteration wall times in milliseconds (for statistical analysis).
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub iteration_times_ms: Vec<u64>,
    /// Number of worker threads used.
    pub workers: usize,
    /// Comparison against baseline, if available.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub vs_baseline: Option<BaselineComparison>,
}

/// Comparison of a bench result against a baseline entry.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct BaselineComparison {
    /// Baseline wall time in milliseconds.
    pub baseline_time_ms: u64,
    /// Speedup ratio (baseline / current). >1.0 means current is faster.
    pub speedup: f64,
    /// Whether state counts match the baseline.
    pub states_match: bool,
}

/// Saved benchmark baseline: a collection of results keyed by spec name.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct BenchBaseline {
    /// ISO 8601 timestamp of when the baseline was captured.
    pub timestamp: String,
    /// Git commit hash at time of capture (if available).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub commit: Option<String>,
    /// Per-spec benchmark results.
    pub specs: BTreeMap<String, BenchBaselineEntry>,
}

/// A single entry in the saved benchmark baseline.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct BenchBaselineEntry {
    pub states_found: u64,
    pub distinct_states: u64,
    pub wall_time_ms: u64,
    pub states_per_sec: f64,
    pub workers: usize,
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
}

#[derive(Deserialize)]
struct CheckJsonStats {
    states_found: u64,
    #[serde(default)]
    states_distinct: Option<u64>,
    #[serde(default)]
    states_per_second: Option<f64>,
    #[serde(default)]
    memory_mb: Option<f64>,
}

// ── Spec baseline format (same schema as spec_baseline.json used by diagnose) ─

#[derive(Deserialize)]
struct SpecBaseline {
    specs: BTreeMap<String, SpecBaselineEntry>,
}

/// Partial deserialization of a spec_baseline.json entry. Only fields used
/// for comparison are kept; unknown fields are silently ignored by serde.
#[derive(Deserialize)]
struct SpecBaselineEntry {
    tlc: SpecBaselineTlc,
}

#[derive(Deserialize)]
struct SpecBaselineTlc {
    #[serde(default)]
    states: Option<u64>,
    #[serde(default)]
    time_seconds: Option<f64>,
}

// ── Entry point ──────────────────────────────────────────────────────────────

pub(crate) fn cmd_bench(config: BenchConfig) -> Result<()> {
    if config.iterations == 0 {
        bail!("--iterations must be >= 1");
    }

    let exe = std::env::current_exe().context("resolve current exe path")?;
    let mut spec_files = collect_spec_files(&config.files)?;

    // If --config is provided for a single-spec benchmark, override the .cfg path.
    if let Some(ref cfg_override) = config.config {
        if spec_files.len() == 1 {
            spec_files[0].1 = cfg_override.clone();
        } else {
            bail!("--config can only be used with a single spec file, not with multiple files or directories");
        }
    }

    if spec_files.is_empty() {
        bail!("no .tla spec files found in the provided paths");
    }

    // Load spec baseline for comparison (the TLC baseline, not bench baseline).
    let spec_baseline = config
        .baseline
        .as_ref()
        .map(|p| load_spec_baseline(p))
        .transpose()?;

    // Load previously-saved bench baseline for time comparison.
    let bench_baseline = config
        .save_baseline
        .as_ref()
        .filter(|p| p.exists())
        .map(|p| load_bench_baseline(p))
        .transpose()?;

    let total = spec_files.len();
    let mut results = Vec::with_capacity(total);

    for (idx, (tla_path, cfg_path)) in spec_files.iter().enumerate() {
        let spec_name = spec_name_from_path(tla_path);
        eprintln!(
            "[{}/{}] Benchmarking {} ...",
            idx + 1,
            total,
            spec_name
        );

        let result = bench_one_spec(
            &exe,
            &spec_name,
            tla_path,
            cfg_path,
            config.iterations,
            config.workers,
            spec_baseline.as_ref(),
            bench_baseline.as_ref(),
        );
        results.push(result);
    }

    // Output results.
    match config.format {
        BenchOutputFormat::Human => print_human(&results),
        BenchOutputFormat::Json => print_json(&results)?,
        BenchOutputFormat::Markdown => print_markdown(&results),
    }

    // Save baseline if requested.
    if let Some(ref save_path) = config.save_baseline {
        save_bench_baseline(save_path, &results)?;
        eprintln!("\nBaseline saved to {}", save_path.display());
    }

    // Exit with error if any spec failed.
    let any_fail = results.iter().any(|r| matches!(r.status, BenchStatus::Fail | BenchStatus::Error));
    if any_fail {
        bail!("one or more specs failed during benchmarking");
    }
    Ok(())
}

// ── Spec file collection ─────────────────────────────────────────────────────

/// Collect .tla files from the provided paths (files or directories).
/// For each .tla file, find its companion .cfg file.
fn collect_spec_files(paths: &[PathBuf]) -> Result<Vec<(PathBuf, PathBuf)>> {
    let mut specs = Vec::new();
    for path in paths {
        if path.is_dir() {
            collect_from_directory(path, &mut specs)?;
        } else if path.extension().is_some_and(|e| e == "tla") {
            let cfg = find_cfg_for_tla(path);
            specs.push((path.clone(), cfg));
        } else {
            bail!(
                "expected a .tla file or directory, got: {}",
                path.display()
            );
        }
    }
    Ok(specs)
}

/// Recursively collect .tla files from a directory.
fn collect_from_directory(dir: &Path, specs: &mut Vec<(PathBuf, PathBuf)>) -> Result<()> {
    let mut entries: Vec<_> = fs::read_dir(dir)
        .with_context(|| format!("read directory {}", dir.display()))?
        .filter_map(|e| e.ok())
        .collect();
    entries.sort_by_key(|e| e.file_name());

    for entry in entries {
        let path = entry.path();
        if path.is_dir() {
            collect_from_directory(&path, specs)?;
        } else if path.extension().is_some_and(|e| e == "tla") {
            let cfg = find_cfg_for_tla(&path);
            specs.push((path, cfg));
        }
    }
    Ok(())
}

/// Find the .cfg file for a .tla file (same stem, .cfg extension).
fn find_cfg_for_tla(tla_path: &Path) -> PathBuf {
    let mut cfg = tla_path.to_path_buf();
    cfg.set_extension("cfg");
    cfg
}

/// Extract a human-readable spec name from a file path.
fn spec_name_from_path(path: &Path) -> String {
    path.file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| path.display().to_string())
}

// ── Benchmark execution ──────────────────────────────────────────────────────

/// Benchmark a single spec over `iterations` runs.
fn bench_one_spec(
    exe: &Path,
    spec_name: &str,
    tla_path: &Path,
    cfg_path: &Path,
    iterations: usize,
    workers: usize,
    spec_baseline: Option<&SpecBaseline>,
    bench_baseline: Option<&BenchBaseline>,
) -> BenchResult {
    let mut iteration_times = Vec::with_capacity(iterations);
    let mut last_states_found = 0u64;
    let mut last_distinct = 0u64;
    let mut last_states_per_sec = 0.0f64;
    let mut last_memory_mb: Option<f64> = None;
    let mut last_status = BenchStatus::Pass;

    for i in 0..iterations {
        if iterations > 1 {
            eprint!("  iteration {}/{} ... ", i + 1, iterations);
        }
        let start = Instant::now();
        match run_check_subprocess(exe, tla_path, cfg_path, workers) {
            Ok(parsed) => {
                let elapsed = start.elapsed();
                let elapsed_ms = elapsed.as_millis() as u64;
                iteration_times.push(elapsed_ms);

                last_states_found = parsed.statistics.states_found;
                last_distinct = parsed.statistics.states_distinct.unwrap_or(last_states_found);
                last_states_per_sec = parsed
                    .statistics
                    .states_per_second
                    .unwrap_or_else(|| {
                        if elapsed.as_secs_f64() > 0.0 {
                            last_states_found as f64 / elapsed.as_secs_f64()
                        } else {
                            0.0
                        }
                    });
                last_memory_mb = parsed.statistics.memory_mb;
                last_status = match parsed.result.status.as_str() {
                    "ok" => BenchStatus::Pass,
                    "error" => BenchStatus::Fail,
                    "timeout" => BenchStatus::Timeout,
                    _ => BenchStatus::Error,
                };

                if iterations > 1 {
                    eprintln!("{}ms", elapsed_ms);
                }
            }
            Err(e) => {
                let elapsed_ms = start.elapsed().as_millis() as u64;
                iteration_times.push(elapsed_ms);
                last_status = BenchStatus::Error;
                if iterations > 1 {
                    eprintln!("error: {e}");
                } else {
                    eprintln!("  error: {e}");
                }
            }
        }
    }

    // Compute median wall time across iterations.
    let wall_time_ms = if iteration_times.is_empty() {
        0
    } else {
        let mut sorted = iteration_times.clone();
        sorted.sort();
        sorted[sorted.len() / 2]
    };

    // Compute throughput from median time.
    let states_per_sec = if wall_time_ms > 0 {
        last_states_found as f64 / (wall_time_ms as f64 / 1000.0)
    } else {
        last_states_per_sec
    };

    // Compare against spec baseline (TLC data).
    let vs_baseline = compute_baseline_comparison(
        spec_name,
        last_states_found,
        wall_time_ms,
        spec_baseline,
        bench_baseline,
    );

    BenchResult {
        spec_name: spec_name.to_string(),
        states_found: last_states_found,
        distinct_states: last_distinct,
        wall_time_ms,
        states_per_sec,
        peak_memory_mb: last_memory_mb,
        status: last_status,
        iteration_times_ms: if iterations > 1 {
            iteration_times
        } else {
            Vec::new()
        },
        workers,
        vs_baseline,
    }
}

/// Spawn `tla2 check --output json` and parse the JSON output.
fn run_check_subprocess(
    exe: &Path,
    tla_path: &Path,
    cfg_path: &Path,
    workers: usize,
) -> Result<CheckJsonOutput> {
    let mut cmd = std::process::Command::new(exe);
    cmd.arg("check")
        .arg(tla_path)
        .arg("--output")
        .arg("json")
        .arg("--continue-on-error");

    if cfg_path.exists() {
        cmd.arg("--config").arg(cfg_path);
    }

    if workers > 0 {
        cmd.arg("--workers").arg(workers.to_string());
    }

    let output = cmd
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .output()
        .context("failed to spawn tla2 check subprocess")?;

    let stdout = String::from_utf8_lossy(&output.stdout);

    // The JSON output is on stdout. Parse it.
    serde_json::from_str::<CheckJsonOutput>(&stdout).with_context(|| {
        let stderr = String::from_utf8_lossy(&output.stderr);
        format!(
            "failed to parse JSON output from tla2 check (exit={}):\nstdout: {}\nstderr: {}",
            output.status, stdout, stderr
        )
    })
}

// ── Baseline loading and comparison ──────────────────────────────────────────

fn load_spec_baseline(path: &Path) -> Result<SpecBaseline> {
    let text = fs::read_to_string(path)
        .with_context(|| format!("read baseline {}", path.display()))?;
    serde_json::from_str(&text).context("parse spec_baseline.json")
}

fn load_bench_baseline(path: &Path) -> Result<BenchBaseline> {
    let text = fs::read_to_string(path)
        .with_context(|| format!("read bench baseline {}", path.display()))?;
    serde_json::from_str(&text).context("parse bench baseline JSON")
}

fn compute_baseline_comparison(
    spec_name: &str,
    states_found: u64,
    wall_time_ms: u64,
    spec_baseline: Option<&SpecBaseline>,
    bench_baseline: Option<&BenchBaseline>,
) -> Option<BaselineComparison> {
    // First try bench baseline (previously saved TLA2 runs).
    if let Some(bb) = bench_baseline {
        if let Some(entry) = bb.specs.get(spec_name) {
            let speedup = if wall_time_ms > 0 {
                entry.wall_time_ms as f64 / wall_time_ms as f64
            } else {
                0.0
            };
            return Some(BaselineComparison {
                baseline_time_ms: entry.wall_time_ms,
                speedup,
                states_match: states_found == entry.states_found,
            });
        }
    }

    // Fall back to spec baseline (TLC comparison data).
    if let Some(sb) = spec_baseline {
        if let Some(entry) = sb.specs.get(spec_name) {
            if let Some(tlc_time) = entry.tlc.time_seconds {
                let tlc_time_ms = (tlc_time * 1000.0) as u64;
                let speedup = if wall_time_ms > 0 {
                    tlc_time_ms as f64 / wall_time_ms as f64
                } else {
                    0.0
                };
                return Some(BaselineComparison {
                    baseline_time_ms: tlc_time_ms,
                    speedup,
                    states_match: entry
                        .tlc
                        .states
                        .map_or(true, |s| states_found == s),
                });
            }
        }
    }

    None
}

// ── Baseline saving ──────────────────────────────────────────────────────────

fn save_bench_baseline(path: &Path, results: &[BenchResult]) -> Result<()> {
    let commit = std::process::Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string());

    let timestamp = chrono::Utc::now().to_rfc3339();

    let mut specs = BTreeMap::new();
    for r in results {
        if matches!(r.status, BenchStatus::Pass) {
            specs.insert(
                r.spec_name.clone(),
                BenchBaselineEntry {
                    states_found: r.states_found,
                    distinct_states: r.distinct_states,
                    wall_time_ms: r.wall_time_ms,
                    states_per_sec: r.states_per_sec,
                    workers: r.workers,
                },
            );
        }
    }

    let baseline = BenchBaseline {
        timestamp,
        commit,
        specs,
    };

    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)
            .with_context(|| format!("create directory {}", parent.display()))?;
    }

    let json = serde_json::to_string_pretty(&baseline).context("serialize bench baseline")?;
    fs::write(path, json).with_context(|| format!("write bench baseline {}", path.display()))
}

// ── Output formatting ────────────────────────────────────────────────────────

fn print_human(results: &[BenchResult]) {
    // Header
    println!(
        "{:<30} {:>7} {:>12} {:>12} {:>12} {:>10}",
        "Spec", "Status", "States", "Time", "States/s", "vs Base"
    );
    println!("{}", "-".repeat(87));

    for r in results {
        let time_str = format_duration_ms(r.wall_time_ms);
        let throughput_str = format_throughput(r.states_per_sec);
        let baseline_str = match &r.vs_baseline {
            Some(cmp) => format_speedup(cmp.speedup),
            None => "-".to_string(),
        };
        let states_str = format_count(r.states_found);

        println!(
            "{:<30} {:>7} {:>12} {:>12} {:>12} {:>10}",
            truncate_name(&r.spec_name, 30),
            r.status,
            states_str,
            time_str,
            throughput_str,
            baseline_str,
        );
    }

    // Summary
    println!("{}", "-".repeat(87));
    let pass_count = results.iter().filter(|r| r.status == BenchStatus::Pass).count();
    let total_time: u64 = results.iter().map(|r| r.wall_time_ms).sum();
    let total_states: u64 = results.iter().map(|r| r.states_found).sum();
    println!(
        "{} specs, {} passed, total {} states in {}",
        results.len(),
        pass_count,
        format_count(total_states),
        format_duration_ms(total_time),
    );

    // Show memory if available.
    let with_mem: Vec<_> = results.iter().filter_map(|r| r.peak_memory_mb).collect();
    if !with_mem.is_empty() {
        let max_mem = with_mem.iter().cloned().fold(0.0f64, f64::max);
        println!("Peak memory: {:.0} MB", max_mem);
    }
}

fn print_json(results: &[BenchResult]) -> Result<()> {
    let json = serde_json::to_string_pretty(results).context("serialize bench results")?;
    println!("{json}");
    Ok(())
}

fn print_markdown(results: &[BenchResult]) {
    println!("| Spec | Status | States | Time | States/s | vs Baseline |");
    println!("|:-----|:------:|-------:|-----:|---------:|:-----------:|");
    for r in results {
        let time_str = format_duration_ms(r.wall_time_ms);
        let throughput_str = format_throughput(r.states_per_sec);
        let baseline_str = match &r.vs_baseline {
            Some(cmp) => format_speedup(cmp.speedup),
            None => "-".to_string(),
        };
        println!(
            "| {} | {} | {} | {} | {} | {} |",
            r.spec_name,
            r.status,
            format_count(r.states_found),
            time_str,
            throughput_str,
            baseline_str,
        );
    }
}

// ── Formatting helpers ───────────────────────────────────────────────────────

fn format_duration_ms(ms: u64) -> String {
    if ms < 1_000 {
        format!("{}ms", ms)
    } else if ms < 60_000 {
        format!("{:.1}s", ms as f64 / 1_000.0)
    } else {
        let secs = ms / 1_000;
        format!("{}m{:02}s", secs / 60, secs % 60)
    }
}

fn format_throughput(sps: f64) -> String {
    if sps >= 1_000_000.0 {
        format!("{:.1}M", sps / 1_000_000.0)
    } else if sps >= 1_000.0 {
        format!("{:.1}K", sps / 1_000.0)
    } else {
        format!("{:.0}", sps)
    }
}

fn format_count(n: u64) -> String {
    if n >= 1_000_000 {
        format!("{:.2}M", n as f64 / 1_000_000.0)
    } else if n >= 1_000 {
        format!("{:.1}K", n as f64 / 1_000.0)
    } else {
        format!("{}", n)
    }
}

fn format_speedup(speedup: f64) -> String {
    if speedup >= 1.0 {
        format!("{:.2}x faster", speedup)
    } else if speedup > 0.0 {
        format!("{:.2}x slower", 1.0 / speedup)
    } else {
        "-".to_string()
    }
}

fn truncate_name(name: &str, max_len: usize) -> String {
    if name.len() <= max_len {
        name.to_string()
    } else {
        format!("{}...", &name[..max_len.saturating_sub(3)])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_duration_ms_millis() {
        assert_eq!(format_duration_ms(42), "42ms");
        assert_eq!(format_duration_ms(999), "999ms");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_duration_ms_seconds() {
        assert_eq!(format_duration_ms(1_500), "1.5s");
        assert_eq!(format_duration_ms(59_999), "60.0s");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_duration_ms_minutes() {
        assert_eq!(format_duration_ms(60_000), "1m00s");
        assert_eq!(format_duration_ms(125_000), "2m05s");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_throughput() {
        assert_eq!(format_throughput(42.0), "42");
        assert_eq!(format_throughput(1_234.0), "1.2K");
        assert_eq!(format_throughput(2_500_000.0), "2.5M");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_count() {
        assert_eq!(format_count(42), "42");
        assert_eq!(format_count(1_234), "1.2K");
        assert_eq!(format_count(6_016_610), "6.02M");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_format_speedup() {
        assert_eq!(format_speedup(2.0), "2.00x faster");
        assert_eq!(format_speedup(0.5), "2.00x slower");
        assert_eq!(format_speedup(0.0), "-");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_truncate_name_short() {
        assert_eq!(truncate_name("Foo", 30), "Foo");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_truncate_name_long() {
        let long = "A".repeat(35);
        let result = truncate_name(&long, 30);
        assert!(result.len() <= 30);
        assert!(result.ends_with("..."));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bench_result_serialization_roundtrip() {
        let result = BenchResult {
            spec_name: "MCBakery".to_string(),
            states_found: 6_016_610,
            distinct_states: 6_016_610,
            wall_time_ms: 18_700,
            states_per_sec: 321_685.0,
            peak_memory_mb: Some(128.5),
            status: BenchStatus::Pass,
            iteration_times_ms: vec![18_500, 18_700, 18_900],
            workers: 1,
            vs_baseline: Some(BaselineComparison {
                baseline_time_ms: 5_000,
                speedup: 0.267,
                states_match: true,
            }),
        };
        let json = serde_json::to_string(&result).expect("serialize");
        let parsed: BenchResult = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(parsed.spec_name, "MCBakery");
        assert_eq!(parsed.states_found, 6_016_610);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_bench_baseline_serialization_roundtrip() {
        let mut specs = BTreeMap::new();
        specs.insert(
            "TestSpec".to_string(),
            BenchBaselineEntry {
                states_found: 100,
                distinct_states: 50,
                wall_time_ms: 500,
                states_per_sec: 200.0,
                workers: 1,
            },
        );
        let baseline = BenchBaseline {
            timestamp: "2026-03-30T00:00:00Z".to_string(),
            commit: Some("abc1234".to_string()),
            specs,
        };
        let json = serde_json::to_string_pretty(&baseline).expect("serialize");
        let parsed: BenchBaseline = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(parsed.specs.len(), 1);
        assert!(parsed.specs.contains_key("TestSpec"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compute_baseline_comparison_with_bench_baseline() {
        let mut specs = BTreeMap::new();
        specs.insert(
            "Foo".to_string(),
            BenchBaselineEntry {
                states_found: 100,
                distinct_states: 100,
                wall_time_ms: 1000,
                states_per_sec: 100.0,
                workers: 1,
            },
        );
        let bb = BenchBaseline {
            timestamp: String::new(),
            commit: None,
            specs,
        };
        let cmp = compute_baseline_comparison("Foo", 100, 500, None, Some(&bb));
        assert!(cmp.is_some());
        let cmp = cmp.expect("should have comparison");
        assert!(cmp.states_match);
        assert!((cmp.speedup - 2.0).abs() < 0.01);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compute_baseline_comparison_none() {
        let cmp = compute_baseline_comparison("Nonexistent", 100, 500, None, None);
        assert!(cmp.is_none());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_spec_name_from_path() {
        assert_eq!(
            spec_name_from_path(Path::new("/foo/bar/MCBakery.tla")),
            "MCBakery"
        );
        assert_eq!(spec_name_from_path(Path::new("Spec.tla")), "Spec");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_find_cfg_for_tla() {
        let cfg = find_cfg_for_tla(Path::new("/foo/MCBakery.tla"));
        assert_eq!(cfg, PathBuf::from("/foo/MCBakery.cfg"));
    }
}
