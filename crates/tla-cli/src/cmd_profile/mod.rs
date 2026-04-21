// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 profile` -- performance profiling for model checking runs.
//!
//! Runs `tla2 check` as a subprocess with profiling flags enabled, parses the
//! JSON output and stderr profiling data, and reports:
//!
//! 1. Overall statistics: total/distinct states, wall time, states/sec, peak memory
//! 2. Per-action breakdown: occurrences, successor count, percentage
//! 3. Operator hotspots: eval call counts (from `--profile-eval` stderr)
//! 4. Memory timeline: periodic RSS snapshots (macOS `ps` based)
//! 5. Level-by-level BFS stats: states per level, time per level

use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};

use crate::cli_schema::ProfileOutputFormat;

// ── Configuration ────────────────────────────────────────────────────────────

/// Configuration built from CLI args.
pub(crate) struct ProfileConfig {
    pub file: PathBuf,
    pub config: Option<PathBuf>,
    pub workers: usize,
    pub format: ProfileOutputFormat,
    pub top: usize,
    pub memory: bool,
}

// ── Result types ─────────────────────────────────────────────────────────────

/// Complete profile report.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct ProfileReport {
    pub spec_name: String,
    pub overall: OverallStats,
    pub actions: Vec<ActionProfile>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub eval_hotspots: Vec<EvalHotspot>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub memory_timeline: Vec<MemorySnapshot>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub bfs_levels: Vec<BfsLevelStats>,
}

/// Overall checking statistics.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct OverallStats {
    pub states_found: u64,
    pub states_distinct: u64,
    pub wall_time_seconds: f64,
    pub states_per_second: f64,
    pub peak_memory_mb: Option<f64>,
    pub workers: usize,
    pub status: String,
    pub max_depth: Option<u64>,
}

/// Per-action profiling data.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct ActionProfile {
    pub name: String,
    pub occurrences: u64,
    pub percentage: f64,
}

/// Operator eval hotspot parsed from `--profile-eval` stderr output.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct EvalHotspot {
    pub label: String,
    pub count: u64,
}

/// Memory RSS snapshot at a point in time.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct MemorySnapshot {
    pub elapsed_seconds: f64,
    pub rss_mb: f64,
}

/// Per-BFS-level statistics parsed from progress output.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct BfsLevelStats {
    pub level: u32,
    pub states_in_level: u64,
    pub cumulative_states: u64,
    pub elapsed_seconds: f64,
}

// ── Subset of JSON output from `tla2 check --output json` ───────────────────

#[derive(Deserialize)]
struct CheckJsonOutput {
    result: CheckJsonResult,
    statistics: CheckJsonStats,
    #[serde(default)]
    actions_detected: Vec<CheckJsonAction>,
}

#[derive(Deserialize)]
struct CheckJsonResult {
    status: String,
}

#[derive(Deserialize)]
#[allow(dead_code)]
struct CheckJsonStats {
    states_found: u64,
    #[serde(default)]
    states_distinct: Option<u64>,
    #[serde(default)]
    states_per_second: Option<f64>,
    #[serde(default)]
    memory_mb: Option<f64>,
    #[serde(default)]
    time_seconds: f64,
    #[serde(default)]
    max_depth: Option<u64>,
}

#[derive(Deserialize)]
struct CheckJsonAction {
    name: String,
    occurrences: u64,
    #[serde(default)]
    percentage: Option<f64>,
}

// ── Entry point ──────────────────────────────────────────────────────────────

pub(crate) fn cmd_profile(config: ProfileConfig) -> Result<()> {
    let exe = std::env::current_exe().context("resolve current exe path")?;

    if !config.file.exists() {
        bail!("spec file not found: {}", config.file.display());
    }

    let spec_name = config
        .file
        .file_stem()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_else(|| config.file.display().to_string());

    eprintln!("Profiling {} ...", spec_name);

    let report = run_profiling(
        &exe,
        &spec_name,
        &config.file,
        config.config.as_deref(),
        config.workers,
        config.memory,
        config.top,
    )?;

    match config.format {
        ProfileOutputFormat::Human => print_human_report(&report, config.top),
        ProfileOutputFormat::Json => print_json_report(&report)?,
    }

    Ok(())
}

// ── Profiling execution ──────────────────────────────────────────────────────

/// Run the check subprocess with profiling enabled and collect all data.
fn run_profiling(
    exe: &Path,
    spec_name: &str,
    tla_path: &Path,
    cfg_path: Option<&Path>,
    workers: usize,
    collect_memory: bool,
    top: usize,
) -> Result<ProfileReport> {
    let mut cmd = Command::new(exe);
    cmd.arg("check")
        .arg(tla_path)
        .arg("--output")
        .arg("json")
        .arg("--profile-eval")
        .arg("--profile-enum")
        .arg("--continue-on-error")
        .arg("--coverage");

    if let Some(cfg) = cfg_path {
        if cfg.exists() {
            cmd.arg("--config").arg(cfg);
        }
    } else {
        // Try default .cfg path
        let mut default_cfg = tla_path.to_path_buf();
        default_cfg.set_extension("cfg");
        if default_cfg.exists() {
            cmd.arg("--config").arg(default_cfg);
        }
    }

    if workers > 0 {
        cmd.arg("--workers").arg(workers.to_string());
    }

    cmd.stdout(Stdio::piped()).stderr(Stdio::piped());

    let start = Instant::now();
    let mut child = cmd.spawn().context("failed to spawn tla2 check subprocess")?;

    let child_id = child.id();

    // Collect stderr lines in a background thread (for profile-eval output).
    let stderr = child.stderr.take().context("capture stderr")?;
    let stderr_lines: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));
    let stderr_lines_clone = Arc::clone(&stderr_lines);
    let stderr_thread = std::thread::spawn(move || {
        let reader = BufReader::new(stderr);
        for line in reader.lines() {
            if let Ok(line) = line {
                stderr_lines_clone
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .push(line);
            }
        }
    });

    // Collect memory snapshots in a background thread.
    let memory_timeline: Arc<Mutex<Vec<MemorySnapshot>>> = Arc::new(Mutex::new(Vec::new()));
    let mem_timeline_clone = Arc::clone(&memory_timeline);
    let mem_start = start;
    let mem_thread = if collect_memory {
        let pid = child_id;
        Some(std::thread::spawn(move || {
            collect_memory_timeline(pid, mem_start, &mem_timeline_clone);
        }))
    } else {
        None
    };

    // Wait for the child to finish.
    let output = child.wait_with_output().context("wait for tla2 check")?;
    let wall_time = start.elapsed();

    // Join background threads.
    let _ = stderr_thread.join();
    if let Some(t) = mem_thread {
        let _ = t.join();
    }

    let stdout = String::from_utf8_lossy(&output.stdout);

    // Parse JSON output.
    let parsed: CheckJsonOutput = serde_json::from_str(&stdout).with_context(|| {
        let stderr_text = stderr_lines
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .join("\n");
        format!(
            "failed to parse JSON from tla2 check (exit={}):\nstdout (first 500): {}\nstderr (last 500): {}",
            output.status,
            &stdout[..stdout.len().min(500)],
            &stderr_text[stderr_text.len().saturating_sub(500)..]
        )
    })?;

    let stderr_vec = stderr_lines
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .clone();

    // Parse eval hotspots from stderr.
    let eval_hotspots = parse_eval_hotspots(&stderr_vec, top);

    // Parse BFS level stats from stderr progress lines.
    let bfs_levels = parse_bfs_levels(&stderr_vec);

    // Build action profiles.
    let total_occurrences: u64 = parsed.actions_detected.iter().map(|a| a.occurrences).sum();
    let actions: Vec<ActionProfile> = parsed
        .actions_detected
        .iter()
        .map(|a| ActionProfile {
            name: a.name.clone(),
            occurrences: a.occurrences,
            percentage: a
                .percentage
                .unwrap_or_else(|| {
                    if total_occurrences > 0 {
                        a.occurrences as f64 / total_occurrences as f64 * 100.0
                    } else {
                        0.0
                    }
                }),
        })
        .collect();

    let states_found = parsed.statistics.states_found;
    let distinct = parsed.statistics.states_distinct.unwrap_or(states_found);
    let wall_secs = wall_time.as_secs_f64();

    let mem_snapshots = memory_timeline
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .clone();

    // Determine peak memory: max of RSS snapshots or reported memory_mb.
    let peak_from_snapshots = mem_snapshots
        .iter()
        .map(|s| s.rss_mb)
        .fold(f64::NEG_INFINITY, f64::max);
    let peak_memory_mb = if peak_from_snapshots > 0.0 {
        Some(peak_from_snapshots)
    } else {
        parsed.statistics.memory_mb
    };

    Ok(ProfileReport {
        spec_name: spec_name.to_string(),
        overall: OverallStats {
            states_found,
            states_distinct: distinct,
            wall_time_seconds: wall_secs,
            states_per_second: parsed
                .statistics
                .states_per_second
                .unwrap_or_else(|| {
                    if wall_secs > 0.0 {
                        states_found as f64 / wall_secs
                    } else {
                        0.0
                    }
                }),
            peak_memory_mb,
            workers,
            status: parsed.result.status,
            max_depth: parsed.statistics.max_depth,
        },
        actions,
        eval_hotspots,
        memory_timeline: mem_snapshots,
        bfs_levels,
    })
}

// ── Memory collection (macOS) ────────────────────────────────────────────────

/// Periodically sample RSS of the child process via `ps`.
fn collect_memory_timeline(
    pid: u32,
    start: Instant,
    timeline: &Mutex<Vec<MemorySnapshot>>,
) {
    let interval = Duration::from_millis(500);
    loop {
        std::thread::sleep(interval);
        let elapsed = start.elapsed().as_secs_f64();

        match sample_rss(pid) {
            Some(rss_mb) => {
                timeline
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .push(MemorySnapshot {
                        elapsed_seconds: elapsed,
                        rss_mb,
                    });
            }
            None => {
                // Process likely exited.
                break;
            }
        }
    }
}

/// Sample the RSS of a process in MB via `ps -o rss= -p <pid>`.
fn sample_rss(pid: u32) -> Option<f64> {
    let output = Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .output()
        .ok()?;

    if !output.status.success() {
        return None;
    }

    let text = String::from_utf8_lossy(&output.stdout);
    let kb: f64 = text.trim().parse().ok()?;
    Some(kb / 1024.0) // KB to MB
}

// ── Stderr parsing ───────────────────────────────────────────────────────────

/// Parse eval hotspot lines from stderr.
///
/// The `--profile-eval` output on stderr looks like:
/// ```text
/// === Eval Profile ===
///   Total eval() calls: 12345
/// ```
///
/// The `--profile-enum` output looks like:
/// ```text
/// === Enumeration Profile ===
///   Successor generation: 1234ms (45.2%)
///   Fingerprinting:        567ms (21.3%)
///   ...
/// ```
fn parse_eval_hotspots(lines: &[String], top: usize) -> Vec<EvalHotspot> {
    let mut hotspots = Vec::new();

    for line in lines {
        let trimmed = line.trim();

        // Parse "Total eval() calls: N"
        if let Some(rest) = trimmed.strip_prefix("Total eval() calls:") {
            if let Ok(count) = rest.trim().replace(',', "").parse::<u64>() {
                hotspots.push(EvalHotspot {
                    label: "Total eval() calls".to_string(),
                    count,
                });
            }
            continue;
        }

        // Parse enumeration profile lines like "  Successor generation: 1234ms (45.2%)"
        // or "  Something: 1234ms"
        if let Some((label, rest)) = trimmed.split_once(':') {
            let rest = rest.trim();
            // Try to parse "NNNms" or "NNN"
            let value_str = rest
                .split_whitespace()
                .next()
                .unwrap_or("")
                .trim_end_matches("ms")
                .replace(',', "");
            if let Ok(value) = value_str.parse::<u64>() {
                let clean_label = label.trim().to_string();
                // Filter out section headers and empty labels
                if !clean_label.is_empty()
                    && !clean_label.starts_with("===")
                    && !clean_label.starts_with("---")
                    && value > 0
                {
                    hotspots.push(EvalHotspot {
                        label: clean_label,
                        count: value,
                    });
                }
            }
        }
    }

    // Sort by count descending, take top N.
    hotspots.sort_by(|a, b| b.count.cmp(&a.count));
    hotspots.truncate(top);
    hotspots
}

/// Parse BFS level stats from stderr progress lines.
///
/// Progress lines on stderr look like:
/// ```text
/// Progress: level 3, 1234 states, 5678 distinct, 0.5s
/// ```
fn parse_bfs_levels(lines: &[String]) -> Vec<BfsLevelStats> {
    let mut levels = Vec::new();

    for line in lines {
        let trimmed = line.trim();

        // Look for progress lines with level information.
        // Various formats:
        //   "Level 3: 456 new states (1234 total), 0.5s"
        //   "  level 3 ... states ... "
        if let Some(level_info) = parse_progress_level_line(trimmed) {
            levels.push(level_info);
        }
    }

    levels
}

/// Try to parse a single progress line into BFS level stats.
fn parse_progress_level_line(line: &str) -> Option<BfsLevelStats> {
    // Pattern: look for "level N" or "Level N" or "depth N"
    let lower = line.to_lowercase();

    let level_idx = lower.find("level ").or_else(|| lower.find("depth "))?;
    let after_keyword = &line[level_idx..];
    let num_start = after_keyword.find(char::is_numeric)?;
    let num_str: String = after_keyword[num_start..]
        .chars()
        .take_while(|c| c.is_ascii_digit())
        .collect();
    let level: u32 = num_str.parse().ok()?;

    // Try to find state counts: look for numbers after "states" or just large numbers
    let mut states_in_level: u64 = 0;
    let mut cumulative: u64 = 0;

    // Look for patterns like "N new" or "N states" or "total N" or "(N total)"
    let words: Vec<&str> = line.split_whitespace().collect();
    for (i, word) in words.iter().enumerate() {
        let cleaned = word.replace(',', "").replace('(', "").replace(')', "");
        if let Ok(num) = cleaned.parse::<u64>() {
            // If next word is "new" or "states", this is states_in_level
            if i + 1 < words.len() {
                let next = words[i + 1].to_lowercase();
                if next.starts_with("new") || next.starts_with("state") {
                    states_in_level = num;
                } else if next.starts_with("total") || next.starts_with("distinct") {
                    cumulative = num;
                }
            }
            // If previous word is "total" or "distinct"
            if i > 0 {
                let prev = words[i - 1].to_lowercase();
                if prev.contains("total") || prev.contains("distinct") || prev.contains("cumulative")
                {
                    cumulative = num;
                }
            }
        }
    }

    // Try to find elapsed time: "N.Ns" or "Nms"
    let mut elapsed = 0.0f64;
    for word in &words {
        let cleaned = word.replace(',', "");
        if let Some(secs_str) = cleaned.strip_suffix('s') {
            // Could be "0.5s" (seconds) or "500ms" (milliseconds)
            if let Some(ms_str) = secs_str.strip_suffix('m') {
                if let Ok(ms) = ms_str.parse::<f64>() {
                    elapsed = ms / 1000.0;
                }
            } else if let Ok(s) = secs_str.parse::<f64>() {
                elapsed = s;
            }
        }
    }

    Some(BfsLevelStats {
        level,
        states_in_level,
        cumulative_states: cumulative,
        elapsed_seconds: elapsed,
    })
}

// ── Human output formatting ──────────────────────────────────────────────────

fn print_human_report(report: &ProfileReport, top: usize) {
    println!();
    println!("=== Profile Report: {} ===", report.spec_name);
    println!();

    // 1. Overall statistics
    println!("--- Overall Statistics ---");
    println!(
        "  Status:          {}",
        report.overall.status
    );
    println!(
        "  States found:    {}",
        format_count(report.overall.states_found)
    );
    println!(
        "  Distinct states: {}",
        format_count(report.overall.states_distinct)
    );
    if let Some(depth) = report.overall.max_depth {
        println!("  Max BFS depth:   {depth}");
    }
    println!(
        "  Wall time:       {:.3}s",
        report.overall.wall_time_seconds
    );
    println!(
        "  Throughput:      {} states/s",
        format_throughput(report.overall.states_per_second)
    );
    if let Some(mem) = report.overall.peak_memory_mb {
        println!("  Peak memory:     {:.1} MB", mem);
    }
    println!("  Workers:         {}", report.overall.workers);
    println!();

    // 2. Per-action breakdown
    if !report.actions.is_empty() {
        println!("--- Action Breakdown ---");
        println!(
            "  {:<40} {:>12} {:>8}",
            "Action", "Occurrences", "%"
        );
        println!("  {}", "-".repeat(62));
        for action in &report.actions {
            let bar = make_bar(action.percentage, 20);
            println!(
                "  {:<40} {:>12} {:>7.1}% {}",
                truncate_name(&action.name, 40),
                format_count(action.occurrences),
                action.percentage,
                bar,
            );
        }
        println!();
    }

    // 3. Operator hotspots
    if !report.eval_hotspots.is_empty() {
        println!("--- Hotspots (top {}) ---", top);
        println!("  {:<50} {:>14}", "Metric", "Value");
        println!("  {}", "-".repeat(66));
        let max_count = report
            .eval_hotspots
            .first()
            .map(|h| h.count)
            .unwrap_or(1);
        for hotspot in &report.eval_hotspots {
            let pct = if max_count > 0 {
                hotspot.count as f64 / max_count as f64 * 100.0
            } else {
                0.0
            };
            let bar = make_bar(pct, 15);
            println!(
                "  {:<50} {:>14} {}",
                truncate_name(&hotspot.label, 50),
                format_count(hotspot.count),
                bar,
            );
        }
        println!();
    }

    // 4. Memory timeline
    if !report.memory_timeline.is_empty() {
        println!("--- Memory Timeline ---");
        println!("  {:>8} {:>10}", "Time", "RSS (MB)");
        println!("  {}", "-".repeat(20));
        // Show a sampled subset (up to 20 points).
        let step = (report.memory_timeline.len() / 20).max(1);
        for snap in report.memory_timeline.iter().step_by(step) {
            println!(
                "  {:>7.1}s {:>9.1}",
                snap.elapsed_seconds, snap.rss_mb
            );
        }
        // Always show the last snapshot.
        if let Some(last) = report.memory_timeline.last() {
            if report.memory_timeline.len() > 1 {
                println!(
                    "  {:>7.1}s {:>9.1}  (final)",
                    last.elapsed_seconds, last.rss_mb
                );
            }
        }
        println!();
    }

    // 5. BFS level stats
    if !report.bfs_levels.is_empty() {
        println!("--- BFS Levels ---");
        println!(
            "  {:>5} {:>14} {:>14} {:>10}",
            "Level", "New States", "Cumulative", "Elapsed"
        );
        println!("  {}", "-".repeat(47));
        for level in &report.bfs_levels {
            println!(
                "  {:>5} {:>14} {:>14} {:>9.3}s",
                level.level,
                format_count(level.states_in_level),
                format_count(level.cumulative_states),
                level.elapsed_seconds,
            );
        }
        println!();
    }
}

// ── JSON output ──────────────────────────────────────────────────────────────

fn print_json_report(report: &ProfileReport) -> Result<()> {
    let json = serde_json::to_string_pretty(report).context("serialize profile report")?;
    println!("{json}");
    Ok(())
}

// ── Formatting helpers ───────────────────────────────────────────────────────

/// Format a large count with comma separators.
fn format_count(n: u64) -> String {
    if n < 1_000 {
        return n.to_string();
    }
    let s = n.to_string();
    let mut result = String::with_capacity(s.len() + s.len() / 3);
    for (i, c) in s.chars().enumerate() {
        if i > 0 && (s.len() - i) % 3 == 0 {
            result.push(',');
        }
        result.push(c);
    }
    result
}

/// Format throughput as a human-readable string.
fn format_throughput(sps: f64) -> String {
    if sps >= 1_000_000.0 {
        format!("{:.2}M", sps / 1_000_000.0)
    } else if sps >= 1_000.0 {
        format!("{:.1}K", sps / 1_000.0)
    } else {
        format!("{:.0}", sps)
    }
}

/// Truncate a name to fit within `max_len` characters.
fn truncate_name(name: &str, max_len: usize) -> String {
    if name.len() <= max_len {
        name.to_string()
    } else {
        format!("{}...", &name[..max_len.saturating_sub(3)])
    }
}

/// Create a text-based bar proportional to a percentage (0-100).
fn make_bar(pct: f64, max_width: usize) -> String {
    let filled = ((pct / 100.0) * max_width as f64).round() as usize;
    let filled = filled.min(max_width);
    let empty = max_width.saturating_sub(filled);
    format!("[{}{}]", "#".repeat(filled), " ".repeat(empty))
}
