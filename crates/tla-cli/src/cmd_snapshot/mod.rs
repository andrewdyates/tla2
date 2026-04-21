// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `snapshot` subcommand: spec snapshot testing for regression detection.
//!
//! Records model-checking results (status, state counts, max depth) as snapshot
//! files, then compares future runs against them to catch regressions.
//!
//! - **Record mode** (`--update`): Run `tla2 check --output json` on each spec,
//!   save key metrics as `<snapshot_dir>/<spec_name>.snapshot.json`.
//! - **Check mode** (default): Run model checking, compare against saved snapshots.
//!   Report any differences as regressions.

use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};

use crate::cli_schema::SnapshotOutputFormat;

// ── Snapshot data ────────────────────────────────────────────────────────────

/// Persisted snapshot of a single spec's model-checking results.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct SpecSnapshot {
    /// Spec file stem (e.g. "MCBakery").
    pub spec: String,
    /// Config file used (e.g. "MCBakery.cfg").
    pub config: String,
    /// Check outcome: "pass" or "error".
    pub status: String,
    /// Number of distinct states found.
    pub distinct_states: u64,
    /// Total number of states found (including duplicates).
    pub total_states: u64,
    /// Maximum BFS depth reached.
    pub max_depth: u64,
    /// Error type if status is "error" (e.g. "invariant_violation").
    pub error_type: Option<String>,
    /// ISO 8601 timestamp of when this snapshot was captured.
    pub timestamp: String,
    /// TLA2 version at time of capture.
    pub tla2_version: String,
}

/// Outcome for a single spec during snapshot checking.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct SnapshotOutcome {
    pub spec: String,
    pub verdict: SnapshotVerdict,
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub regressions: Vec<String>,
}

/// High-level verdict for a snapshot comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum SnapshotVerdict {
    /// Current run matches the saved snapshot exactly.
    Match,
    /// One or more metrics differ from the saved snapshot.
    Regression,
    /// No saved snapshot exists for this spec.
    New,
    /// Model checking failed to produce parseable output.
    Error,
}

impl std::fmt::Display for SnapshotVerdict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Match => write!(f, "MATCH"),
            Self::Regression => write!(f, "REGRESSION"),
            Self::New => write!(f, "NEW"),
            Self::Error => write!(f, "ERROR"),
        }
    }
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
    error_type: Option<String>,
}

#[derive(Deserialize)]
struct CheckJsonStats {
    states_found: u64,
    #[serde(default)]
    states_distinct: Option<u64>,
    #[serde(default)]
    depth: Option<u64>,
}

// ── Entry point ──────────────────────────────────────────────────────────────

pub(crate) fn cmd_snapshot(
    files: &[PathBuf],
    config: Option<&Path>,
    snapshot_dir: &Path,
    update: bool,
    format: SnapshotOutputFormat,
) -> Result<()> {
    if files.is_empty() {
        bail!("at least one .tla file is required");
    }

    let exe = std::env::current_exe().context("resolve current exe path")?;

    // Collect spec files with their configs.
    let spec_files = collect_spec_files(files, config)?;

    // Ensure snapshot directory exists.
    fs::create_dir_all(snapshot_dir)
        .with_context(|| format!("create snapshot dir {}", snapshot_dir.display()))?;

    let mut outcomes = Vec::with_capacity(spec_files.len());

    for (tla_path, cfg_path) in &spec_files {
        let spec_name = spec_name_from_path(tla_path);
        let snapshot_path = snapshot_dir.join(format!("{spec_name}.snapshot.json"));

        eprintln!("Checking {spec_name} ...");

        // Run model checking.
        let run_result = run_check_subprocess(&exe, tla_path, cfg_path);

        match run_result {
            Ok(parsed) => {
                let current = build_snapshot(
                    &spec_name,
                    cfg_path,
                    &parsed,
                );

                if update {
                    // Record mode: save snapshot.
                    save_snapshot(&snapshot_path, &current)?;
                    eprintln!("  Saved snapshot: {}", snapshot_path.display());
                    outcomes.push(SnapshotOutcome {
                        spec: spec_name,
                        verdict: SnapshotVerdict::Match,
                        regressions: Vec::new(),
                    });
                } else {
                    // Check mode: compare against saved snapshot.
                    let outcome = compare_snapshot(&spec_name, &snapshot_path, &current);
                    match outcome.verdict {
                        SnapshotVerdict::Match => {
                            eprintln!("  MATCH");
                        }
                        SnapshotVerdict::Regression => {
                            for r in &outcome.regressions {
                                eprintln!("  REGRESSION: {r}");
                            }
                        }
                        SnapshotVerdict::New => {
                            eprintln!("  NEW (run with --update to create snapshot)");
                        }
                        SnapshotVerdict::Error => {
                            eprintln!("  ERROR");
                        }
                    }
                    outcomes.push(outcome);
                }
            }
            Err(e) => {
                eprintln!("  ERROR: {e}");
                outcomes.push(SnapshotOutcome {
                    spec: spec_name,
                    verdict: SnapshotVerdict::Error,
                    regressions: vec![format!("check failed: {e}")],
                });
            }
        }
    }

    // Output final report.
    match format {
        SnapshotOutputFormat::Human => print_human_report(&outcomes, update),
        SnapshotOutputFormat::Json => print_json_report(&outcomes)?,
    }

    // Exit code: 1 if any regression or error (in check mode).
    if !update {
        let any_regression = outcomes.iter().any(|o| {
            matches!(
                o.verdict,
                SnapshotVerdict::Regression | SnapshotVerdict::Error
            )
        });
        if any_regression {
            bail!("snapshot regressions detected");
        }
    }

    Ok(())
}

// ── Spec file collection ─────────────────────────────────────────────────────

/// Collect .tla files from the provided paths with their companion .cfg files.
fn collect_spec_files(
    paths: &[PathBuf],
    config_override: Option<&Path>,
) -> Result<Vec<(PathBuf, PathBuf)>> {
    let mut specs = Vec::new();
    for path in paths {
        if path.is_dir() {
            collect_from_directory(path, &mut specs)?;
        } else if path.extension().is_some_and(|e| e == "tla") {
            let cfg = match config_override {
                Some(c) => c.to_path_buf(),
                None => find_cfg_for_tla(path),
            };
            specs.push((path.clone(), cfg));
        } else {
            bail!(
                "expected a .tla file or directory, got: {}",
                path.display()
            );
        }
    }
    // Only apply the config override to the first spec if multiple were collected
    // from directories. For directory collection, each spec uses its own .cfg.
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

// ── Model checking execution ─────────────────────────────────────────────────

/// Spawn `tla2 check --output json --continue-on-error` and parse the JSON output.
fn run_check_subprocess(
    exe: &Path,
    tla_path: &Path,
    cfg_path: &Path,
) -> Result<CheckJsonOutput> {
    let mut cmd = std::process::Command::new(exe);
    cmd.arg("check")
        .arg(tla_path)
        .arg("--output")
        .arg("json")
        .arg("--continue-on-error")
        .arg("--workers")
        .arg("1");

    if cfg_path.exists() {
        cmd.arg("--config").arg(cfg_path);
    }

    let output = cmd
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .output()
        .context("failed to spawn tla2 check subprocess")?;

    let stdout = String::from_utf8_lossy(&output.stdout);

    serde_json::from_str::<CheckJsonOutput>(&stdout).with_context(|| {
        let stderr = String::from_utf8_lossy(&output.stderr);
        format!(
            "failed to parse JSON output from tla2 check (exit={}):\nstdout: {}\nstderr: {}",
            output.status, stdout, stderr
        )
    })
}

// ── Snapshot building and I/O ────────────────────────────────────────────────

/// Build a `SpecSnapshot` from parsed JSON output.
fn build_snapshot(
    spec_name: &str,
    cfg_path: &Path,
    parsed: &CheckJsonOutput,
) -> SpecSnapshot {
    let cfg_name = cfg_path
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_default();

    SpecSnapshot {
        spec: spec_name.to_string(),
        config: cfg_name,
        status: parsed.result.status.clone(),
        distinct_states: parsed.statistics.states_distinct.unwrap_or(parsed.statistics.states_found),
        total_states: parsed.statistics.states_found,
        max_depth: parsed.statistics.depth.unwrap_or(0),
        error_type: parsed.result.error_type.clone(),
        timestamp: chrono::Utc::now().to_rfc3339(),
        tla2_version: env!("CARGO_PKG_VERSION").to_string(),
    }
}

/// Save a snapshot to a JSON file.
fn save_snapshot(path: &Path, snapshot: &SpecSnapshot) -> Result<()> {
    let json = serde_json::to_string_pretty(snapshot).context("serialize snapshot")?;
    fs::write(path, json).with_context(|| format!("write snapshot {}", path.display()))
}

/// Load a snapshot from a JSON file.
fn load_snapshot(path: &Path) -> Result<SpecSnapshot> {
    let text =
        fs::read_to_string(path).with_context(|| format!("read snapshot {}", path.display()))?;
    serde_json::from_str(&text).with_context(|| format!("parse snapshot {}", path.display()))
}

// ── Snapshot comparison ──────────────────────────────────────────────────────

/// Compare the current run against a saved snapshot, producing a verdict and
/// a list of human-readable regression descriptions.
fn compare_snapshot(
    spec_name: &str,
    snapshot_path: &Path,
    current: &SpecSnapshot,
) -> SnapshotOutcome {
    if !snapshot_path.exists() {
        return SnapshotOutcome {
            spec: spec_name.to_string(),
            verdict: SnapshotVerdict::New,
            regressions: Vec::new(),
        };
    }

    let saved = match load_snapshot(snapshot_path) {
        Ok(s) => s,
        Err(e) => {
            return SnapshotOutcome {
                spec: spec_name.to_string(),
                verdict: SnapshotVerdict::Error,
                regressions: vec![format!("failed to load snapshot: {e}")],
            };
        }
    };

    let mut regressions = Vec::new();

    // Status comparison.
    if current.status != saved.status {
        regressions.push(format!(
            "{spec_name} status: was {}, now {}",
            saved.status, current.status
        ));
    }

    // Distinct states comparison.
    if current.distinct_states != saved.distinct_states {
        regressions.push(format!(
            "{spec_name} distinct_states: {} -> {}",
            saved.distinct_states, current.distinct_states
        ));
    }

    // Total states comparison.
    if current.total_states != saved.total_states {
        regressions.push(format!(
            "{spec_name} total_states: {} -> {}",
            saved.total_states, current.total_states
        ));
    }

    // Max depth comparison.
    if current.max_depth != saved.max_depth {
        regressions.push(format!(
            "{spec_name} max_depth: {} -> {}",
            saved.max_depth, current.max_depth
        ));
    }

    // Error type comparison (only when both are errors).
    if current.status == "error" && saved.status == "error" {
        if current.error_type != saved.error_type {
            regressions.push(format!(
                "{spec_name} error_type: {:?} -> {:?}",
                saved.error_type, current.error_type
            ));
        }
    }

    let verdict = if regressions.is_empty() {
        SnapshotVerdict::Match
    } else {
        SnapshotVerdict::Regression
    };

    SnapshotOutcome {
        spec: spec_name.to_string(),
        verdict,
        regressions,
    }
}

// ── Output formatting ────────────────────────────────────────────────────────

/// Print a human-readable summary table.
fn print_human_report(outcomes: &[SnapshotOutcome], update_mode: bool) {
    if update_mode {
        println!("\nSnapshot update complete: {} specs recorded.", outcomes.len());
        return;
    }

    println!();
    println!("{:<30} {:>12}", "Spec", "Verdict");
    println!("{}", "-".repeat(44));

    for o in outcomes {
        let verdict_str = match o.verdict {
            SnapshotVerdict::Match => "\x1b[32mMATCH\x1b[0m",
            SnapshotVerdict::Regression => "\x1b[31mREGRESSION\x1b[0m",
            SnapshotVerdict::New => "\x1b[33mNEW\x1b[0m",
            SnapshotVerdict::Error => "\x1b[31mERROR\x1b[0m",
        };
        println!("{:<30} {:>12}", truncate_name(&o.spec, 30), verdict_str);
        for r in &o.regressions {
            println!("    {r}");
        }
    }

    println!("{}", "-".repeat(44));

    let total = outcomes.len();
    let matches = outcomes
        .iter()
        .filter(|o| o.verdict == SnapshotVerdict::Match)
        .count();
    let regressions = outcomes
        .iter()
        .filter(|o| o.verdict == SnapshotVerdict::Regression)
        .count();
    let new_specs = outcomes
        .iter()
        .filter(|o| o.verdict == SnapshotVerdict::New)
        .count();
    let errors = outcomes
        .iter()
        .filter(|o| o.verdict == SnapshotVerdict::Error)
        .count();

    println!(
        "{total} specs: {matches} match, {regressions} regression(s), {new_specs} new, {errors} error(s)"
    );
}

/// Print a structured JSON report.
fn print_json_report(outcomes: &[SnapshotOutcome]) -> Result<()> {
    let json = serde_json::to_string_pretty(outcomes).context("serialize snapshot report")?;
    println!("{json}");
    Ok(())
}

/// Truncate a name to fit within `max_len` characters.
fn truncate_name(name: &str, max_len: usize) -> String {
    if name.len() <= max_len {
        name.to_string()
    } else {
        format!("{}...", &name[..max_len.saturating_sub(3)])
    }
}

// ── Tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_spec_snapshot_serialization_roundtrip() {
        let snapshot = SpecSnapshot {
            spec: "MCBakery".to_string(),
            config: "MCBakery.cfg".to_string(),
            status: "pass".to_string(),
            distinct_states: 1234,
            total_states: 5678,
            max_depth: 42,
            error_type: None,
            timestamp: "2026-03-30T00:00:00Z".to_string(),
            tla2_version: "0.1.0".to_string(),
        };
        let json = serde_json::to_string_pretty(&snapshot).expect("serialize");
        let parsed: SpecSnapshot = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(parsed.spec, "MCBakery");
        assert_eq!(parsed.distinct_states, 1234);
        assert_eq!(parsed.total_states, 5678);
        assert_eq!(parsed.max_depth, 42);
        assert!(parsed.error_type.is_none());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_spec_snapshot_with_error_type() {
        let snapshot = SpecSnapshot {
            spec: "BadSpec".to_string(),
            config: "BadSpec.cfg".to_string(),
            status: "error".to_string(),
            distinct_states: 100,
            total_states: 200,
            max_depth: 5,
            error_type: Some("invariant_violation".to_string()),
            timestamp: "2026-03-30T00:00:00Z".to_string(),
            tla2_version: "0.1.0".to_string(),
        };
        let json = serde_json::to_string_pretty(&snapshot).expect("serialize");
        let parsed: SpecSnapshot = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(parsed.status, "error");
        assert_eq!(
            parsed.error_type.as_deref(),
            Some("invariant_violation")
        );
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compare_snapshot_match() {
        let current = SpecSnapshot {
            spec: "Foo".to_string(),
            config: "Foo.cfg".to_string(),
            status: "pass".to_string(),
            distinct_states: 100,
            total_states: 200,
            max_depth: 10,
            error_type: None,
            timestamp: "2026-03-30T01:00:00Z".to_string(),
            tla2_version: "0.1.0".to_string(),
        };

        let dir = tempfile::tempdir().expect("create tempdir");
        let snap_path = dir.path().join("Foo.snapshot.json");
        save_snapshot(&snap_path, &current).expect("save");

        let outcome = compare_snapshot("Foo", &snap_path, &current);
        assert_eq!(outcome.verdict, SnapshotVerdict::Match);
        assert!(outcome.regressions.is_empty());
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compare_snapshot_regression_state_count() {
        let saved = SpecSnapshot {
            spec: "Foo".to_string(),
            config: "Foo.cfg".to_string(),
            status: "pass".to_string(),
            distinct_states: 100,
            total_states: 200,
            max_depth: 10,
            error_type: None,
            timestamp: "2026-03-30T00:00:00Z".to_string(),
            tla2_version: "0.1.0".to_string(),
        };
        let current = SpecSnapshot {
            distinct_states: 105,
            total_states: 210,
            ..saved.clone()
        };

        let dir = tempfile::tempdir().expect("create tempdir");
        let snap_path = dir.path().join("Foo.snapshot.json");
        save_snapshot(&snap_path, &saved).expect("save");

        let outcome = compare_snapshot("Foo", &snap_path, &current);
        assert_eq!(outcome.verdict, SnapshotVerdict::Regression);
        assert_eq!(outcome.regressions.len(), 2);
        assert!(outcome.regressions[0].contains("distinct_states"));
        assert!(outcome.regressions[1].contains("total_states"));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compare_snapshot_regression_status_change() {
        let saved = SpecSnapshot {
            spec: "Foo".to_string(),
            config: "Foo.cfg".to_string(),
            status: "pass".to_string(),
            distinct_states: 100,
            total_states: 200,
            max_depth: 10,
            error_type: None,
            timestamp: "2026-03-30T00:00:00Z".to_string(),
            tla2_version: "0.1.0".to_string(),
        };
        let current = SpecSnapshot {
            status: "error".to_string(),
            error_type: Some("invariant_violation".to_string()),
            ..saved.clone()
        };

        let dir = tempfile::tempdir().expect("create tempdir");
        let snap_path = dir.path().join("Foo.snapshot.json");
        save_snapshot(&snap_path, &saved).expect("save");

        let outcome = compare_snapshot("Foo", &snap_path, &current);
        assert_eq!(outcome.verdict, SnapshotVerdict::Regression);
        assert!(outcome.regressions.iter().any(|r| r.contains("status")));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compare_snapshot_new_spec() {
        let current = SpecSnapshot {
            spec: "NewSpec".to_string(),
            config: "NewSpec.cfg".to_string(),
            status: "pass".to_string(),
            distinct_states: 50,
            total_states: 100,
            max_depth: 5,
            error_type: None,
            timestamp: "2026-03-30T00:00:00Z".to_string(),
            tla2_version: "0.1.0".to_string(),
        };

        let dir = tempfile::tempdir().expect("create tempdir");
        let snap_path = dir.path().join("NewSpec.snapshot.json");
        // Do NOT create the snapshot file — simulate a new spec.

        let outcome = compare_snapshot("NewSpec", &snap_path, &current);
        assert_eq!(outcome.verdict, SnapshotVerdict::New);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compare_snapshot_regression_depth_change() {
        let saved = SpecSnapshot {
            spec: "Foo".to_string(),
            config: "Foo.cfg".to_string(),
            status: "pass".to_string(),
            distinct_states: 100,
            total_states: 200,
            max_depth: 10,
            error_type: None,
            timestamp: "2026-03-30T00:00:00Z".to_string(),
            tla2_version: "0.1.0".to_string(),
        };
        let current = SpecSnapshot {
            max_depth: 12,
            ..saved.clone()
        };

        let dir = tempfile::tempdir().expect("create tempdir");
        let snap_path = dir.path().join("Foo.snapshot.json");
        save_snapshot(&snap_path, &saved).expect("save");

        let outcome = compare_snapshot("Foo", &snap_path, &current);
        assert_eq!(outcome.verdict, SnapshotVerdict::Regression);
        assert!(outcome.regressions.iter().any(|r| r.contains("max_depth")));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_compare_snapshot_error_type_mismatch() {
        let saved = SpecSnapshot {
            spec: "Bad".to_string(),
            config: "Bad.cfg".to_string(),
            status: "error".to_string(),
            distinct_states: 100,
            total_states: 200,
            max_depth: 10,
            error_type: Some("invariant_violation".to_string()),
            timestamp: "2026-03-30T00:00:00Z".to_string(),
            tla2_version: "0.1.0".to_string(),
        };
        let current = SpecSnapshot {
            error_type: Some("deadlock".to_string()),
            ..saved.clone()
        };

        let dir = tempfile::tempdir().expect("create tempdir");
        let snap_path = dir.path().join("Bad.snapshot.json");
        save_snapshot(&snap_path, &saved).expect("save");

        let outcome = compare_snapshot("Bad", &snap_path, &current);
        assert_eq!(outcome.verdict, SnapshotVerdict::Regression);
        assert!(outcome.regressions.iter().any(|r| r.contains("error_type")));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_snapshot_outcome_serialization() {
        let outcome = SnapshotOutcome {
            spec: "Test".to_string(),
            verdict: SnapshotVerdict::Regression,
            regressions: vec!["Test distinct_states: 100 -> 105".to_string()],
        };
        let json = serde_json::to_string_pretty(&outcome).expect("serialize");
        let parsed: SnapshotOutcome = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(parsed.verdict, SnapshotVerdict::Regression);
        assert_eq!(parsed.regressions.len(), 1);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_spec_name_from_path_basic() {
        assert_eq!(
            spec_name_from_path(Path::new("/foo/bar/MCBakery.tla")),
            "MCBakery"
        );
        assert_eq!(spec_name_from_path(Path::new("Spec.tla")), "Spec");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn test_find_cfg_for_tla_basic() {
        let cfg = find_cfg_for_tla(Path::new("/foo/MCBakery.tla"));
        assert_eq!(cfg, PathBuf::from("/foo/MCBakery.cfg"));
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
}
