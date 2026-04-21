// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native Rust benchmark runner — executes Z4 directly without Python.
//!
//! Discovers benchmarks from eval spec YAML, runs them with timeout,
//! and produces results.json compatible with scoring.rs.

use anyhow::{bail, Context, Result};
use serde::Serialize;
use std::io::Read as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

// ===================================================================
// Result types (JSON-compatible with scoring.rs)
// ===================================================================

#[derive(Debug, Serialize)]
pub(crate) struct NativeResultItem {
    pub file: String,
    pub expected: Option<String>,
    pub result: String,
    pub time_sec: f64,
    pub cpu_time_sec: f64,
    pub exit_code: Option<i32>,
}

#[derive(Debug, Serialize)]
pub(crate) struct ComparisonItem {
    pub file: String,
    pub z4_result: String,
    pub z4_time_sec: f64,
    pub ref_result: String,
    pub ref_time_sec: f64,
    pub agreement: &'static str,
}

#[derive(Debug, Serialize)]
pub(crate) struct ComparisonSummary {
    pub reference_solver: String,
    pub agree: u32,
    pub disagree: u32,
    pub z4_only: u32,
    pub ref_only: u32,
    pub both_solved: u32,
    pub z4_faster: u32,
    pub ref_faster: u32,
    pub z4_total_time: f64,
    pub ref_total_time: f64,
}

#[derive(Debug, Serialize)]
pub(crate) struct NativeResults {
    pub environment: crate::environment::Environment,
    pub items: Vec<NativeResultItem>,
    pub settings: NativeSettings,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comparison: Option<ComparisonSummary>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub comparisons: Option<Vec<ComparisonItem>>,
}

#[derive(Debug, Serialize)]
pub(crate) struct NativeSettings {
    pub benchmarks_dir: String,
    pub timeout_sec: f64,
    pub domain: String,
    pub benchmark_count: usize,
}

// ===================================================================
// Verdict parsing
// ===================================================================

fn parse_verdict(stdout: &str, exit_code: Option<i32>) -> &'static str {
    for line in stdout.lines() {
        let trimmed = line.trim();
        let lower = trimmed.to_ascii_lowercase();
        match lower.as_str() {
            "sat" | "s satisfiable" | "satisfiable" => return "sat",
            "unsat" | "s unsatisfiable" | "unsatisfiable" => return "unsat",
            "unknown" | "s unknown" => return "unknown",
            _ => {}
        }
    }
    match exit_code {
        Some(10) => "sat",
        Some(20) => "unsat",
        _ => "error",
    }
}

fn guess_expected_from_path(path: &Path) -> Option<String> {
    let name = path.file_name()?.to_str()?.to_ascii_lowercase();
    let parts: Vec<String> = path.iter().map(|p| p.to_string_lossy().to_ascii_lowercase()).collect();

    if parts.iter().any(|p| p == "unsat") {
        return Some("unsat".to_string());
    }
    if parts.iter().any(|p| p == "sat") {
        return Some("sat".to_string());
    }
    // SATLIB naming: uufN = unsatisfiable uniform random, ufN = satisfiable
    // Only match when followed by a digit to avoid false positives on
    // UFLRA/UFLIA/etc. SMT-LIB logic names.
    if name.starts_with("uuf")
        && name.as_bytes().get(3).is_some_and(|b| b.is_ascii_digit())
    {
        return Some("unsat".to_string());
    }
    if name.starts_with("uf")
        && name.as_bytes().get(2).is_some_and(|b| b.is_ascii_digit())
    {
        return Some("sat".to_string());
    }
    None
}

// ===================================================================
// Benchmark discovery
// ===================================================================

fn is_benchmark_file(path: &Path, domain: &str) -> bool {
    let name = match path.file_name().and_then(|n| n.to_str()) {
        Some(n) => n,
        None => return false,
    };
    match domain {
        "sat" => {
            // Only plain .cnf — compressed files (.xz/.gz/.bz2) require
            // decompression which the native runner does not yet support.
            name.ends_with(".cnf") || name.ends_with(".dimacs") || name.ends_with(".icnf")
        }
        "chc" | "smt" => name.ends_with(".smt2"),
        _ => name.ends_with(".smt2") || name.ends_with(".cnf"),
    }
}

pub(crate) fn discover_benchmarks(dir: &Path, domain: &str) -> Result<Vec<PathBuf>> {
    if !dir.exists() {
        bail!("benchmarks directory not found: {}", dir.display());
    }
    let mut files = Vec::new();
    collect_benchmarks_recursive(dir, domain, &mut files)?;
    files.sort();
    Ok(files)
}

fn collect_benchmarks_recursive(dir: &Path, domain: &str, out: &mut Vec<PathBuf>) -> Result<()> {
    for entry in std::fs::read_dir(dir).with_context(|| format!("reading {}", dir.display()))? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_benchmarks_recursive(&path, domain, out)?;
        } else if is_benchmark_file(&path, domain) {
            out.push(path);
        }
    }
    Ok(())
}

// ===================================================================
// Solver execution with timeout
// ===================================================================

fn run_solver(
    z4_path: &Path,
    benchmark: &Path,
    timeout_sec: f64,
    is_chc: bool,
) -> NativeResultItem {
    let start = Instant::now();
    let timeout = Duration::from_secs_f64(timeout_sec);
    let file_name = benchmark
        .file_name()
        .map(|n| n.to_string_lossy().to_string())
        .unwrap_or_else(|| benchmark.display().to_string());
    let expected = guess_expected_from_path(benchmark);

    let mut cmd = Command::new(z4_path);
    if is_chc {
        cmd.arg("--chc");
    }
    cmd.arg(benchmark);
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::piped());

    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            return NativeResultItem {
                file: file_name,
                expected,
                result: format!("error: {e}"),
                time_sec: 0.0,
                cpu_time_sec: 0.0,
                exit_code: None,
            };
        }
    };

    // Poll for completion with timeout
    let poll_interval = Duration::from_millis(50);
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let elapsed = start.elapsed().as_secs_f64();
                let mut stdout = String::new();
                if let Some(mut out) = child.stdout.take() {
                    let _ = out.read_to_string(&mut stdout);
                }
                let verdict = parse_verdict(&stdout, status.code());
                // Wall time is used as a CPU time approximation. For
                // single-threaded CPU-bound solvers this is accurate. True
                // child-process CPU time would require platform-specific APIs
                // (libc::getrusage / wait4) which need unsafe code, and this
                // crate forbids unsafe.
                return NativeResultItem {
                    file: file_name,
                    expected,
                    result: verdict.to_string(),
                    time_sec: round6(elapsed),
                    cpu_time_sec: round6(elapsed),
                    exit_code: status.code(),
                };
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return NativeResultItem {
                        file: file_name,
                        expected,
                        result: "timeout".to_string(),
                        time_sec: round6(timeout_sec),
                        cpu_time_sec: round6(timeout_sec),
                        exit_code: None,
                    };
                }
                std::thread::sleep(poll_interval);
            }
            Err(_) => {
                let elapsed = start.elapsed().as_secs_f64();
                return NativeResultItem {
                    file: file_name,
                    expected,
                    result: "error".to_string(),
                    time_sec: round6(elapsed),
                    cpu_time_sec: round6(elapsed),
                    exit_code: None,
                };
            }
        }
    }
}

/// Run an external solver (e.g., z3) on a benchmark and return (verdict, time_sec).
fn run_external_solver(
    solver_path: &Path,
    benchmark: &Path,
    timeout_sec: f64,
) -> (String, f64) {
    let start = Instant::now();
    let timeout = Duration::from_secs_f64(timeout_sec);

    let mut cmd = Command::new(solver_path);
    cmd.arg(benchmark);
    cmd.stdout(Stdio::piped());
    cmd.stderr(Stdio::piped());

    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(_) => return ("error".to_string(), 0.0),
    };

    let poll_interval = Duration::from_millis(50);
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                let elapsed = start.elapsed().as_secs_f64();
                let mut stdout = String::new();
                if let Some(mut out) = child.stdout.take() {
                    let _ = out.read_to_string(&mut stdout);
                }
                let verdict = parse_verdict(&stdout, status.code());
                return (verdict.to_string(), round6(elapsed));
            }
            Ok(None) => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return ("timeout".to_string(), round6(timeout_sec));
                }
                std::thread::sleep(poll_interval);
            }
            Err(_) => {
                return ("error".to_string(), round6(start.elapsed().as_secs_f64()));
            }
        }
    }
}

fn round6(x: f64) -> f64 {
    (x * 1_000_000.0).round() / 1_000_000.0
}

fn classify_agreement(z4: &str, reference: &str) -> &'static str {
    let definitive = |s: &str| s == "sat" || s == "unsat";
    match (definitive(z4), definitive(reference)) {
        (true, true) => {
            if z4 == reference { "agree" } else { "disagree" }
        }
        (true, false) => "z4_only",
        (false, true) => "ref_only",
        (false, false) => "both_unknown",
    }
}

// ===================================================================
// Public entry point
// ===================================================================

pub(crate) struct NativeRunArgs<'a> {
    pub z4: &'a Path,
    pub benchmarks_dir: &'a Path,
    pub timeout_sec: f64,
    pub domain: &'a str,
    pub quiet: bool,
    /// Pre-built file list. If set, skips directory discovery.
    pub file_list: Option<Vec<PathBuf>>,
    /// Number of runs per benchmark. The median-time run is selected.
    pub runs: u32,
    /// Reference solver binary for comparison (e.g., z3).
    pub reference_solver: Option<PathBuf>,
}

/// Select the representative run from multiple results for the same benchmark.
/// Picks the run with median wall time. For even counts, picks the lower median.
pub(crate) fn select_representative(mut results: Vec<NativeResultItem>) -> NativeResultItem {
    if results.len() == 1 {
        return results.remove(0);
    }
    results.sort_by(|a, b| a.time_sec.partial_cmp(&b.time_sec).unwrap());
    let mid = (results.len() - 1) / 2;
    results.remove(mid)
}

pub(crate) fn run_native(args: &NativeRunArgs<'_>) -> Result<NativeResults> {
    let env = crate::environment::Environment::capture(args.z4);

    let benchmarks = if let Some(ref list) = args.file_list {
        list.clone()
    } else {
        discover_benchmarks(args.benchmarks_dir, args.domain)?
    };
    if benchmarks.is_empty() {
        bail!(
            "no {} benchmarks found in {}",
            args.domain,
            args.benchmarks_dir.display()
        );
    }

    let is_chc = args.domain == "chc";
    let total = benchmarks.len();
    let runs = args.runs.max(1);

    if !args.quiet {
        eprintln!("[env] {env}");
        if runs > 1 {
            eprintln!(
                "[native] running {} {} benchmarks x {} runs, timeout={:.0}s",
                total, args.domain, runs, args.timeout_sec,
            );
        } else {
            eprintln!(
                "[native] running {} {} benchmarks, timeout={:.0}s",
                total, args.domain, args.timeout_sec,
            );
        }
    }

    let mut items = Vec::with_capacity(total);
    for (idx, benchmark) in benchmarks.iter().enumerate() {
        if !args.quiet && (idx == 0 || idx + 1 == total || (idx + 1) % 10 == 0) {
            eprintln!(
                "[native] {}/{}: {}",
                idx + 1,
                total,
                benchmark.file_name().unwrap_or_default().to_string_lossy(),
            );
        }
        if runs == 1 {
            let item = run_solver(args.z4, benchmark, args.timeout_sec, is_chc);
            items.push(item);
        } else {
            let mut run_results = Vec::with_capacity(runs as usize);
            for _ in 0..runs {
                run_results.push(run_solver(args.z4, benchmark, args.timeout_sec, is_chc));
            }
            items.push(select_representative(run_results));
        }
    }

    // Run reference solver if specified
    let (comparison, comparisons) = if let Some(ref ref_solver) = args.reference_solver {
        if !args.quiet {
            eprintln!(
                "[ref] running reference solver {} on {} benchmarks",
                ref_solver.display(),
                total
            );
        }
        let mut comp_items = Vec::with_capacity(total);
        let mut agree = 0u32;
        let mut disagree = 0u32;
        let mut z4_only = 0u32;
        let mut ref_only = 0u32;
        let mut both_solved = 0u32;
        let mut z4_faster = 0u32;
        let mut ref_faster = 0u32;
        let mut z4_total = 0.0f64;
        let mut ref_total = 0.0f64;

        for (idx, benchmark) in benchmarks.iter().enumerate() {
            let z4_item = &items[idx];
            let (ref_result, ref_time) =
                run_external_solver(ref_solver, benchmark, args.timeout_sec);
            let agreement = classify_agreement(&z4_item.result, &ref_result);

            match agreement {
                "agree" => {
                    agree += 1;
                    both_solved += 1;
                    z4_total += z4_item.time_sec;
                    ref_total += ref_time;
                    if z4_item.time_sec < ref_time {
                        z4_faster += 1;
                    } else {
                        ref_faster += 1;
                    }
                }
                "disagree" => disagree += 1,
                "z4_only" => z4_only += 1,
                "ref_only" => ref_only += 1,
                _ => {}
            }

            comp_items.push(ComparisonItem {
                file: z4_item.file.clone(),
                z4_result: z4_item.result.clone(),
                z4_time_sec: z4_item.time_sec,
                ref_result: ref_result.clone(),
                ref_time_sec: ref_time,
                agreement,
            });

            if !args.quiet && (idx == 0 || idx + 1 == total || (idx + 1) % 10 == 0) {
                eprintln!(
                    "[ref] {}/{}: {} ({})",
                    idx + 1,
                    total,
                    benchmark.file_name().unwrap_or_default().to_string_lossy(),
                    agreement,
                );
            }
        }

        let solver_name = ref_solver
            .file_name()
            .map(|n| n.to_string_lossy().to_string())
            .unwrap_or_else(|| ref_solver.display().to_string());

        let summary = ComparisonSummary {
            reference_solver: solver_name,
            agree,
            disagree,
            z4_only,
            ref_only,
            both_solved,
            z4_faster,
            ref_faster,
            z4_total_time: round6(z4_total),
            ref_total_time: round6(ref_total),
        };

        (Some(summary), Some(comp_items))
    } else {
        (None, None)
    };

    let results = NativeResults {
        environment: env,
        items,
        settings: NativeSettings {
            benchmarks_dir: args.benchmarks_dir.display().to_string(),
            timeout_sec: args.timeout_sec,
            domain: args.domain.to_string(),
            benchmark_count: total,
        },
        comparison,
        comparisons,
    };

    Ok(results)
}

// ===================================================================
// Tests
// ===================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_verdict_sat() {
        assert_eq!(parse_verdict("sat\n", None), "sat");
        assert_eq!(parse_verdict("SAT\n", None), "sat");
        assert_eq!(parse_verdict("s satisfiable\n", None), "sat");
    }

    #[test]
    fn test_parse_verdict_unsat() {
        assert_eq!(parse_verdict("unsat\n", None), "unsat");
        assert_eq!(parse_verdict("UNSAT\n", None), "unsat");
        assert_eq!(parse_verdict("s unsatisfiable\n", None), "unsat");
    }

    #[test]
    fn test_parse_verdict_exit_code() {
        assert_eq!(parse_verdict("", Some(10)), "sat");
        assert_eq!(parse_verdict("", Some(20)), "unsat");
        assert_eq!(parse_verdict("", Some(0)), "error");
        assert_eq!(parse_verdict("", None), "error");
    }

    #[test]
    fn test_parse_verdict_unknown() {
        assert_eq!(parse_verdict("unknown\n", None), "unknown");
        assert_eq!(parse_verdict("s unknown\n", None), "unknown");
    }

    #[test]
    fn test_guess_expected_unsat_dir() {
        let path = Path::new("/benchmarks/unsat/foo.cnf");
        assert_eq!(guess_expected_from_path(path), Some("unsat".into()));
    }

    #[test]
    fn test_guess_expected_sat_dir() {
        let path = Path::new("/benchmarks/sat/foo.cnf");
        assert_eq!(guess_expected_from_path(path), Some("sat".into()));
    }

    #[test]
    fn test_guess_expected_uf_prefix() {
        let path = Path::new("/benchmarks/uf100-01.cnf");
        assert_eq!(guess_expected_from_path(path), Some("sat".into()));
    }

    #[test]
    fn test_guess_expected_uuf_prefix() {
        let path = Path::new("/benchmarks/uuf100-01.cnf");
        assert_eq!(guess_expected_from_path(path), Some("unsat".into()));
    }

    #[test]
    fn test_guess_expected_none() {
        let path = Path::new("/benchmarks/problem42.cnf");
        assert_eq!(guess_expected_from_path(path), None);
    }

    #[test]
    fn test_guess_expected_uflra_not_sat() {
        // UFLRA/UFLIA are SMT-LIB logic names, not SATLIB uf-prefix files
        let path = Path::new("/benchmarks/smt/uflra_simple.smt2");
        assert_eq!(guess_expected_from_path(path), None);
        let path = Path::new("/benchmarks/smt/uflia_test.smt2");
        assert_eq!(guess_expected_from_path(path), None);
    }

    #[test]
    fn test_is_benchmark_file_sat() {
        assert!(is_benchmark_file(Path::new("test.cnf"), "sat"));
        // Compressed files are NOT discovered (native runner can't decompress)
        assert!(!is_benchmark_file(Path::new("test.cnf.xz"), "sat"));
        assert!(!is_benchmark_file(Path::new("test.cnf.gz"), "sat"));
        assert!(!is_benchmark_file(Path::new("test.smt2"), "sat"));
    }

    #[test]
    fn test_is_benchmark_file_smt() {
        assert!(is_benchmark_file(Path::new("test.smt2"), "smt"));
        assert!(!is_benchmark_file(Path::new("test.cnf"), "smt"));
    }

    #[test]
    fn test_classify_agreement() {
        assert_eq!(classify_agreement("sat", "sat"), "agree");
        assert_eq!(classify_agreement("unsat", "unsat"), "agree");
        assert_eq!(classify_agreement("sat", "unsat"), "disagree");
        assert_eq!(classify_agreement("unsat", "sat"), "disagree");
        assert_eq!(classify_agreement("sat", "timeout"), "z4_only");
        assert_eq!(classify_agreement("unsat", "unknown"), "z4_only");
        assert_eq!(classify_agreement("timeout", "sat"), "ref_only");
        assert_eq!(classify_agreement("error", "unsat"), "ref_only");
        assert_eq!(classify_agreement("timeout", "unknown"), "both_unknown");
        assert_eq!(classify_agreement("error", "error"), "both_unknown");
    }
}
