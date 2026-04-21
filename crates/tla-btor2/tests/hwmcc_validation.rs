// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! HWMCC'25 validation test harness.
//!
//! Reads the HWMCC'25 word-level BV results CSV to determine ground-truth
//! expected results (consensus across all participating solvers), then
//! validates that the TLA2 BTOR2 parser can handle every benchmark file.
//!
//! ## Modes
//!
//! **Parse-only (default):** For every benchmark with a consensus result,
//! parse the BTOR2 file and verify that parsing succeeds. This validates
//! the parser covers all opcodes and constructs used in real-world
//! hardware model checking benchmarks.
//!
//! **Full solve (opt-in):** Set `TLA2_HWMCC_SOLVE=1` to additionally run
//! the BTOR2 model checker on each benchmark and compare the result against
//! the HWMCC consensus. This is expensive and intended for CI or manual
//! validation runs.
//!
//! ## Data sources
//!
//! - Results CSV: `~/hwmcc/results/hwmcc25-wordlevel-bv.csv`
//!   Columns: benchmark, config, result, time_real, time_cpu, memory
//!   Results: sat, unsat, none, unknown, timeout, memout, error
//!
//! - Benchmark files: `~/hwmcc/benchmarks/wordlevel/bv/<benchmark_path>`
//!
//! Run with: cargo test -p tla-btor2 --test hwmcc_validation

use std::collections::HashMap;
use std::path::PathBuf;
use std::time::Duration;

use tla_btor2::parser::parse_file;
use tla_btor2::PortfolioConfig;

// ---------------------------------------------------------------------------
// Data model
// ---------------------------------------------------------------------------

/// Expected result for a benchmark (consensus across all HWMCC solvers).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HwmccResult {
    /// All properties are safe (unreachable bad states).
    Unsat,
    /// At least one property is violated (reachable bad state).
    Sat,
}

/// A benchmark entry with its expected result and filesystem path.
#[derive(Debug)]
struct BenchmarkEntry {
    /// Relative path as it appears in the CSV (e.g., "2019/beem/bakery.3.prop1-func-interl.btor2").
    relative_path: String,
    /// Consensus result from HWMCC.
    expected: HwmccResult,
    /// Absolute path to the BTOR2 file.
    absolute_path: PathBuf,
}

// ---------------------------------------------------------------------------
// CSV loading
// ---------------------------------------------------------------------------

/// Root directory for HWMCC'25 word-level BV benchmarks.
fn hwmcc_bv_dir() -> PathBuf {
    let home = std::env::var("HOME").expect("HOME not set");
    PathBuf::from(home).join("hwmcc/benchmarks/wordlevel/bv")
}

/// Path to the HWMCC'25 results CSV.
fn hwmcc_csv_path() -> PathBuf {
    let home = std::env::var("HOME").expect("HOME not set");
    PathBuf::from(home).join("hwmcc/results/hwmcc25-wordlevel-bv.csv")
}

/// Load the HWMCC results CSV and compute consensus results.
///
/// A benchmark has consensus when all tools that returned a definitive
/// answer (sat or unsat) agree. Benchmarks where no tool returned a
/// definitive answer, or where tools disagree, are excluded.
fn load_consensus_results() -> Vec<BenchmarkEntry> {
    let csv_path = hwmcc_csv_path();
    if !csv_path.exists() {
        panic!(
            "HWMCC results CSV not found at {}. Set up ~/hwmcc/ to run these tests.",
            csv_path.display()
        );
    }

    let bv_dir = hwmcc_bv_dir();

    // Collect all definitive results per benchmark.
    let contents = std::fs::read_to_string(&csv_path)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", csv_path.display()));

    // Validate header.
    let header = contents.lines().next().expect("CSV must have header");
    assert!(
        header.contains("benchmark"),
        "CSV header should contain 'benchmark', got: {header}"
    );

    // Parse all data lines (skip header).
    let csv_lines: Vec<&str> = contents.lines().skip(1).collect();
    let mut results_map: HashMap<String, Vec<String>> = HashMap::new();

    for line in &csv_lines {
        let fields: Vec<&str> = line.split(',').collect();
        if fields.len() < 3 {
            continue;
        }
        let benchmark = fields[0].to_string();
        let result = fields[2].trim().to_string();
        results_map.entry(benchmark).or_default().push(result);
    }

    // Compute consensus: all sat/unsat results must agree.
    let mut entries = Vec::new();
    for (benchmark, results) in &results_map {
        let definitive: Vec<&str> = results
            .iter()
            .filter(|r| *r == "sat" || *r == "unsat")
            .map(|s| s.as_str())
            .collect();

        if definitive.is_empty() {
            // No tool returned a definitive result.
            continue;
        }

        // Check consensus: all definitive results must be the same.
        let first = definitive[0];
        if !definitive.iter().all(|r| *r == first) {
            // Conflict among solvers — skip this benchmark.
            eprintln!("WARNING: conflicting results for {benchmark}, skipping");
            continue;
        }

        let expected = match first {
            "sat" => HwmccResult::Sat,
            "unsat" => HwmccResult::Unsat,
            _ => unreachable!(),
        };

        let absolute_path = bv_dir.join(benchmark);
        if !absolute_path.exists() {
            continue;
        }

        entries.push(BenchmarkEntry {
            relative_path: benchmark.clone(),
            expected,
            absolute_path,
        });
    }

    // Sort for deterministic test ordering.
    entries.sort_by(|a, b| a.relative_path.cmp(&b.relative_path));
    entries
}

/// Load only BEEM protocol benchmarks (small, directly relevant to TLA2).
fn load_beem_benchmarks() -> Vec<BenchmarkEntry> {
    load_consensus_results()
        .into_iter()
        .filter(|e| e.relative_path.contains("/beem/"))
        .collect()
}

// ---------------------------------------------------------------------------
// Tests: Parse-only validation
// ---------------------------------------------------------------------------

/// Validate that every BEEM benchmark with consensus parses successfully.
///
/// BEEM benchmarks are small protocol models (bakery, collision, brp2, exit,
/// pgm_protocol) — directly relevant to TLA2's domain.
#[test]
fn test_hwmcc_beem_benchmarks_parse() {
    let benchmarks = load_beem_benchmarks();
    assert!(
        !benchmarks.is_empty(),
        "expected at least one BEEM benchmark with consensus"
    );

    let mut failures = Vec::new();
    let mut success_count = 0;

    for entry in &benchmarks {
        match parse_file(&entry.absolute_path) {
            Ok(prog) => {
                success_count += 1;
                // Sanity: every BEEM benchmark should have at least one bad property.
                assert!(
                    !prog.bad_properties.is_empty(),
                    "{}: parsed but has no bad properties",
                    entry.relative_path
                );
            }
            Err(e) => {
                failures.push(format!("{}: {e}", entry.relative_path));
            }
        }
    }

    eprintln!(
        "BEEM parse validation: {success_count}/{} passed",
        benchmarks.len()
    );

    assert!(
        failures.is_empty(),
        "failed to parse {} BEEM benchmark(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Validate that ALL benchmarks with consensus parse successfully.
///
/// This covers all 291 benchmarks where HWMCC solvers agreed on the result,
/// spanning multiple categories: BEEM protocols, Goel industrial circuits,
/// Mann designs, Wolf designs, HKUST arithmetic, SosyLab, and YosysHQ.
#[test]
fn test_hwmcc_all_consensus_benchmarks_parse() {
    let benchmarks = load_consensus_results();
    assert!(
        benchmarks.len() > 100,
        "expected >100 consensus benchmarks, got {}",
        benchmarks.len()
    );

    let mut failures = Vec::new();
    let mut success_count = 0;
    let mut sat_count = 0;
    let mut unsat_count = 0;

    for entry in &benchmarks {
        match parse_file(&entry.absolute_path) {
            Ok(_prog) => {
                success_count += 1;
                match entry.expected {
                    HwmccResult::Sat => sat_count += 1,
                    HwmccResult::Unsat => unsat_count += 1,
                }
            }
            Err(e) => {
                failures.push(format!("{}: {e}", entry.relative_path));
            }
        }
    }

    eprintln!(
        "HWMCC parse validation: {success_count}/{} passed (sat={sat_count}, unsat={unsat_count})",
        benchmarks.len()
    );

    assert!(
        failures.is_empty(),
        "failed to parse {} benchmark(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Verify expected result distribution matches HWMCC'25 data.
#[test]
fn test_hwmcc_result_distribution() {
    let benchmarks = load_consensus_results();

    let sat_count = benchmarks
        .iter()
        .filter(|b| b.expected == HwmccResult::Sat)
        .count();
    let unsat_count = benchmarks
        .iter()
        .filter(|b| b.expected == HwmccResult::Unsat)
        .count();

    // From the CSV analysis: 103 sat, 188 unsat, 0 conflicts.
    // Allow some tolerance in case benchmarks are added/removed.
    assert!(
        sat_count >= 90,
        "expected >= 90 sat benchmarks, got {sat_count}"
    );
    assert!(
        unsat_count >= 170,
        "expected >= 170 unsat benchmarks, got {unsat_count}"
    );
    assert_eq!(
        sat_count + unsat_count,
        benchmarks.len(),
        "all benchmarks should be sat or unsat"
    );

    eprintln!(
        "HWMCC result distribution: {} total ({sat_count} sat, {unsat_count} unsat)",
        benchmarks.len()
    );
}

/// Validate structural properties of parsed BEEM benchmarks.
///
/// Verifies that each benchmark has the expected number of states, inputs,
/// and bad properties based on manual inspection.
#[test]
fn test_hwmcc_beem_structural_properties() {
    let _ = load_beem_benchmarks(); // ensures data is available

    // Expected values from grep -c on the benchmark files.
    let expected: &[(&str, usize, usize, usize)] = &[
        // (relative_path, num_states, num_inputs, num_bad)
        ("2019/beem/bakery.3.prop1-func-interl.btor2", 28, 24, 1),
        ("2019/beem/brp2.3.prop3-func-interl.btor2", 44, 33, 1),
        ("2019/beem/collision.1.prop1-func-interl.btor2", 27, 31, 1),
        ("2019/beem/exit.3.prop1-back-serstep.btor2", 52, 139, 1),
        (
            "2019/beem/pgm_protocol.8.prop6-func-interl.btor2",
            178,
            120,
            1,
        ),
    ];

    let bv_dir = hwmcc_bv_dir();
    for &(relative, exp_states, exp_inputs, exp_bad) in expected {
        let path = bv_dir.join(relative);
        if !path.exists() {
            continue;
        }
        let prog = parse_file(&path).unwrap_or_else(|e| panic!("failed to parse {relative}: {e}"));

        assert_eq!(
            prog.num_states, exp_states,
            "{relative}: expected {exp_states} states, got {}",
            prog.num_states
        );
        assert_eq!(
            prog.num_inputs, exp_inputs,
            "{relative}: expected {exp_inputs} inputs, got {}",
            prog.num_inputs
        );
        assert_eq!(
            prog.bad_properties.len(),
            exp_bad,
            "{relative}: expected {exp_bad} bad properties, got {}",
            prog.bad_properties.len()
        );
    }
}

// ---------------------------------------------------------------------------
// Tests: Full solve validation (opt-in via TLA2_HWMCC_SOLVE=1)
// ---------------------------------------------------------------------------

/// Run the full BTOR2 model checker on BEEM benchmarks and compare results.
///
/// This test is gated by the `TLA2_HWMCC_SOLVE` environment variable.
/// Set `TLA2_HWMCC_SOLVE=1` to enable.
#[test]
fn test_hwmcc_beem_solve() {
    if std::env::var("TLA2_HWMCC_SOLVE").unwrap_or_default() != "1" {
        eprintln!("SKIP: set TLA2_HWMCC_SOLVE=1 to run full solve validation");
        return;
    }

    let benchmarks = load_beem_benchmarks();
    assert!(!benchmarks.is_empty());

    let config = PortfolioConfig {
        time_budget: Some(Duration::from_secs(30)),
        enable_coi: true,
        enable_simplify: true,
        enable_bmc: true,
        bmc_budget_fraction: 0.2,
        bmc_max_depth: 20,
        verbose: false,
    };

    let mut correct = 0;
    let mut wrong = 0;
    let mut timeout = 0;
    let mut errors = Vec::new();

    for entry in &benchmarks {
        let prog = match parse_file(&entry.absolute_path) {
            Ok(p) => p,
            Err(e) => {
                errors.push(format!("{}: parse error: {e}", entry.relative_path));
                wrong += 1;
                continue;
            }
        };

        let (results, stats) = match tla_btor2::check_btor2_portfolio(&prog, &config) {
            Ok(r) => r,
            Err(e) => {
                errors.push(format!("{}: solver error: {e}", entry.relative_path));
                wrong += 1;
                continue;
            }
        };

        // Determine our verdict: any sat result means sat, all unsat means unsat.
        let any_sat = results
            .iter()
            .any(|r| matches!(r, tla_btor2::Btor2CheckResult::Sat { .. }));
        let any_unknown = results
            .iter()
            .any(|r| matches!(r, tla_btor2::Btor2CheckResult::Unknown { .. }));

        if any_unknown && !any_sat {
            timeout += 1;
            eprintln!(
                "  {} -> TIMEOUT (expected {:?}, phase={:?})",
                entry.relative_path, entry.expected, stats.result_phase
            );
            continue;
        }

        let our_result = if any_sat {
            HwmccResult::Sat
        } else {
            HwmccResult::Unsat
        };

        if our_result == entry.expected {
            correct += 1;
            eprintln!(
                "  {} -> CORRECT ({:?}, phase={:?}, COI {}/{})",
                entry.relative_path,
                our_result,
                stats.result_phase,
                stats.states_after_coi,
                stats.states_before_coi,
            );
        } else {
            wrong += 1;
            errors.push(format!(
                "{}: expected {:?}, got {:?}",
                entry.relative_path, entry.expected, our_result
            ));
            eprintln!(
                "  {} -> WRONG (expected {:?}, got {:?})",
                entry.relative_path, entry.expected, our_result
            );
        }
    }

    eprintln!(
        "BEEM solve validation: {correct} correct, {wrong} wrong, {timeout} timeout / {} total",
        benchmarks.len()
    );
    assert!(
        errors.is_empty(),
        "WRONG answers ({wrong}):\n{}",
        errors.join("\n")
    );
}

/// Run the full BTOR2 model checker on ALL consensus benchmarks.
///
/// Gated by `TLA2_HWMCC_SOLVE=all`. Uses the portfolio pipeline
/// (COI + BMC preprocessing + full CHC) with a per-benchmark timeout.
#[test]
fn test_hwmcc_all_solve() {
    if std::env::var("TLA2_HWMCC_SOLVE").unwrap_or_default() != "all" {
        eprintln!("SKIP: set TLA2_HWMCC_SOLVE=all to run full solve on all benchmarks");
        return;
    }

    let timeout_secs: u64 = std::env::var("TLA2_HWMCC_TIMEOUT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(15);

    let benchmarks = load_consensus_results();
    let config = PortfolioConfig {
        time_budget: Some(Duration::from_secs(timeout_secs)),
        enable_coi: true,
        enable_simplify: true,
        enable_bmc: true,
        bmc_budget_fraction: 0.2,
        bmc_max_depth: 20,
        verbose: false,
    };

    let mut correct = 0;
    let mut wrong = 0;
    let mut timeout = 0;
    let mut error_count = 0;
    let mut wrong_details = Vec::new();

    for (idx, entry) in benchmarks.iter().enumerate() {
        let prog = match parse_file(&entry.absolute_path) {
            Ok(p) => p,
            Err(e) => {
                error_count += 1;
                eprintln!(
                    "  [{}/{}] {} -> ERROR (parse: {e})",
                    idx + 1,
                    benchmarks.len(),
                    entry.relative_path,
                );
                continue;
            }
        };

        let (results, stats) = match tla_btor2::check_btor2_portfolio(&prog, &config) {
            Ok(r) => r,
            Err(e) => {
                error_count += 1;
                eprintln!(
                    "  [{}/{}] {} -> ERROR (solver: {e})",
                    idx + 1,
                    benchmarks.len(),
                    entry.relative_path,
                );
                continue;
            }
        };

        let any_sat = results
            .iter()
            .any(|r| matches!(r, tla_btor2::Btor2CheckResult::Sat { .. }));
        let any_unknown = results
            .iter()
            .any(|r| matches!(r, tla_btor2::Btor2CheckResult::Unknown { .. }));

        if any_unknown && !any_sat {
            timeout += 1;
            eprintln!(
                "  [{}/{}] {} -> TIMEOUT (expected {:?})",
                idx + 1,
                benchmarks.len(),
                entry.relative_path,
                entry.expected,
            );
            continue;
        }

        let our_result = if any_sat {
            HwmccResult::Sat
        } else {
            HwmccResult::Unsat
        };

        if our_result == entry.expected {
            correct += 1;
            eprintln!(
                "  [{}/{}] {} -> CORRECT ({:?}, phase={:?}, COI {}/{}, {:.1}s)",
                idx + 1,
                benchmarks.len(),
                entry.relative_path,
                our_result,
                stats.result_phase,
                stats.states_after_coi,
                stats.states_before_coi,
                stats.total_time.as_secs_f64(),
            );
        } else {
            wrong += 1;
            wrong_details.push(format!(
                "{}: expected {:?}, got {:?}",
                entry.relative_path, entry.expected, our_result
            ));
            eprintln!(
                "  [{}/{}] {} -> WRONG (expected {:?}, got {:?})",
                idx + 1,
                benchmarks.len(),
                entry.relative_path,
                entry.expected,
                our_result,
            );
        }
    }

    let total = benchmarks.len();
    eprintln!(
        "\nHWMCC full solve: {correct} correct, {wrong} wrong, {timeout} timeout, {error_count} error / {total} total"
    );
    eprintln!(
        "Accuracy: {correct}/{} ({:.1}% of resolved)",
        correct + wrong,
        if correct + wrong > 0 {
            100.0 * correct as f64 / (correct + wrong) as f64
        } else {
            0.0
        }
    );

    assert!(
        wrong == 0,
        "WRONG answers ({wrong}):\n{}",
        wrong_details.join("\n")
    );
}
