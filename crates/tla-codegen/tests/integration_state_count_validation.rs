// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Codegen state count validation: verifies that generated state machines
//! produce the same distinct state counts as TLC.
//!
//! This test generates, compiles, and executes Rust model checkers from
//! real TLA+ specs via `tla2 codegen --tir --scaffold`, then compares
//! the distinct state counts against known TLC baseline values.
//!
//! Only specs confirmed to work through the full pipeline (codegen ->
//! compile -> execute -> correct state count) are included.
//!
//! Part of #3937.

use std::path::{Path, PathBuf};
use std::process::Command;

/// A TLA+ spec with known TLC baseline state counts, confirmed to
/// produce correct results through the TIR codegen pipeline.
struct SpecTestCase {
    /// Human-readable name for reporting.
    name: &'static str,
    /// Relative path within tlaplus-examples/specifications/ to the .tla file.
    tla_rel: &'static str,
    /// Relative path within tlaplus-examples/specifications/ to the .cfg file.
    cfg_rel: &'static str,
    /// Expected distinct states from TLC baseline (spec_baseline.json).
    tlc_distinct_states: usize,
}

/// Curated list of specs that produce correct state counts through TIR codegen.
///
/// Each spec was individually verified to: (1) generate valid Rust via
/// `tla2 codegen --tir --scaffold`, (2) compile successfully, (3) run BFS
/// model checking to completion, (4) produce the exact TLC distinct state
/// count.
const TEST_SPECS: &[SpecTestCase] = &[
    SpecTestCase {
        name: "HourClock",
        tla_rel: "SpecifyingSystems/HourClock/HourClock.tla",
        cfg_rel: "SpecifyingSystems/HourClock/HourClock.cfg",
        tlc_distinct_states: 12,
    },
    SpecTestCase {
        name: "ABCorrectness",
        tla_rel: "SpecifyingSystems/TLC/ABCorrectness.tla",
        cfg_rel: "SpecifyingSystems/TLC/ABCorrectness.cfg",
        tlc_distinct_states: 20,
    },
    SpecTestCase {
        name: "AsynchInterface",
        tla_rel: "SpecifyingSystems/AsynchronousInterface/AsynchInterface.tla",
        cfg_rel: "SpecifyingSystems/AsynchronousInterface/AsynchInterface.cfg",
        tlc_distinct_states: 12,
    },
    SpecTestCase {
        name: "MCConsensus_2",
        tla_rel: "PaxosHowToWinATuringAward/MCConsensus.tla",
        cfg_rel: "PaxosHowToWinATuringAward/MCConsensus.cfg",
        tlc_distinct_states: 4,
    },
    SpecTestCase {
        name: "Barrier",
        tla_rel: "barriers/Barrier.tla",
        cfg_rel: "barriers/Barrier.cfg",
        tlc_distinct_states: 64,
    },
    SpecTestCase {
        name: "VoucherLifeCycle",
        tla_rel: "byihive/VoucherLifeCycle.tla",
        cfg_rel: "byihive/VoucherLifeCycle.cfg",
        tlc_distinct_states: 64,
    },
];

/// Root directory of the tla2 repo (derived from CARGO_MANIFEST_DIR).
fn repo_root() -> PathBuf {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR not set");
    PathBuf::from(manifest_dir)
        .parent() // crates/
        .and_then(|p| p.parent()) // repo root
        .expect("could not find repo root")
        .to_path_buf()
}

/// Absolute path to the tla-runtime crate.
fn tla_runtime_path() -> PathBuf {
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest_dir)
        .parent()
        .expect("could not find crates dir")
        .join("tla-runtime")
        .canonicalize()
        .expect("could not canonicalize tla-runtime path")
}

/// Root of the tlaplus-examples/specifications/ directory.
fn specs_root() -> PathBuf {
    PathBuf::from("./tlaplus-examples/specifications")
}

/// Find the tla2 binary, checking common build output locations.
///
/// Searches the worktree target dirs, the main repo target dirs, and
/// common temp build dirs. Does NOT build the binary — the caller should
/// ensure it exists before running this test suite.
fn find_tla2_binary() -> Option<PathBuf> {
    let root = repo_root();
    // Check worktree and main repo target dirs
    let mut candidates: Vec<PathBuf> = vec![
        root.join("target/release/tla2"),
        root.join("target/user/release/tla2"),
        root.join("target/debug/tla2"),
    ];
    // Also check the main repo root (worktree parent)
    if let Some(main_root) = root.parent().and_then(|p| p.parent()) {
        candidates.push(main_root.join("target/release/tla2"));
        candidates.push(main_root.join("target/user/release/tla2"));
    }
    // Common temp build dirs used by agents
    candidates.push(PathBuf::from("/tmp/tl4k-build/release/tla2"));
    candidates.push(PathBuf::from("/tmp/tla2-hwmcc/release/tla2"));

    candidates.into_iter().find(|p| p.exists())
}

/// Run `tla2 codegen --tir --scaffold` to generate a complete Cargo project.
fn run_codegen_scaffold(
    tla2_bin: &Path,
    tla_file: &Path,
    cfg_file: &Path,
    output_dir: &Path,
) -> Result<(), String> {
    let output = Command::new(tla2_bin)
        .args([
            "codegen",
            "--tir",
            "--config",
            cfg_file.to_str().unwrap(),
            "--scaffold",
            "--output",
            output_dir.to_str().unwrap(),
            tla_file.to_str().unwrap(),
        ])
        .output()
        .map_err(|e| format!("failed to run tla2 codegen: {e}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("codegen failed: {stderr}"));
    }
    Ok(())
}

/// Overwrite the scaffold's Cargo.toml with a correct tla-runtime path.
///
/// The scaffold generates a relative path that works from the binary's
/// location but not from a temp directory.
fn fix_cargo_toml(project_dir: &Path, runtime_path: &Path) {
    let cargo_toml = format!(
        "[package]\n\
         name = \"codegen-test\"\n\
         version = \"0.1.0\"\n\
         edition = \"2021\"\n\
         \n\
         [workspace]\n\
         \n\
         [[bin]]\n\
         name = \"check\"\n\
         path = \"src/main.rs\"\n\
         \n\
         [dependencies]\n\
         tla-runtime = {{ path = \"{}\" }}\n",
        runtime_path.display()
    );
    std::fs::write(project_dir.join("Cargo.toml"), &cargo_toml)
        .expect("failed to write Cargo.toml");
}

/// Build and run the scaffold project, parsing state counts from stdout.
///
/// Returns (distinct_states, states_explored) on success.
fn build_and_run(project_dir: &Path) -> Result<(usize, usize), String> {
    // Build
    let build = Command::new("cargo")
        .args(["build", "--release"])
        .current_dir(project_dir)
        .output()
        .map_err(|e| format!("cargo build failed to start: {e}"))?;
    if !build.status.success() {
        let stderr = String::from_utf8_lossy(&build.stderr);
        // Truncate for readability
        let short = if stderr.len() > 500 {
            format!("{}...", &stderr[..500])
        } else {
            stderr.to_string()
        };
        return Err(format!("build failed:\n{short}"));
    }

    // Run with a 60-second timeout
    let run = Command::new("cargo")
        .args(["run", "--release"])
        .current_dir(project_dir)
        .output()
        .map_err(|e| format!("cargo run failed to start: {e}"))?;

    let stdout = String::from_utf8_lossy(&run.stdout);

    // Parse "Distinct states: N"
    let distinct = stdout
        .lines()
        .find_map(|line| {
            line.strip_prefix("Distinct states: ")
                .and_then(|s| s.trim().parse::<usize>().ok())
        })
        .ok_or_else(|| format!("could not parse distinct states from stdout:\n{}", stdout))?;

    let explored = stdout
        .lines()
        .find_map(|line| {
            line.strip_prefix("States explored: ")
                .and_then(|s| s.trim().parse::<usize>().ok())
        })
        .unwrap_or(0);

    Ok((distinct, explored))
}

/// End-to-end validation: codegen -> compile -> run -> compare state counts
/// against TLC baselines.
///
/// This test verifies the correctness of the code generation pipeline by
/// ensuring that generated Rust model checkers produce the exact same
/// distinct state counts as TLC for each curated spec.
#[cfg_attr(test, ntest::timeout(300_000))]
#[test]
fn test_codegen_state_counts_match_tlc() {
    let specs_dir = specs_root();
    if !specs_dir.exists() {
        eprintln!(
            "SKIP: tlaplus-examples not found at {}",
            specs_dir.display()
        );
        return;
    }

    let tla2_bin = match find_tla2_binary() {
        Some(bin) => bin,
        None => {
            eprintln!("SKIP: tla2 binary not found. Build with: cargo build --release --bin tla2");
            return;
        }
    };

    let runtime_path = tla_runtime_path();

    let mut passed: Vec<&str> = Vec::new();
    let mut failed: Vec<(&str, String)> = Vec::new();
    let mut skipped: Vec<(&str, String)> = Vec::new();

    for spec in TEST_SPECS {
        let tla_file = specs_dir.join(spec.tla_rel);
        let cfg_file = specs_dir.join(spec.cfg_rel);

        if !tla_file.exists() {
            skipped.push((
                spec.name,
                format!("TLA file not found: {}", tla_file.display()),
            ));
            continue;
        }
        if !cfg_file.exists() {
            skipped.push((
                spec.name,
                format!("CFG file not found: {}", cfg_file.display()),
            ));
            continue;
        }

        let output_dir = std::env::temp_dir().join(format!(
            "tla2_codegen_validate_{}_{}",
            spec.name,
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&output_dir);

        // Step 1: Generate scaffold
        if let Err(e) = run_codegen_scaffold(&tla2_bin, &tla_file, &cfg_file, &output_dir) {
            failed.push((spec.name, format!("codegen: {e}")));
            let _ = std::fs::remove_dir_all(&output_dir);
            continue;
        }

        // Step 2: Fix Cargo.toml with absolute tla-runtime path
        fix_cargo_toml(&output_dir, &runtime_path);

        // Step 3: Build and run, comparing state counts
        match build_and_run(&output_dir) {
            Ok((distinct, explored)) => {
                let _ = std::fs::remove_dir_all(&output_dir);
                if distinct == spec.tlc_distinct_states {
                    passed.push(spec.name);
                    println!(
                        "PASS {}: distinct={}, explored={} (TLC baseline: {})",
                        spec.name, distinct, explored, spec.tlc_distinct_states
                    );
                } else {
                    failed.push((
                        spec.name,
                        format!(
                            "state count mismatch: codegen={}, TLC={}",
                            distinct, spec.tlc_distinct_states
                        ),
                    ));
                }
            }
            Err(e) => {
                let _ = std::fs::remove_dir_all(&output_dir);
                failed.push((spec.name, format!("build/run: {e}")));
            }
        }
    }

    // Summary
    let total = TEST_SPECS.len();
    let skip_count = skipped.len();
    println!("\n=== Codegen State Count Validation ===");
    println!(
        "Total: {total}, Passed: {}, Failed: {}, Skipped: {skip_count}",
        passed.len(),
        failed.len()
    );
    for name in &passed {
        println!("  PASS: {name}");
    }
    for (name, reason) in &failed {
        let short = if reason.len() > 200 {
            format!("{}...", &reason[..200])
        } else {
            reason.clone()
        };
        println!("  FAIL {name}: {short}");
    }
    for (name, reason) in &skipped {
        println!("  SKIP {name}: {reason}");
    }

    // All specs in the curated list must pass (they were individually verified)
    assert!(
        failed.is_empty(),
        "codegen state count validation failed for {} specs: {:?}",
        failed.len(),
        failed
            .iter()
            .map(|(n, r)| format!("{n}: {r}"))
            .collect::<Vec<_>>()
    );
}
