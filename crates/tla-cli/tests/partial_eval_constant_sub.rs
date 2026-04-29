// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration test for `--partial-eval` flag (Part of #4251 Stream 5).
//!
//! Verifies that:
//! 1. `--partial-eval` successfully drives a model check to completion with
//!    `CONSTANT N = 3` substituted at TIR preprocess time.
//! 2. State counts with and without `--partial-eval` are identical
//!    (correctness: partial eval must be an optimization, never a behavior
//!    change).
//!
//! The TIR-level substitution semantics are covered by nine unit tests in
//! `tla-tir/src/analysis/partial_eval.rs`. This test exercises the CLI
//! plumbing that wires `.cfg` CONSTANT bindings into the `ConstantEnv` for
//! `TirProgram`, the env-var gate (`TLA2_PARTIAL_EVAL=1`), and the actual
//! `preprocess_operator` / `try_eval_expr_detailed` entry points.

mod common;

use std::time::Duration;

const SPEC: &str = r#"---- MODULE PartialEvalFixture ----
EXTENDS Naturals
CONSTANT N
VARIABLE x

Init == x = 0
Next == x' = (x + 1) % N
Inv == x < N
====
"#;

const CFG: &str = r#"CONSTANT N = 3
INIT Init
NEXT Next
INVARIANT Inv
"#;

fn extract_state_count(stdout: &str) -> Option<u64> {
    // `tla2 check` prints a "Statistics:" block containing a line like
    // "  States found: 3". Match on that exact prefix to avoid collisions with
    // other lines such as "Initial states: 1".
    for line in stdout.lines() {
        let trimmed = line.trim_start();
        if let Some(rest) = trimmed.strip_prefix("States found:") {
            let num: String = rest
                .trim_start()
                .chars()
                .take_while(|c| c.is_ascii_digit())
                .collect();
            if let Ok(n) = num.parse::<u64>() {
                return Some(n);
            }
        }
    }
    None
}

#[test]
fn partial_eval_flag_preserves_state_count() {
    let dir = common::TempDir::new("partial-eval-fixture");
    let (spec_path, cfg_path) =
        common::write_spec_and_config(&dir, "PartialEvalFixture", SPEC, CFG);
    let spec_arg = spec_path.to_str().expect("spec path utf8");
    let cfg_arg = cfg_path.to_str().expect("cfg path utf8");

    // Baseline run: partial-eval OFF.
    let (baseline_code, baseline_stdout, baseline_stderr) = common::run_tla_parsed_with_env_timeout(
        &["check", spec_arg, "--config", cfg_arg, "--workers", "1"],
        &[],
        &["TLA2_PARTIAL_EVAL"],
        Duration::from_secs(60),
    );
    assert_eq!(
        baseline_code, 0,
        "baseline check failed: code={baseline_code}\nstdout:\n{baseline_stdout}\nstderr:\n{baseline_stderr}"
    );
    let baseline_states = extract_state_count(&baseline_stdout).unwrap_or_else(|| {
        panic!("could not extract state count from baseline stdout:\n{baseline_stdout}")
    });

    // Partial-eval run: --partial-eval ON.
    let (pe_code, pe_stdout, pe_stderr) = common::run_tla_parsed_with_env_timeout(
        &[
            "check",
            spec_arg,
            "--config",
            cfg_arg,
            "--workers",
            "1",
            "--partial-eval",
        ],
        &[],
        &[],
        Duration::from_secs(60),
    );
    assert_eq!(
        pe_code, 0,
        "--partial-eval check failed: code={pe_code}\nstdout:\n{pe_stdout}\nstderr:\n{pe_stderr}"
    );
    let pe_states = extract_state_count(&pe_stdout).unwrap_or_else(|| {
        panic!("could not extract state count from --partial-eval stdout:\n{pe_stdout}")
    });

    assert_eq!(
        baseline_states, pe_states,
        "state count mismatch: baseline={baseline_states}, --partial-eval={pe_states}.\nbaseline stdout:\n{baseline_stdout}\n--partial-eval stdout:\n{pe_stdout}",
    );
    // Spec has N=3 successor states (0 -> 1 -> 2 -> 0): we expect 3 distinct
    // reachable states. Guard against regressions in either path.
    assert_eq!(
        pe_states, 3,
        "PartialEvalFixture with N=3 should enumerate exactly 3 states, got {pe_states}"
    );
}
