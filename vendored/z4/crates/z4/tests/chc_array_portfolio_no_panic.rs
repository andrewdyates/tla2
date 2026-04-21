// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;

fn workspace_root() -> PathBuf {
    PathBuf::from(
        env!("CARGO_MANIFEST_DIR")
            .strip_suffix("/crates/z4")
            .unwrap_or(env!("CARGO_MANIFEST_DIR")),
    )
}

fn local_chc_benchmark(path: &str) -> PathBuf {
    workspace_root().join(path)
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(30_000))]
fn test_chc_array_bv_safe_benchmark_has_no_portfolio_panic() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let benchmark = local_chc_benchmark("benchmarks/chc/array_bv_safe.smt2");

    assert!(
        benchmark.exists(),
        "Expected benchmark at {}",
        benchmark.display()
    );

    let output = Command::new(z4_path)
        .arg("--chc")
        .arg(&benchmark)
        .arg("-t:15000")
        .output()
        .expect("failed to spawn z4 on array CHC benchmark");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let first_line = stdout.lines().next().unwrap_or("").trim();

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        stdout,
        stderr
    );
    assert_eq!(
        first_line, "sat",
        "Expected sat for array_bv_safe benchmark\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("panicked") && !stderr.contains("BUG:"),
        "CHC portfolio emitted an internal panic on array_bv_safe\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
