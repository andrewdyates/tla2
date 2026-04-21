// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for stray SAT preprocess diagnostics leaking into normal CHC CLI output.

use ntest::timeout;
use std::process::Command;

#[test]
#[timeout(30_000)]
fn test_chc_cli_output_excludes_preprocess_diagnostics_5970() {
    let z4_path = env!("CARGO_BIN_EXE_z4");
    let benchmark_path = format!(
        "{}/../../benchmarks/chc-comp/2025/extra-small-lia/const_mod_1_000.smt2",
        env!("CARGO_MANIFEST_DIR")
    );

    let output = Command::new(z4_path)
        .arg("--chc")
        .arg(&benchmark_path)
        .output()
        .expect("Failed to spawn z4");

    assert!(
        output.status.success(),
        "Expected zero exit status, got {:?}",
        output.status
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(
        stdout.trim(),
        "sat",
        "Expected clean CHC stdout with only the result, got stdout={stdout:?} stderr={stderr:?}"
    );

    for marker in [
        "[preprocess-breakdown]",
        "[preprocess-phases]",
        "[preprocess-final]",
        "c preprocess:",
    ] {
        assert!(
            !stderr.contains(marker),
            "Expected no SAT preprocess diagnostics on stderr, found {marker:?} in {stderr:?}"
        );
    }
}
