// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
}

fn mcc_model_dir(model: &str) -> PathBuf {
    workspace_root()
        .join("benchmarks")
        .join("mcc")
        .join("2024")
        .join("INPUTS")
        .join(model)
}

fn has_mcc_benchmark(model: &str) -> bool {
    mcc_model_dir(model).join("model.pnml").exists()
}

fn reachability_fireability_registry(model: &str, index: usize) -> bool {
    let path = workspace_root()
        .join("registry")
        .join("mcc-labels")
        .join("reachability-fireability-2024.csv");
    let contents = fs::read_to_string(path).expect("reachability-fireability registry should read");
    let needle = format!("{model}/{index},");
    let line = contents
        .lines()
        .find(|line| line.starts_with(&needle))
        .unwrap_or_else(|| panic!("registry should contain {model}/{index}"));
    match line
        .split_once(',')
        .expect("registry row should contain a comma")
        .1
    {
        "true" => true,
        "false" => false,
        other => panic!("unexpected registry verdict {other} for {model}/{index}"),
    }
}

fn assert_stdout_contains_formula(stdout: &str, formula_id: &str, expected: bool) {
    let verdict = if expected { "TRUE" } else { "FALSE" };
    let expected_line = format!("FORMULA {formula_id} {verdict} TECHNIQUES EXPLICIT");
    assert!(
        stdout.contains(&expected_line),
        "stdout should contain `{expected_line}`, got:\n{stdout}"
    );
}

#[test]
fn test_cryptominer_cli_traces_kinduction_and_matches_registry() {
    const MODEL: &str = "CryptoMiner-PT-D03N100";
    const EF_FALSE_FORMULA: &str = "CryptoMiner-PT-D03N100-ReachabilityFireability-2024-00";
    const AG_TRUE_FORMULA: &str = "CryptoMiner-PT-D03N100-ReachabilityFireability-2024-09";

    if !has_mcc_benchmark(MODEL) {
        eprintln!("SKIP: {MODEL} benchmark not downloaded");
        return;
    }

    let trace_filter = format!("{EF_FALSE_FORMULA},{AG_TRUE_FORMULA}");
    let output = Command::new(env!("CARGO_BIN_EXE_pnml-tools"))
        .arg("--examination")
        .arg("ReachabilityFireability")
        .arg("--timeout")
        .arg("20")
        .arg("--max-states")
        .arg("50000")
        .arg(mcc_model_dir(MODEL))
        .env("PNML_REACH_TRACE", &trace_filter)
        .output()
        .expect("pnml-tools should run on CryptoMiner benchmark");

    assert!(
        output.status.success(),
        "pnml-tools should succeed: stdout={}, stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8(output.stdout).expect("stdout should be utf-8");
    let stderr = String::from_utf8(output.stderr).expect("stderr should be utf-8");

    assert!(
        stderr.contains(&format!(
            "REACH-TRACE property={EF_FALSE_FORMULA} phase=Kinduction verdict=FALSE depth=1"
        )),
        "stderr should trace {EF_FALSE_FORMULA} through kinduction, got:\n{stderr}"
    );
    assert!(
        stderr.contains(&format!(
            "REACH-TRACE property={AG_TRUE_FORMULA} phase=Kinduction verdict=TRUE depth=1"
        )),
        "stderr should trace {AG_TRUE_FORMULA} through kinduction, got:\n{stderr}"
    );

    assert_stdout_contains_formula(
        &stdout,
        EF_FALSE_FORMULA,
        reachability_fireability_registry(MODEL, 0),
    );
    assert_stdout_contains_formula(
        &stdout,
        AG_TRUE_FORMULA,
        reachability_fireability_registry(MODEL, 9),
    );
}
