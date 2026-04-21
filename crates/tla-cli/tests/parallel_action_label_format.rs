// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CLI integration test: parallel action labels use line/col format (not byte offsets).
//!
//! Part of #2920, Part of #2470: When running with `--workers 2 --continue-on-error`,
//! the parallel checker must resolve action labels to `line N, col N to line N, col N`
//! format. This requires `register_files_and_spec!` to be called in the parallel path
//! so FileId → path resolution is available for span-to-line/col conversion.

mod common;
use common::TempDir;
use std::time::Duration;

const ACTION_LABEL_SPEC: &[u8] = br#"
---- MODULE ActionLabels ----
EXTENDS Naturals
VARIABLES x, y

Init ==
    /\ x = 0
    /\ y = 0

IncrementX ==
    /\ x < 5
    /\ x' = x + 1
    /\ y' = y

IncrementY ==
    /\ y < 3
    /\ y' = y + 1
    /\ x' = x

Reset ==
    /\ x > 2
    /\ x' = 0
    /\ y' = 0

Next == IncrementX \/ IncrementY \/ Reset

Bound == x <= 3
====
"#;

const ACTION_LABEL_CFG: &[u8] = b"INIT Init\nNEXT Next\nINVARIANT Bound\nCHECK_DEADLOCK FALSE\n";

fn run_tla(args: &[&str]) -> (i32, String, String) {
    common::run_tla_parsed_with_timeout(args, Duration::from_secs(90))
}

/// Check if output contains an action label with line/col format for the given module.
fn has_line_col_action_label(output: &str, module_name: &str) -> bool {
    let suffix = format!("of module {module_name}>");
    output.lines().any(|line| {
        line.contains(&suffix)
            && line.contains(" line ")
            && line.contains(" col ")
            && line.contains(" to ")
    })
}

/// Write the shared spec+config and return (spec_path, cfg_path) as strings.
fn setup_spec(dir: &TempDir) -> (String, String) {
    let spec = dir.path.join("ActionLabels.tla");
    let cfg = dir.path.join("ActionLabels.cfg");
    common::write_file(&spec, ACTION_LABEL_SPEC);
    common::write_file(&cfg, ACTION_LABEL_CFG);
    (
        spec.to_str().expect("utf8 spec path").to_string(),
        cfg.to_str().expect("utf8 cfg path").to_string(),
    )
}

/// Assert the output contains invariant violation with line/col action labels.
fn assert_action_label_format(output: &str, stdout: &str, stderr: &str) {
    assert!(
        output.contains("Invariant Bound is violated"),
        "expected 'Invariant Bound is violated'\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        has_line_col_action_label(output, "ActionLabels"),
        "action labels must use 'line N, col N to line N, col N of module' format\n\
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        !output.contains("offset "),
        "byte offset format must not appear in action labels\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// Verify parallel mode (--workers 2 --continue-on-error) produces action labels
/// with `line N, col N` format. Without register_files_and_spec! in the parallel
/// path (#2920), labels would show byte offsets or "unknown".
#[cfg_attr(test, ntest::timeout(180000))]
#[test]
fn parallel_action_labels_show_line_col_format() {
    let dir = TempDir::new("tla2-par-action-labels");
    let (spec, cfg) = setup_spec(&dir);

    let (code, stdout, stderr) = run_tla(&[
        "check",
        &spec,
        "--config",
        &cfg,
        "--workers",
        "2",
        "--continue-on-error",
    ]);
    let output = format!("{stdout}\n{stderr}");

    assert_ne!(
        code, 0,
        "expected invariant violation\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        output.contains("Mode: parallel (2 workers)"),
        "expected parallel mode with --continue-on-error\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_action_label_format(&output, &stdout, &stderr);
}

/// Verify sequential mode also uses line/col format for action labels (baseline parity).
#[cfg_attr(test, ntest::timeout(180000))]
#[test]
fn sequential_action_labels_show_line_col_format() {
    let dir = TempDir::new("tla2-seq-action-labels");
    let (spec, cfg) = setup_spec(&dir);

    let (code, stdout, stderr) = run_tla(&["check", &spec, "--config", &cfg, "--workers", "1"]);
    let output = format!("{stdout}\n{stderr}");

    assert_ne!(
        code, 0,
        "expected invariant violation\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_action_label_format(&output, &stdout, &stderr);
}
