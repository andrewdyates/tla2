// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::process::Command;

use serde_json::Value;

mod common;
use common::TempDir;

fn run_tla(args: &[&str]) -> std::process::Output {
    let bin = env!("CARGO_BIN_EXE_tla2");
    Command::new(bin)
        .args(args)
        .env_remove("TLA2_SKIP_LIVENESS")
        .output()
        .expect("spawn tla2")
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn no_trace_property_json_keeps_soundness_clean() {
    let dir = TempDir::new("tla2-check-no-trace-soundness");
    let spec = dir.path.join("NoTraceSoundness.tla");
    let cfg = dir.path.join("NoTraceSoundness.cfg");

    common::write_file(
        &spec,
        br#"
---- MODULE NoTraceSoundness ----
EXTENDS Integers

VARIABLE x

Init == x = 0
Next == UNCHANGED x
Progress == <>(x = 1)
====
"#,
    );
    common::write_file(
        &cfg,
        b"INIT Init\nNEXT Next\nPROPERTY Progress\nCHECK_DEADLOCK FALSE\n",
    );

    let out = run_tla(&[
        "check",
        spec.to_str().expect("utf-8 spec path"),
        "--config",
        cfg.to_str().expect("utf-8 cfg path"),
        "--workers",
        "1",
        "--no-trace",
        "--output",
        "json",
    ]);

    assert!(
        !out.status.success(),
        "expected liveness violation with no-trace/property run\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let json: Value = serde_json::from_slice(&out.stdout).unwrap_or_else(|err| {
        panic!(
            "expected JSON output: {err}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        )
    });
    let soundness = json
        .get("soundness")
        .and_then(Value::as_object)
        .unwrap_or_else(|| panic!("missing soundness object: {json:#?}"));
    let features = soundness
        .get("features_used")
        .and_then(Value::as_array)
        .unwrap_or_else(|| panic!("missing soundness.features_used: {json:#?}"));
    assert!(
        !features.iter().any(|f| f == "no_trace"),
        "did not expect no_trace feature marker\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    let deviations = soundness
        .get("deviations")
        .and_then(Value::as_array)
        .unwrap_or_else(|| panic!("missing soundness.deviations: {json:#?}"));
    assert!(
        !deviations
            .iter()
            .filter_map(Value::as_str)
            .any(|d| d.contains("--no-trace") && d.contains("PROPERTY/liveness")),
        "did not expect no-trace/property soundness deviation\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn no_trace_property_human_output_reports_trace_tradeoff_without_liveness_warning() {
    let dir = TempDir::new("tla2-check-no-trace-human-warning");
    let spec = dir.path.join("NoTraceHumanWarning.tla");
    let cfg = dir.path.join("NoTraceHumanWarning.cfg");

    common::write_file(
        &spec,
        br#"
---- MODULE NoTraceHumanWarning ----
EXTENDS Integers

VARIABLE x

Init == x = 0
Next == UNCHANGED x
Progress == <>(x = 1)
====
"#,
    );
    common::write_file(
        &cfg,
        b"INIT Init\nNEXT Next\nPROPERTY Progress\nCHECK_DEADLOCK FALSE\n",
    );

    let out = run_tla(&[
        "check",
        spec.to_str().expect("utf-8 spec path"),
        "--config",
        cfg.to_str().expect("utf-8 cfg path"),
        "--workers",
        "1",
        "--no-trace",
    ]);

    assert!(
        !out.status.success(),
        "expected liveness violation with no-trace/property run\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stdout.contains("Requested --no-trace:")
            && stdout.contains("safety counterexample traces may be unavailable"),
        "expected updated no-trace status line in stdout\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
    assert!(
        !stderr.contains("--no-trace disables liveness checking"),
        "did not expect stale no-trace liveness warning in stderr\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn no_trace_symmetry_liveness_reports_full_state_auto_enable() {
    let dir = TempDir::new("tla2-check-no-trace-symmetry-liveness");
    let spec = dir.path.join("NoTraceSymmetryLiveness.tla");
    let cfg = dir.path.join("NoTraceSymmetryLiveness.cfg");

    // Use model values for symmetry (TLC rejects integer symmetry:
    // "Symmetry function must have model values as domain and range").
    // The property <>[](x \in {M1, M2}) holds trivially since x is always
    // in {M1, M2}, even on stuttering paths (no fairness needed).
    common::write_file(
        &spec,
        br#"
---- MODULE NoTraceSymmetryLiveness ----
EXTENDS TLC

CONSTANT M1, M2

VARIABLE x

Sym == Permutations({M1, M2})

Init == x \in {M1, M2}
Next == IF x = M1 THEN x' = M2 ELSE x' = M1
Progress == <>[](x \in {M1, M2})
====
"#,
    );
    common::write_file(
        &cfg,
        b"INIT Init\nNEXT Next\nPROPERTY Progress\nSYMMETRY Sym\nCHECK_DEADLOCK FALSE\nCONSTANTS\nM1 = M1\nM2 = M2\n",
    );

    let out = run_tla(&[
        "check",
        spec.to_str().expect("utf-8 spec path"),
        "--config",
        cfg.to_str().expect("utf-8 cfg path"),
        "--workers",
        "1",
        "--no-trace",
    ]);

    assert!(
        out.status.success(),
        "expected symmetry+liveness run to succeed with no-trace auto-upgrade\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stdout.contains("Store-states mode: full states in memory")
            && stdout.contains("auto-enabled for PROPERTY/liveness checking"),
        "expected full-state auto-enable message in stdout\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
    assert!(
        !stdout.contains("Requested --no-trace:"),
        "did not expect the plain no-trace status line once the checker auto-upgrades to full-state mode\nstdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );
}
