// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;
use common::TempDir;
use std::time::Duration;

fn run_tla(args: &[&str], env: &[(&str, &str)]) -> (i32, String, String) {
    common::run_tla_parsed_with_env_timeout(
        args,
        env,
        &["TLA2_SKIP_LIVENESS"],
        Duration::from_secs(10),
    )
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_skip_liveness_disables_store_states_auto_enable() {
    let dir = TempDir::new("tla2-check-skip-liveness-test");
    let spec = dir.path.join("SkipLiveness.tla");
    let cfg = dir.path.join("SkipLiveness.cfg");

    common::write_file(
        &spec,
        br#"
---- MODULE SkipLiveness ----
EXTENDS Integers

VARIABLE x
vars == <<x>>

Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

SpecProp == Init /\ [][Next]_vars
====
"#,
    );
    common::write_file(
        &cfg,
        b"INIT Init\nNEXT Next\nPROPERTY SpecProp\nCHECK_DEADLOCK FALSE\n",
    );

    let spec_str = spec.to_str().unwrap();
    let cfg_str = cfg.to_str().unwrap();

    // Without TLA2_SKIP_LIVENESS, PROPERTY triggers store-states auto-enable.
    let (code, stdout, stderr) = run_tla(&["check", spec_str, "--config", cfg_str], &[]);
    assert_eq!(
        code, 0,
        "expected success\nstderr:\n{stderr}\nstdout:\n{stdout}"
    );
    assert!(
        stdout.contains("auto-enabled for PROPERTY/liveness checking"),
        "stdout:\n{stdout}"
    );

    // With TLA2_SKIP_LIVENESS=1, we should NOT auto-enable store-states.
    let (code, stdout, stderr) = run_tla(
        &["check", spec_str, "--config", cfg_str],
        &[("TLA2_SKIP_LIVENESS", "1")],
    );
    assert_eq!(
        code, 0,
        "expected success\nstderr:\n{stderr}\nstdout:\n{stdout}"
    );
    assert!(stdout.contains("TLA2_SKIP_LIVENESS=1"), "stdout:\n{stdout}");
    assert!(
        stdout.contains("PROPERTY/liveness checking will be skipped"),
        "stdout:\n{stdout}"
    );
    assert!(
        !stdout.contains("auto-enabled for PROPERTY/liveness checking"),
        "stdout:\n{stdout}"
    );
    assert!(!stdout.contains("Store-states mode:"), "stdout:\n{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_skip_liveness_skips_tautology_rejection() {
    let dir = TempDir::new("tla2-check-skip-liveness-tautology-test");
    let spec = dir.path.join("SkipLivenessTautology.tla");
    let cfg = dir.path.join("SkipLivenessTautology.cfg");

    common::write_file(
        &spec,
        br#"
---- MODULE SkipLivenessTautology ----
VARIABLE x

Init == x = 0
Next == x' = x
Prop == <>TRUE
====
"#,
    );
    common::write_file(
        &cfg,
        b"INIT Init\nNEXT Next\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\n",
    );

    let spec_str = spec.to_str().unwrap();
    let cfg_str = cfg.to_str().unwrap();

    // Baseline: without skip-liveness, tautological property is rejected (EC 2253 parity).
    let (code, stdout, stderr) = run_tla(&["check", spec_str, "--config", cfg_str], &[]);
    assert_ne!(
        code, 0,
        "expected tautology rejection without skip-liveness\nstderr:\n{stderr}\nstdout:\n{stdout}"
    );
    let combined = format!("{stdout}\n{stderr}");
    assert!(
        combined.contains("tautology") || combined.contains("TLC_LIVE_FORMULA_TAUTOLOGY"),
        "expected tautology diagnostic without skip-liveness\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );

    // With TLA2_SKIP_LIVENESS=1, PROPERTY/liveness checks are skipped.
    let (code, stdout, stderr) = run_tla(
        &["check", spec_str, "--config", cfg_str],
        &[("TLA2_SKIP_LIVENESS", "1")],
    );
    assert_eq!(
        code, 0,
        "expected success with skip-liveness\nstderr:\n{stderr}\nstdout:\n{stdout}"
    );
    assert!(stdout.contains("TLA2_SKIP_LIVENESS=1"), "stdout:\n{stdout}");
    assert!(
        stdout.contains("PROPERTY/liveness checking will be skipped"),
        "stdout:\n{stdout}"
    );
}
