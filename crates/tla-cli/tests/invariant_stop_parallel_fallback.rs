// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

mod common;
use common::TempDir;
use std::time::Duration;

fn run_tla(args: &[&str]) -> (i32, String, String) {
    common::run_tla_parsed_with_timeout(args, Duration::from_secs(90))
}

/// Part of #3058: Explicit --workers N now runs parallel even with invariants.
/// Auto mode (--workers 0) still forces sequential for TLC parity.
/// This test verifies that --workers 2 actually runs in parallel mode and
/// still finds the invariant violation.
#[cfg_attr(test, ntest::timeout(180000))]
#[test]
fn invariant_stop_workers_gt1_runs_parallel_finds_violation() {
    let dir = TempDir::new("tla2-invariant-stop-parallel");
    let spec = dir.path.join("InvariantStopParallel.tla");
    let cfg = dir.path.join("InvariantStopParallel.cfg");

    common::write_file(
        &spec,
        br#"
---- MODULE InvariantStopParallel ----
VARIABLES p, d, x

Init ==
    /\ p \in {0, 1}
    /\ d = 0
    /\ x = 0

Next ==
    \/ /\ p = 0
       /\ d < 5
       /\ p' = 0
       /\ d' = d + 1
       /\ x' = 0
    \/ /\ p = 1
       /\ d = 0
       /\ p' = 1
       /\ d' = 1
       /\ x' \in 1..10

NoDeepPath == ~(p = 0 /\ d = 5)
TypeOK == /\ p \in {0, 1}
          /\ d \in 0..5
          /\ x \in 0..10
====
"#,
    );
    common::write_file(
        &cfg,
        b"INIT Init\nNEXT Next\nINVARIANT TypeOK\nINVARIANT NoDeepPath\nCHECK_DEADLOCK FALSE\n",
    );

    let spec_str = spec.to_str().expect("utf8 spec path");
    let cfg_str = cfg.to_str().expect("utf8 cfg path");

    // Sequential (--workers 1) should find the invariant violation
    let (seq_code, seq_stdout, seq_stderr) =
        run_tla(&["check", spec_str, "--config", cfg_str, "--workers", "1"]);
    assert_ne!(
        seq_code, 0,
        "expected invariant violation in sequential mode\nstdout:\n{seq_stdout}\nstderr:\n{seq_stderr}"
    );

    // Parallel (--workers 2) should run in parallel and also find the violation
    let (par_code, par_stdout, par_stderr) =
        run_tla(&["check", spec_str, "--config", cfg_str, "--workers", "2"]);
    assert_ne!(
        par_code, 0,
        "expected invariant violation in workers=2 mode\nstdout:\n{par_stdout}\nstderr:\n{par_stderr}"
    );

    let par_output = format!("{par_stdout}\n{par_stderr}");

    // With #3058 fix: --workers 2 should actually run parallel, not force sequential
    assert!(
        par_output.contains("Mode: parallel (2 workers)"),
        "workers=2 should run in parallel mode after #3058 fix\nstdout:\n{par_stdout}\nstderr:\n{par_stderr}"
    );
    assert!(
        !par_output.contains("forced for invariant-stop"),
        "workers=2 should NOT be forced sequential\nstdout:\n{par_stdout}\nstderr:\n{par_stderr}"
    );

    // Both should find NoDeepPath violation
    assert!(
        par_output.contains("NoDeepPath"),
        "parallel mode should find the NoDeepPath invariant violation\nstdout:\n{par_stdout}\nstderr:\n{par_stderr}"
    );
}

/// Part of #3058: Auto mode (no --workers flag) should still force sequential
/// for specs with invariants, preserving TLC parity for default usage.
#[cfg_attr(test, ntest::timeout(180000))]
#[test]
fn invariant_stop_auto_mode_forces_sequential_tlc_parity() {
    let dir = TempDir::new("tla2-invariant-stop-auto");
    let spec = dir.path.join("InvariantStopAuto.tla");
    let cfg = dir.path.join("InvariantStopAuto.cfg");

    common::write_file(
        &spec,
        br#"
---- MODULE InvariantStopAuto ----
VARIABLES p, d

Init ==
    /\ p \in {0, 1}
    /\ d = 0

Next ==
    \/ /\ p = 0
       /\ d < 5
       /\ p' = 0
       /\ d' = d + 1
    \/ /\ p = 1
       /\ d = 0
       /\ p' = 1
       /\ d' = 1

NoDeepPath == ~(p = 0 /\ d = 5)
====
"#,
    );
    common::write_file(
        &cfg,
        b"INIT Init\nNEXT Next\nINVARIANT NoDeepPath\nCHECK_DEADLOCK FALSE\n",
    );

    let spec_str = spec.to_str().expect("utf8 spec path");
    let cfg_str = cfg.to_str().expect("utf8 cfg path");

    // Auto mode (no --workers) should force sequential for invariant specs
    let (_code, auto_stdout, auto_stderr) = run_tla(&["check", spec_str, "--config", cfg_str]);
    let auto_output = format!("{auto_stdout}\n{auto_stderr}");

    assert!(
        auto_output.contains("Mode: sequential (auto: invariant-stop TLC parity)"),
        "auto mode should force sequential for invariant specs\nstdout:\n{auto_stdout}\nstderr:\n{auto_stderr}"
    );
}
