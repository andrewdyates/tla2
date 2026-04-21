// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::process::Command;

mod common;
use common::TempDir;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn simulate_loads_standalone_instance_modules() {
    let dir = TempDir::new("tla2-simulate-instance-modules");

    let main = dir.path.join("Main.tla");
    let inst = dir.path.join("InstMod.tla");
    let cfg = dir.path.join("Main.cfg");

    common::write_file(
        &main,
        br#"
---- MODULE Main ----
INSTANCE InstMod

VARIABLE x
vars == <<x>>

Init == x = 0
Next == x' = Inc(x)
====
"#,
    );

    common::write_file(
        &inst,
        br#"
---- MODULE InstMod ----
EXTENDS Naturals
Inc(v) == v + 1
====
"#,
    );

    common::write_file(&cfg, b"INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n");

    let bin = env!("CARGO_BIN_EXE_tla2");
    let out = Command::new(bin)
        .args([
            "simulate",
            main.to_str().expect("utf-8 main path"),
            "--config",
            cfg.to_str().expect("utf-8 cfg path"),
            "--num-traces",
            "1",
            "--max-trace-length",
            "2",
            "--seed",
            "1",
        ])
        .output()
        .expect("run tla2 simulate");

    assert!(
        out.status.success(),
        "expected success\nexit code: {code:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        code = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("Simulation complete: No errors found."),
        "stdout:\n{stdout}"
    );
    assert!(stdout.contains("Traces generated: 1"), "stdout:\n{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn check_simulate_flag_loads_standalone_instance_modules() {
    let dir = TempDir::new("tla2-check-simulate-instance-modules");

    let main = dir.path.join("Main.tla");
    let inst = dir.path.join("InstMod.tla");
    let cfg = dir.path.join("Main.cfg");

    common::write_file(
        &main,
        br#"
---- MODULE Main ----
INSTANCE InstMod

VARIABLE x
vars == <<x>>

Init == x = 0
Next == x' = Inc(x)
====
"#,
    );

    common::write_file(
        &inst,
        br#"
---- MODULE InstMod ----
EXTENDS Naturals
Inc(v) == v + 1
====
"#,
    );

    common::write_file(&cfg, b"INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n");

    let bin = env!("CARGO_BIN_EXE_tla2");
    let out = Command::new(bin)
        .args([
            "check",
            "--simulate",
            main.to_str().expect("utf-8 main path"),
            "--config",
            cfg.to_str().expect("utf-8 cfg path"),
        ])
        .output()
        .expect("run tla2 check --simulate");

    assert!(
        out.status.success(),
        "expected success\nexit code: {code:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        code = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("Simulation complete: No errors found."),
        "stdout:\n{stdout}"
    );
}
