// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;
use std::process::Command;

mod common;
use common::TempDir;

fn write_spec_and_config(dir: &TempDir) -> (PathBuf, PathBuf) {
    let spec = dir.path.join("Tmp.tla");
    let cfg = dir.path.join("Tmp.cfg");

    std::fs::write(
        &spec,
        r#"---- MODULE Tmp ----
EXTENDS TLC
VARIABLES x, y

Init ==
    /\ x = Print({"a", "a"}, {"b", "b"})
    /\ y = PrintT({"c", "c"})
Next ==
    /\ x' = x
    /\ y' = y
====
"#,
    )
    .expect("write spec");

    std::fs::write(
        &cfg,
        r#"INIT Init
NEXT Next
"#,
    )
    .expect("write cfg");

    (spec, cfg)
}

fn run_check() -> std::process::Output {
    let dir = TempDir::new("tla-cli-tlc-print-output");
    let (spec, cfg) = write_spec_and_config(&dir);

    let bin = env!("CARGO_BIN_EXE_tla2");
    Command::new(bin)
        .args([
            "check",
            spec.to_str().expect("utf-8 spec path"),
            "--config",
            cfg.to_str().expect("utf-8 cfg path"),
            "--no-deadlock",
            "--max-depth",
            "1",
            "--max-states",
            "1",
            "--output",
            "json",
        ])
        .output()
        .expect("run tla check")
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn tlc_print_goes_to_stderr_and_prints_both_args() {
    let out = run_check();
    assert!(
        out.status.success(),
        "expected exit code 0, got {status:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        status = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    // Ensure `--output json` stays parseable (TLC!Print must not write to stdout).
    //
    // Note: Java TLC prints `TLC!Print` output to stdout in SYSTEM mode; tla2 intentionally routes it
    // to stderr so `--output json` keeps stdout as valid JSON.
    let stdout = std::str::from_utf8(&out.stdout).expect("stdout must be utf-8");
    serde_json::from_str::<serde_json::Value>(stdout.trim()).unwrap_or_else(|e| {
        panic!(
            "expected stdout to be valid JSON: {e}\nstderr:\n{stderr}\nstdout:\n{stdout}",
            stderr = String::from_utf8_lossy(&out.stderr),
            stdout = stdout,
        )
    });

    let stderr = String::from_utf8_lossy(&out.stderr);
    let mut lines: Vec<&str> = Vec::new();
    for line in stderr.lines() {
        lines.push(line.trim_end_matches('\r'));
    }
    let has_line = |expected: &str| lines.contains(&expected);
    assert!(
        has_line("{\"a\"}  {\"b\"}"),
        "expected TLC!Print line to be present\nstderr:\n{stderr}",
    );
    assert!(
        has_line("{\"c\"}"),
        "expected TLC!PrintT line to be present\nstderr:\n{stderr}",
    );
    assert!(
        !stderr.contains("TLC Print:"),
        "unexpected legacy TLC Print prefix still present\nstderr:\n{stderr}",
    );
}
