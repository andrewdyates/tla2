// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::process::Command;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn tla2_trace_validate_help_mentions_input_format() {
    let bin = env!("CARGO_BIN_EXE_tla2");
    let out = Command::new(bin)
        .args(["trace", "validate", "--help"])
        .output()
        .expect("run tla2 trace validate --help");
    assert!(
        out.status.success(),
        "expected exit code 0, got {status:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        status = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("Usage: tla2 trace validate"), "{stdout}");
    assert!(stdout.contains("--input-format"), "{stdout}");
    assert!(stdout.contains("[default: auto]"), "{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn tla2_trace_help_mentions_validate_subcommand() {
    let bin = env!("CARGO_BIN_EXE_tla2");
    let out = Command::new(bin)
        .args(["trace", "--help"])
        .output()
        .expect("run tla2 trace --help");
    assert!(
        out.status.success(),
        "expected exit code 0, got {status:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        status = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("Usage: tla2 trace"), "{stdout}");
    assert!(stdout.contains("validate"), "{stdout}");
}
