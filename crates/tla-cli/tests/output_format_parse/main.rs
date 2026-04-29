// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[path = "../common/mod.rs"]
mod common;
mod errors;
mod helpers;

use helpers::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_json_parses() {
    let out = run_check("json");
    assert_success(&out);
    let _ = parse_json(&out);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_jsonl_parses() {
    let out = run_check("jsonl");
    assert_success(&out);
    let _ = parse_json_lines(&out);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_json_lines_alias_parses() {
    let out = run_check("json-lines");
    assert_success(&out);
    let _ = parse_json_lines(&out);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_unknown_format_emits_clap_error_to_stderr() {
    let out = run_check("definitely-not-a-real-output-format");
    assert_failure(&out);
    assert_exit_code_2(&out, "unknown output format");
    assert!(
        String::from_utf8_lossy(&out.stdout).trim().is_empty(),
        "expected clap error to keep stdout empty\nstdout:\n{stdout}\nstderr:\n{stderr}",
        stdout = String::from_utf8_lossy(&out.stdout),
        stderr = String::from_utf8_lossy(&out.stderr),
    );
    assert!(
        !out.stderr.is_empty(),
        "expected clap error to emit stderr\nstdout:\n{stdout}\nstderr:\n{stderr}",
        stdout = String::from_utf8_lossy(&out.stdout),
        stderr = String::from_utf8_lossy(&out.stderr),
    );
}
