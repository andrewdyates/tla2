// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::io::Write;
use std::path::Path;
use std::time::Duration;

mod common;
use common::TempDir;

fn run_tla(args: &[&str]) -> (i32, String, String) {
    common::run_tla_parsed_with_timeout(args, Duration::from_secs(10))
}

fn run_tla_with_stdin(args: &[&str], stdin_bytes: &[u8]) -> (i32, String, String) {
    let bin = env!("CARGO_BIN_EXE_tla2");
    let mut child = std::process::Command::new(bin)
        .args(args)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("spawn tla2");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(stdin_bytes)
        .expect("write stdin");
    let output = child.wait_with_output().expect("wait for tla2");
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
    )
}

fn assert_failed(code: i32, stderr: &str, must_contain: &[&str]) {
    assert_ne!(
        code, 0,
        "expected failure, got exit code 0\nstderr:\n{stderr}"
    );
    for needle in must_contain {
        assert!(
            stderr.contains(needle),
            "stderr did not contain {needle:?}\nstderr:\n{stderr}"
        );
    }
}

fn assert_stderr_contains_path(stderr: &str, path: &str) {
    assert!(
        stderr.contains(path),
        "stderr did not contain expected path {path:?}\nstderr:\n{stderr}"
    );
}

fn write_action_label_spec_files(dir: &TempDir) -> (std::path::PathBuf, std::path::PathBuf) {
    let spec_path = dir.path.join("ActionSpec.tla");
    let cfg_path = dir.path.join("ActionSpec.cfg");
    common::write_file(
        &spec_path,
        br#"---- MODULE ActionSpec ----
VARIABLE x

Init == x = 0

LearnLemma == x = 0 /\ x' = 1
PropagateLemmas == x = 0 /\ x' = 2

Next == LearnLemma \/ PropagateLemmas
====
"#,
    );
    common::write_file(
        &cfg_path,
        br#"INIT Init
NEXT Next
"#,
    );
    (spec_path, cfg_path)
}

fn write_two_step_trace(path: &Path, action_name: Option<&str>) {
    let action_fragment = action_name
        .map(|name| format!(r#","action":{{"name":"{name}"}}"#))
        .unwrap_or_default();
    let trace = format!(
        r#"{{"version":"1","module":"ActionSpec","variables":["x"],"steps":[{{"index":0,"state":{{"x":{{"type":"int","value":0}}}}}},{{"index":1,"state":{{"x":{{"type":"int","value":2}}}}{action_fragment}}}]}}"#
    );
    common::write_file(path, trace.as_bytes());
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_auto_prefers_jsonl_by_extension() {
    let dir = TempDir::new("tla2-trace-validate-test");
    let path = dir.path.join("trace.jsonl");
    common::write_file(
        &path,
        br#"{"type":"header","version":"1","module":"Spec","variables":["x"]}
{"type":"step","index":0,"state":{"x":{"type":"int","value":1}}}
"#,
    );

    let (code, stdout, stderr) = run_tla(&["trace", "validate", path.to_str().unwrap()]);
    assert_eq!(code, 0, "stderr:\n{stderr}\nstdout:\n{stdout}");
    assert!(stdout.contains("OK: parsed 1 steps"), "{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_auto_prefers_jsonl_by_extension_case_insensitive() {
    let dir = TempDir::new("tla2-trace-validate-test");
    let path = dir.path.join("trace.JSONL");
    common::write_file(
        &path,
        br#"{"type":"header","version":"1","module":"Spec","variables":["x"]}
{"type":"step","index":0,"state":{"x":{"type":"int","value":1}}}
"#,
    );

    let (code, stdout, stderr) = run_tla(&["trace", "validate", path.to_str().unwrap()]);
    assert_eq!(code, 0, "stderr:\n{stderr}\nstdout:\n{stdout}");
    assert!(stdout.contains("OK: parsed 1 steps"), "{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_auto_falls_back_to_json() {
    let dir = TempDir::new("tla2-trace-validate-test");
    let path = dir.path.join("trace.json");
    common::write_file(
        &path,
        br#"{"version":"1","module":"Spec","variables":["x"],"steps":[{"index":0,"state":{"x":{"type":"int","value":1}}}]}"#,
    );

    let (code, stdout, stderr) = run_tla(&["trace", "validate", path.to_str().unwrap()]);
    assert_eq!(code, 0, "stderr:\n{stderr}\nstdout:\n{stdout}");
    assert!(stdout.contains("OK: parsed 1 steps"), "{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_json_decode_error_includes_json_path() {
    let dir = TempDir::new("tla2-trace-validate-test");
    let path = dir.path.join("trace.json");
    common::write_file(
        &path,
        br#"{"version":"1","module":"Spec","variables":["x"],"steps":[{"index":0,"state":{"x":1}}]}"#,
    );

    let path_str = path.to_str().unwrap();
    let (code, _stdout, stderr) = run_tla(&["trace", "validate", path_str]);
    assert_failed(
        code,
        &stderr,
        &["parse trace", "as Json", "$.steps[0].state.x"],
    );
    assert_stderr_contains_path(&stderr, path_str);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_jsonl_decode_error_includes_json_path() {
    let dir = TempDir::new("tla2-trace-validate-test");
    let path = dir.path.join("trace.jsonl");
    common::write_file(
        &path,
        br#"{"type":"header","version":"1","module":"Spec","variables":["x"]}
{"type":"step","index":0,"state":{"x":1}}
"#,
    );

    let path_str = path.to_str().unwrap();
    let (code, _stdout, stderr) = run_tla(&["trace", "validate", path_str]);
    assert_failed(code, &stderr, &["parse trace", "as Jsonl", "$.state.x"]);
    assert_stderr_contains_path(&stderr, path_str);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_stdin_json_decode_error_includes_json_path() {
    let (code, _stdout, stderr) = run_tla_with_stdin(
        &["trace", "validate", "-"],
        br#"{"version":"1","module":"Spec","variables":["x"],"steps":[{"index":0,"state":{"x":1}}]}"#,
    );
    assert_failed(
        code,
        &stderr,
        &["parse trace - as Json", "$.steps[0].state.x"],
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_jsonl_requires_flag_without_jsonl_extension() {
    let dir = TempDir::new("tla2-trace-validate-test");
    let path = dir.path.join("trace.log");
    common::write_file(
        &path,
        br#"{"type":"header","version":"1","module":"Spec","variables":["x"]}
{"type":"step","index":0,"state":{"x":{"type":"int","value":1}}}
"#,
    );

    let path_str = path.to_str().unwrap();
    let (code, _stdout, stderr) = run_tla(&["trace", "validate", path_str]);
    assert_failed(code, &stderr, &["parse trace", "as Json"]);
    assert_stderr_contains_path(&stderr, path_str);

    let (code, stdout, stderr) = run_tla(&[
        "trace",
        "validate",
        path.to_str().unwrap(),
        "--input-format",
        "jsonl",
    ]);
    assert_eq!(code, 0, "stderr:\n{stderr}\nstdout:\n{stdout}");
    assert!(stdout.contains("OK: parsed 1 steps"), "{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_input_format_flag_overrides_extension_to_json() {
    let dir = TempDir::new("tla2-trace-validate-test");
    let path = dir.path.join("trace.jsonl");
    common::write_file(
        &path,
        br#"{"type":"header","version":"1","module":"Spec","variables":["x"]}
{"type":"step","index":0,"state":{"x":{"type":"int","value":1}}}
"#,
    );

    let path_str = path.to_str().unwrap();
    let (code, _stdout, stderr) =
        run_tla(&["trace", "validate", path_str, "--input-format", "json"]);
    assert_failed(code, &stderr, &["parse trace", "as Json"]);
    assert_stderr_contains_path(&stderr, path_str);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_input_format_flag_overrides_extension_to_jsonl() {
    let dir = TempDir::new("tla2-trace-validate-test");
    let path = dir.path.join("trace.json");
    common::write_file(
        &path,
        br#"{"type":"header","version":"1","module":"Spec","variables":["x"]}
{"type":"step","index":0,"state":{"x":{"type":"int","value":1}}}
"#,
    );

    let (code, stdout, stderr) = run_tla(&[
        "trace",
        "validate",
        path.to_str().unwrap(),
        "--input-format",
        "jsonl",
    ]);
    assert_eq!(code, 0, "stderr:\n{stderr}\nstdout:\n{stdout}");
    assert!(stdout.contains("OK: parsed 1 steps"), "{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_jsonl_handles_multi_thousand_step_file() {
    use std::fmt::Write as _;

    const STEPS: usize = 3_000;

    let dir = TempDir::new("tla2-trace-validate-test");
    let path = dir.path.join("trace.jsonl");

    // Rough capacity estimate: ~70 bytes/step + header.
    let mut s = String::with_capacity(128 + STEPS * 96);
    s.push_str(r#"{"type":"header","version":"1","module":"Spec","variables":["x"]}"#);
    s.push('\n');
    for idx in 0..STEPS {
        write!(
            &mut s,
            r#"{{"type":"step","index":{idx},"state":{{"x":{{"type":"int","value":{idx}}}}}}}"#
        )
        .unwrap();
        s.push('\n');
    }
    common::write_file(&path, s.as_bytes());

    let (code, stdout, stderr) = run_tla(&["trace", "validate", path.to_str().unwrap()]);
    assert_eq!(code, 0, "stderr:\n{stderr}\nstdout:\n{stdout}");
    assert!(
        stdout.contains(&format!("OK: parsed {STEPS} steps")),
        "{stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_json_handles_multi_thousand_step_file() {
    use std::fmt::Write as _;

    const N: usize = 3000;

    let dir = TempDir::new("tla2-trace-validate-test");
    let path = dir.path.join("trace.json");

    // Rough capacity estimate: ~100 bytes/step + header/footer.
    let mut s = String::with_capacity(128 + N * 120);
    s.push_str(r#"{"version":"1","module":"Spec","variables":["x"],"steps":["#);
    for i in 0..N {
        if i != 0 {
            s.push(',');
        }
        s.push_str(r#"{"index":"#);
        write!(&mut s, "{i}").unwrap();
        s.push_str(r#","state":{"x":{"type":"int","value":"#);
        write!(&mut s, "{i}").unwrap();
        s.push_str("}}}");
    }
    s.push_str("]}");
    common::write_file(&path, s.as_bytes());

    let (code, stdout, stderr) = run_tla(&["trace", "validate", path.to_str().unwrap()]);
    assert_eq!(code, 0, "stderr:\n{stderr}\nstdout:\n{stdout}");
    assert!(
        stdout.contains(&format!("OK: parsed {N} steps")),
        "{stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_jsonl_from_stdin_requires_flag() {
    let (code, _stdout, stderr) = run_tla_with_stdin(
        &["trace", "validate", "-"],
        br#"{"type":"header","version":"1","module":"Spec","variables":["x"]}
{"type":"step","index":0,"state":{"x":{"type":"int","value":1}}}
"#,
    );
    assert_failed(
        code,
        &stderr,
        &[
            "hint: stdin `auto` defaults to JSON",
            "parse trace - as Json",
        ],
    );

    let (code, stdout, stderr) = run_tla_with_stdin(
        &["trace", "validate", "-", "--input-format", "jsonl"],
        br#"{"type":"header","version":"1","module":"Spec","variables":["x"]}
{"type":"step","index":0,"state":{"x":{"type":"int","value":1}}}
"#,
    );
    assert_eq!(code, 0, "stderr:\n{stderr}\nstdout:\n{stdout}");
    assert!(stdout.contains("OK: parsed 1 steps"), "{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_auto_reads_json_from_stdin() {
    let (code, stdout, stderr) = run_tla_with_stdin(
        &["trace", "validate", "-"],
        br#"{"version":"1","module":"Spec","variables":["x"],"steps":[{"index":0,"state":{"x":{"type":"int","value":1}}}]}"#,
    );
    assert_eq!(code, 0, "stderr:\n{stderr}\nstdout:\n{stdout}");
    assert!(stdout.contains("OK: parsed 1 steps"), "{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_jsonl_rejects_step_index_mismatch() {
    let dir = TempDir::new("tla2-trace-validate-test");
    let path = dir.path.join("trace.jsonl");
    common::write_file(
        &path,
        br#"{"type":"header","version":"1","module":"Spec","variables":["x"]}
{"type":"step","index":1,"state":{"x":{"type":"int","value":1}}}
"#,
    );

    let path_str = path.to_str().unwrap();
    let (code, _stdout, stderr) = run_tla(&["trace", "validate", path_str]);
    assert_failed(
        code,
        &stderr,
        &[
            "parse trace",
            "as Jsonl",
            "trace step index mismatch",
            "jsonl line 2",
            "expected 0, got 1",
        ],
    );
    assert_stderr_contains_path(&stderr, path_str);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_jsonl_rejects_unknown_variable() {
    let dir = TempDir::new("tla2-trace-validate-test");
    let path = dir.path.join("trace.jsonl");
    common::write_file(
        &path,
        br#"{"type":"header","version":"1","module":"Spec","variables":["x"]}
{"type":"step","index":0,"state":{"y":{"type":"int","value":1}}}
"#,
    );

    let path_str = path.to_str().unwrap();
    let (code, _stdout, stderr) = run_tla(&["trace", "validate", path_str]);
    assert_failed(
        code,
        &stderr,
        &[
            "parse trace",
            "as Jsonl",
            "trace step references unknown variable",
            "jsonl line 2",
            "\"y\"",
        ],
    );
    assert_stderr_contains_path(&stderr, path_str);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_jsonl_rejects_action_on_initial_step() {
    let dir = TempDir::new("tla2-trace-validate-test");
    let path = dir.path.join("trace.jsonl");
    common::write_file(
        &path,
        br#"{"type":"header","version":"1","module":"Spec","variables":["x"]}
{"type":"step","index":0,"state":{"x":{"type":"int","value":1}},"action":{"name":"A"}}
"#,
    );

    let path_str = path.to_str().unwrap();
    let (code, _stdout, stderr) = run_tla(&["trace", "validate", path_str]);
    assert_failed(
        code,
        &stderr,
        &[
            "parse trace",
            "as Jsonl",
            "trace step 0 must not have an action label",
            "jsonl line 2",
        ],
    );
    assert_stderr_contains_path(&stderr, path_str);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_spec_accepts_matching_action_name() {
    let dir = TempDir::new("tla2-trace-validate-spec-action");
    let (spec_path, cfg_path) = write_action_label_spec_files(&dir);
    let trace_path = dir.path.join("trace.json");
    write_two_step_trace(&trace_path, Some("PropagateLemmas"));

    let (code, stdout, stderr) = run_tla(&[
        "trace",
        "validate",
        trace_path.to_str().unwrap(),
        "--spec",
        spec_path.to_str().unwrap(),
        "--config",
        cfg_path.to_str().unwrap(),
    ]);
    assert_eq!(code, 0, "stderr:\n{stderr}\nstdout:\n{stdout}");
    assert!(stdout.contains("OK: trace validated (2 steps"), "{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_spec_rejects_mismatched_action_name() {
    let dir = TempDir::new("tla2-trace-validate-spec-action");
    let (spec_path, cfg_path) = write_action_label_spec_files(&dir);
    let trace_path = dir.path.join("trace.json");
    write_two_step_trace(&trace_path, Some("LearnLemma"));

    let (code, _stdout, stderr) = run_tla(&[
        "trace",
        "validate",
        trace_path.to_str().unwrap(),
        "--spec",
        spec_path.to_str().unwrap(),
        "--config",
        cfg_path.to_str().unwrap(),
    ]);
    assert_failed(
        code,
        &stderr,
        &[
            "Trace validation failed",
            "trace step 1 action label \"LearnLemma\" did not match any observed transition",
        ],
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_spec_rejects_unknown_action_name() {
    let dir = TempDir::new("tla2-trace-validate-spec-action");
    let (spec_path, cfg_path) = write_action_label_spec_files(&dir);
    let trace_path = dir.path.join("trace.json");
    write_two_step_trace(&trace_path, Some("DoesNotExist"));

    let (code, _stdout, stderr) = run_tla(&[
        "trace",
        "validate",
        trace_path.to_str().unwrap(),
        "--spec",
        spec_path.to_str().unwrap(),
        "--config",
        cfg_path.to_str().unwrap(),
    ]);
    assert_failed(
        code,
        &stderr,
        &[
            "Trace validation failed",
            "trace step 1 references unknown action label \"DoesNotExist\"",
        ],
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_spec_without_actions_preserves_behavior() {
    let dir = TempDir::new("tla2-trace-validate-spec-action");
    let (spec_path, cfg_path) = write_action_label_spec_files(&dir);
    let trace_path = dir.path.join("trace.json");
    write_two_step_trace(&trace_path, None);

    let (code, stdout, stderr) = run_tla(&[
        "trace",
        "validate",
        trace_path.to_str().unwrap(),
        "--spec",
        spec_path.to_str().unwrap(),
        "--config",
        cfg_path.to_str().unwrap(),
    ]);
    assert_eq!(code, 0, "stderr:\n{stderr}\nstdout:\n{stdout}");
    assert!(stdout.contains("OK: trace validated (2 steps"), "{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_spec_warn_mode_accepts_mismatched_action() {
    let dir = TempDir::new("tla2-trace-validate-spec-warn");
    let (spec_path, cfg_path) = write_action_label_spec_files(&dir);
    let trace_path = dir.path.join("trace.json");
    // Label is "LearnLemma" but transition is PropagateLemmas (x: 0->2)
    write_two_step_trace(&trace_path, Some("LearnLemma"));

    let (code, stdout, stderr) = run_tla(&[
        "trace",
        "validate",
        trace_path.to_str().unwrap(),
        "--spec",
        spec_path.to_str().unwrap(),
        "--config",
        cfg_path.to_str().unwrap(),
        "--action-label-mode",
        "warn",
    ]);
    assert_eq!(code, 0, "stderr:\n{stderr}\nstdout:\n{stdout}");
    assert!(stdout.contains("OK: trace validated (2 steps"), "{stdout}");
    assert!(
        stderr.contains("Warning: step 1"),
        "expected warning in stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("LearnLemma"),
        "expected action name in warning:\n{stderr}"
    );
    assert!(
        stdout.contains("action label warnings: 1"),
        "expected warning count:\n{stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_spec_warn_mode_accepts_unknown_action() {
    let dir = TempDir::new("tla2-trace-validate-spec-warn");
    let (spec_path, cfg_path) = write_action_label_spec_files(&dir);
    let trace_path = dir.path.join("trace.json");
    write_two_step_trace(&trace_path, Some("DoesNotExist"));

    let (code, stdout, stderr) = run_tla(&[
        "trace",
        "validate",
        trace_path.to_str().unwrap(),
        "--spec",
        spec_path.to_str().unwrap(),
        "--config",
        cfg_path.to_str().unwrap(),
        "--action-label-mode",
        "warn",
    ]);
    assert_eq!(code, 0, "stderr:\n{stderr}\nstdout:\n{stdout}");
    assert!(stdout.contains("OK: trace validated (2 steps"), "{stdout}");
    assert!(
        stderr.contains("Warning: step 1"),
        "expected warning in stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("DoesNotExist"),
        "expected unknown action name in warning:\n{stderr}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn trace_validate_spec_error_mode_still_rejects_mismatch() {
    // Verify that --action-label-mode error (explicit) still rejects
    let dir = TempDir::new("tla2-trace-validate-spec-strict");
    let (spec_path, cfg_path) = write_action_label_spec_files(&dir);
    let trace_path = dir.path.join("trace.json");
    write_two_step_trace(&trace_path, Some("LearnLemma"));

    let (code, _stdout, stderr) = run_tla(&[
        "trace",
        "validate",
        trace_path.to_str().unwrap(),
        "--spec",
        spec_path.to_str().unwrap(),
        "--config",
        cfg_path.to_str().unwrap(),
        "--action-label-mode",
        "error",
    ]);
    assert_failed(
        code,
        &stderr,
        &[
            "Trace validation failed",
            "trace step 1 action label \"LearnLemma\" did not match any observed transition",
        ],
    );
}
