// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;
use std::process::Command;

use serde_json::Value;

use super::common::{self, TempDir};

pub fn default_spec_src() -> &'static str {
    r#"---- MODULE Tmp ----
EXTENDS Naturals, TLC
VARIABLES x

Init == x = 0
Next == x' = x
====
"#
}

pub fn write_spec_and_config(dir: &TempDir, spec_src: &str) -> (PathBuf, PathBuf) {
    common::write_spec_and_config(dir, "Tmp", spec_src, "INIT Init\nNEXT Next\n")
}

pub fn run_check_with_spec_args(
    output_format: &str,
    spec_src: &str,
    extra_args: &[&str],
) -> std::process::Output {
    let dir = TempDir::new("tla-cli-output-format-parse");
    let (spec, cfg) = write_spec_and_config(&dir, spec_src);

    let bin = env!("CARGO_BIN_EXE_tla2");
    let mut cmd = Command::new(bin);
    cmd.arg("check")
        .arg(&spec)
        .arg("--config")
        .arg(&cfg)
        .arg("--no-deadlock")
        .arg("--max-depth")
        .arg("1")
        .arg("--max-states")
        .arg("1")
        .args(extra_args)
        .arg("--output")
        .arg(output_format);
    cmd.output().expect("run tla check")
}

pub fn run_check_with_spec(output_format: &str, spec_src: &str) -> std::process::Output {
    run_check_with_spec_args(output_format, spec_src, &[])
}

pub fn run_check(output_format: &str) -> std::process::Output {
    run_check_with_spec(output_format, default_spec_src())
}

pub fn run_check_custom(
    output_format: &str,
    spec_src: &str,
    cfg_src: Option<&str>,
    pass_config_flag: bool,
) -> std::process::Output {
    let dir = TempDir::new("tla-cli-output-format-custom");
    let spec = dir.path.join("Tmp.tla");
    let cfg = dir.path.join("Tmp.cfg");

    std::fs::write(&spec, spec_src).expect("write spec");
    if let Some(cfg_src) = cfg_src {
        std::fs::write(&cfg, cfg_src).expect("write cfg");
    }

    let bin = env!("CARGO_BIN_EXE_tla2");
    let mut cmd = Command::new(bin);
    cmd.arg("check")
        .arg(&spec)
        .arg("--no-deadlock")
        .arg("--max-depth")
        .arg("1")
        .arg("--max-states")
        .arg("1");
    if pass_config_flag {
        cmd.arg("--config").arg(&cfg);
    }
    cmd.arg("--output").arg(output_format);
    cmd.output().expect("run tla check")
}

pub fn assert_success(out: &std::process::Output) {
    assert!(
        out.status.success(),
        "expected exit code 0, got {status:?} (code={code:?})\nstderr:\n{stderr}\nstdout:\n{stdout}",
        status = out.status,
        code = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );
}

pub fn assert_failure(out: &std::process::Output) {
    assert!(
        !out.status.success(),
        "expected non-zero exit code, got {status:?} (code={code:?})\nstderr:\n{stderr}\nstdout:\n{stdout}",
        status = out.status,
        code = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );
}

pub fn assert_json_has_summary_fields(out: &std::process::Output, value: &Value) {
    let obj = value.as_object().unwrap_or_else(|| {
        panic!(
            "expected JSON to be an object, got: {value:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            stdout = String::from_utf8_lossy(&out.stdout),
            stderr = String::from_utf8_lossy(&out.stderr),
        )
    });

    let version = obj
        .get("version")
        .and_then(Value::as_str)
        .unwrap_or_else(|| {
            panic!(
                "expected JSON to have string field 'version', got: {value:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
                stdout = String::from_utf8_lossy(&out.stdout),
                stderr = String::from_utf8_lossy(&out.stderr),
            )
        });
    assert!(
        !version.trim().is_empty(),
        "expected JSON 'version' to be non-empty, got: {version:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        stdout = String::from_utf8_lossy(&out.stdout),
        stderr = String::from_utf8_lossy(&out.stderr),
    );

    let tool = obj
        .get("tool")
        .and_then(Value::as_str)
        .unwrap_or_else(|| {
            panic!(
                "expected JSON to have string field 'tool', got: {value:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
                stdout = String::from_utf8_lossy(&out.stdout),
                stderr = String::from_utf8_lossy(&out.stderr),
            )
        });
    assert!(
        !tool.trim().is_empty(),
        "expected JSON 'tool' to be non-empty, got: {tool:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        stdout = String::from_utf8_lossy(&out.stdout),
        stderr = String::from_utf8_lossy(&out.stderr),
    );

    let result = obj
        .get("result")
        .and_then(Value::as_object)
        .unwrap_or_else(|| {
            panic!(
                "expected JSON to have object field 'result', got: {value:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
                stdout = String::from_utf8_lossy(&out.stdout),
                stderr = String::from_utf8_lossy(&out.stderr),
            )
        });
    let status = result
        .get("status")
        .and_then(Value::as_str)
        .unwrap_or_else(|| {
            panic!(
                "expected JSON 'result.status' to be a string, got: {value:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
                stdout = String::from_utf8_lossy(&out.stdout),
                stderr = String::from_utf8_lossy(&out.stderr),
            )
        });
    assert!(
        !status.trim().is_empty(),
        "expected JSON 'result.status' to be non-empty, got: {status:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        stdout = String::from_utf8_lossy(&out.stdout),
        stderr = String::from_utf8_lossy(&out.stderr),
    );
}

pub fn parse_json(out: &std::process::Output) -> Value {
    let s = std::str::from_utf8(&out.stdout).unwrap_or_else(|e| {
        panic!(
            "expected stdout to be utf-8: {e}\nstderr:\n{stderr}\nstdout (lossy):\n{stdout}",
            stderr = String::from_utf8_lossy(&out.stderr),
            stdout = String::from_utf8_lossy(&out.stdout),
        )
    });
    let value: Value = serde_json::from_str(s.trim()).unwrap_or_else(|e| {
        panic!(
            "expected stdout to be valid JSON: {e}\nstderr:\n{stderr}\nstdout:\n{stdout}",
            stderr = String::from_utf8_lossy(&out.stderr),
            stdout = s
        )
    });
    assert!(
        value.is_object(),
        "expected JSON to be an object, got: {value:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = s,
    );
    assert_json_has_summary_fields(out, &value);
    value
}

pub fn parse_json_lines(out: &std::process::Output) -> Vec<Value> {
    let s = std::str::from_utf8(&out.stdout).unwrap_or_else(|e| {
        panic!(
            "expected stdout to be utf-8: {e}\nstderr:\n{stderr}\nstdout (lossy):\n{stdout}",
            stderr = String::from_utf8_lossy(&out.stderr),
            stdout = String::from_utf8_lossy(&out.stdout),
        )
    });
    let mut values = Vec::new();
    for (idx, line) in s.lines().enumerate() {
        let idx = idx + 1;
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let value: Value = serde_json::from_str(line).unwrap_or_else(|e| {
            panic!(
                "expected line {idx} to be valid JSONL: {e}\nstderr:\n{stderr}\nline:\n{line}\nstdout:\n{stdout}",
                stderr = String::from_utf8_lossy(&out.stderr),
                stdout = s
            )
        });
        assert!(
            value.is_object(),
            "expected JSONL line {idx} to be an object, got: {value:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
            stderr = String::from_utf8_lossy(&out.stderr),
            stdout = s,
        );
        values.push(value);
    }
    assert!(
        !values.is_empty(),
        "expected at least one JSON object on stdout, got empty output\nstderr:\n{stderr}\nstdout:\n{stdout}",
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = s
    );
    let summary = find_jsonl_summary(&values, out);
    assert_json_has_summary_fields(out, summary);
    values
}

pub fn assert_exit_code_2(out: &std::process::Output, context: &str) {
    assert_eq!(
        out.status.code(),
        Some(2),
        "{context}: expected exit code 2, got {code:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        code = out.status.code(),
        stdout = String::from_utf8_lossy(&out.stdout),
        stderr = String::from_utf8_lossy(&out.stderr),
    );
}

pub fn assert_cli_error_result(out: &std::process::Output, v: &Value, expected_code: &str) {
    let result = v
        .get("result")
        .and_then(Value::as_object)
        .unwrap_or_else(|| {
            panic!(
                "expected output to have object field 'result', got: {v:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
                stdout = String::from_utf8_lossy(&out.stdout),
                stderr = String::from_utf8_lossy(&out.stderr),
            )
        });

    let status = result.get("status").and_then(Value::as_str).unwrap_or_else(|| {
        panic!(
            "expected output 'result.status' to be a string, got: {v:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            stdout = String::from_utf8_lossy(&out.stdout),
            stderr = String::from_utf8_lossy(&out.stderr),
        )
    });
    assert_eq!(
        status,
        "error",
        "expected output 'result.status' == \"error\", got: {status:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        stdout = String::from_utf8_lossy(&out.stdout),
        stderr = String::from_utf8_lossy(&out.stderr),
    );

    let error_type = result.get("error_type").and_then(Value::as_str).unwrap_or_else(|| {
        panic!(
            "expected output 'result.error_type' to be a string, got: {v:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            stdout = String::from_utf8_lossy(&out.stdout),
            stderr = String::from_utf8_lossy(&out.stderr),
        )
    });
    assert_eq!(
        error_type,
        "cli_error",
        "expected output 'result.error_type' == \"cli_error\", got: {error_type:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        stdout = String::from_utf8_lossy(&out.stdout),
        stderr = String::from_utf8_lossy(&out.stderr),
    );

    let code = result.get("error_code").and_then(Value::as_str).unwrap_or_else(|| {
        panic!(
            "expected output 'result.error_code' to be a string, got: {v:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            stdout = String::from_utf8_lossy(&out.stdout),
            stderr = String::from_utf8_lossy(&out.stderr),
        )
    });
    assert_eq!(
        code,
        expected_code,
        "expected output 'result.error_code' == {expected_code:?}, got: {code:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        stdout = String::from_utf8_lossy(&out.stdout),
        stderr = String::from_utf8_lossy(&out.stderr),
    );

    let msg = result
        .get("error_message")
        .and_then(Value::as_str)
        .unwrap_or_else(|| {
            panic!(
                "expected output 'result.error_message' to be a string, got: {v:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
                stdout = String::from_utf8_lossy(&out.stdout),
                stderr = String::from_utf8_lossy(&out.stderr),
            )
        });
    assert!(
        !msg.trim().is_empty(),
        "expected output 'result.error_message' to be non-empty, got: {msg:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        stdout = String::from_utf8_lossy(&out.stdout),
        stderr = String::from_utf8_lossy(&out.stderr),
    );
}

pub fn find_jsonl_summary<'a>(values: &'a [Value], out: &std::process::Output) -> &'a Value {
    let last = values.last().unwrap_or_else(|| {
        panic!(
            "expected at least one JSON object on stdout, got empty output\nstderr:\n{stderr}\nstdout:\n{stdout}",
            stdout = String::from_utf8_lossy(&out.stdout),
            stderr = String::from_utf8_lossy(&out.stderr),
        )
    });
    if last.get("result").is_none() {
        let has_result = values.iter().any(|v| v.get("result").is_some());
        panic!(
            "expected final JSONL object to be the summary with field 'result' (has_any_result={has_result})\nstderr:\n{stderr}\nstdout:\n{stdout}",
            has_result = has_result,
            stdout = String::from_utf8_lossy(&out.stdout),
            stderr = String::from_utf8_lossy(&out.stderr),
        );
    }
    last
}
