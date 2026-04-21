// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::process::Command;

mod common;
use common::TempDir;

#[derive(Debug)]
struct ToolMessage {
    code: String,
    class: String,
    body: String,
}

fn run_check_tool(spec_src: &str, cfg_src: &str, extra_args: &[&str]) -> std::process::Output {
    let dir = TempDir::new("tla-cli-tlc-tool-output");
    let (spec, cfg) = common::write_spec_and_config(&dir, "Tmp", spec_src, cfg_src);

    let bin = env!("CARGO_BIN_EXE_tla2");
    let mut cmd = Command::new(bin);
    cmd.arg("check")
        .arg(&spec)
        .arg("--config")
        .arg(&cfg)
        .arg("--workers")
        .arg("1")
        .args(extra_args)
        .arg("--output")
        .arg("tlc-tool");
    cmd.output().expect("run tla2 check")
}

fn run_check_tool_flag(spec_src: &str, cfg_src: &str, extra_args: &[&str]) -> std::process::Output {
    let dir = TempDir::new("tla-cli-tlc-tool-output-flag");
    let (spec, cfg) = common::write_spec_and_config(&dir, "Tmp", spec_src, cfg_src);

    let bin = env!("CARGO_BIN_EXE_tla2");
    let mut cmd = Command::new(bin);
    cmd.arg("check")
        .arg(&spec)
        .arg("--config")
        .arg(&cfg)
        .arg("--workers")
        .arg("1")
        .args(extra_args)
        .arg("--tool");
    cmd.output().expect("run tla2 check")
}

fn run_check_tool_with_workers(
    workers: usize,
    spec_src: &str,
    cfg_src: &str,
    extra_args: &[&str],
) -> std::process::Output {
    let dir = TempDir::new("tla-cli-tlc-tool-output-workers");
    let (spec, cfg) = common::write_spec_and_config(&dir, "Tmp", spec_src, cfg_src);

    let bin = env!("CARGO_BIN_EXE_tla2");
    let mut cmd = Command::new(bin);
    cmd.arg("check")
        .arg(&spec)
        .arg("--config")
        .arg(&cfg)
        .arg("--workers")
        .arg(workers.to_string())
        .args(extra_args)
        .arg("--output")
        .arg("tlc-tool");
    cmd.output().expect("run tla2 check")
}

fn parse_tool_output(stdout: &str) -> Vec<ToolMessage> {
    const START_PREFIX: &str = "@!@!@STARTMSG ";
    const END_PREFIX: &str = "@!@!@ENDMSG ";
    const SUFFIX: &str = " @!@!@";

    let mut messages = Vec::new();

    let mut current_code: Option<String> = None;
    let mut current_class: Option<String> = None;
    let mut body_lines: Vec<String> = Vec::new();

    for raw_line in stdout.lines() {
        let line = raw_line.trim_end_matches('\r');
        if line.starts_with(START_PREFIX) {
            assert!(
                current_code.is_none(),
                "nested STARTMSG detected; previous message not closed\nstdout:\n{stdout}"
            );
            assert!(
                line.ends_with(SUFFIX),
                "STARTMSG line missing suffix\nline={line:?}\nstdout:\n{stdout}"
            );
            let inner = &line[START_PREFIX.len()..line.len() - SUFFIX.len()];
            let (code, class) = inner.split_once(':').unwrap_or_else(|| {
                panic!(
                    "invalid STARTMSG payload (expected CODE:CLASS)\nline={line:?}\nstdout:\n{stdout}"
                )
            });
            assert!(
                code.len() == 4 && code.chars().all(|c| c.is_ascii_digit()),
                "tool messageCode must be 4-digit decimal\nline={line:?}\nstdout:\n{stdout}"
            );
            assert!(
                class.len() == 1 && class.chars().all(|c| c.is_ascii_digit()),
                "tool messageClass must be 1-digit decimal\nline={line:?}\nstdout:\n{stdout}"
            );
            let code_i: i32 = code.parse().expect("parse tool messageCode");
            assert!(
                (1000..=9999).contains(&code_i),
                "tool messageCode must be within [1000, 9999]\nline={line:?}\nstdout:\n{stdout}"
            );
            let class_i: i32 = class.parse().expect("parse tool messageClass");
            assert!(
                (0..=9).contains(&class_i),
                "tool messageClass must be within [0, 9]\nline={line:?}\nstdout:\n{stdout}"
            );
            current_code = Some(code.to_string());
            current_class = Some(class.to_string());
            body_lines.clear();
            continue;
        }

        if line.starts_with(END_PREFIX) {
            let code = current_code.take().unwrap_or_else(|| {
                panic!("ENDMSG without STARTMSG\nline={line:?}\nstdout:\n{stdout}")
            });
            let class = current_class.take().expect("class must be set with code");
            assert!(
                line.ends_with(SUFFIX),
                "ENDMSG line missing suffix\nline={line:?}\nstdout:\n{stdout}"
            );
            let end_code = line[END_PREFIX.len()..line.len() - SUFFIX.len()].trim();
            assert_eq!(
                end_code, code,
                "ENDMSG code does not match STARTMSG code\nline={line:?}\nstdout:\n{stdout}"
            );
            messages.push(ToolMessage {
                code,
                class,
                body: body_lines.join("\n"),
            });
            body_lines.clear();
            continue;
        }

        if current_code.is_some() {
            body_lines.push(line.to_string());
        } else {
            assert!(
                line.trim().is_empty(),
                "untagged output encountered outside message blocks\nline={line:?}\nstdout:\n{stdout}"
            );
        }
    }

    assert!(
        current_code.is_none(),
        "unterminated STARTMSG (missing ENDMSG)\nstdout:\n{stdout}"
    );
    assert!(
        !messages.is_empty(),
        "expected at least one tagged message block\nstdout:\n{stdout}"
    );
    messages
}

fn has_msg(messages: &[ToolMessage], code: &str, class: &str) -> bool {
    messages.iter().any(|m| m.code == code && m.class == class)
}

fn find_msg<'a>(messages: &'a [ToolMessage], code: &str, class: &str) -> &'a ToolMessage {
    messages
        .iter()
        .find(|m| m.code == code && m.class == class)
        .unwrap_or_else(|| {
            panic!(
                "missing message code={code} class={class}\nall messages:\n{msgs:#?}",
                msgs = messages
            )
        })
}

fn msg_index(messages: &[ToolMessage], code: &str, class: &str) -> usize {
    messages
        .iter()
        .position(|m| m.code == code && m.class == class)
        .unwrap_or_else(|| {
            panic!(
                "missing message code={code} class={class}\nall messages:\n{msgs:#?}",
                msgs = messages
            )
        })
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn tlc_tool_invariant_violation_emits_state_trace_blocks() {
    let out = run_check_tool(
        r#"---- MODULE Tmp ----
EXTENDS Naturals
VARIABLES x

Init == x = 0
Next == x' = x
Inv == x < 0
====
"#,
        r#"INIT Init
NEXT Next
INVARIANT Inv
"#,
        &["--no-deadlock"],
    );

    assert!(
        !out.status.success(),
        "expected non-zero exit code\nstderr:\n{stderr}\nstdout:\n{stdout}",
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );
    assert!(
        out.stderr.is_empty(),
        "expected tool mode to avoid untagged stderr output\nstderr:\n{stderr}",
        stderr = String::from_utf8_lossy(&out.stderr),
    );

    let stdout = std::str::from_utf8(&out.stdout).expect("stdout utf-8");
    let messages = parse_tool_output(stdout);

    assert!(
        has_msg(&messages, "2110", "1"),
        "expected invariant violation (EC 2110, MP.ERROR)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2121", "1"),
        "expected 'behavior up to this point' (EC 2121, MP.ERROR)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2186", "0"),
        "expected TLC_FINISHED message (EC 2186, MP.NONE)\nmessages:\n{messages:#?}"
    );

    let idx_violation = msg_index(&messages, "2110", "1");
    let idx_behavior = msg_index(&messages, "2121", "1");
    let idx_state = msg_index(&messages, "2217", "4");
    assert!(
        idx_violation < idx_behavior && idx_behavior < idx_state,
        "expected error trace framing to precede state blocks (2110 -> 2121 -> 2217)\nmessages:\n{messages:#?}"
    );

    let state = find_msg(&messages, "2217", "4");
    assert!(
        state.body.starts_with("1: "),
        "expected state body to start with \"1: \"\nstate body:\n{body}",
        body = state.body
    );
    assert!(
        state.body.contains("/\\ x = 0"),
        "expected state body to contain variable assignment\nstate body:\n{body}",
        body = state.body
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn tlc_tool_success_emits_collision_probability_message() {
    let out = run_check_tool(
        r#"---- MODULE Tmp ----
EXTENDS Naturals
VARIABLES x

Init == x = 0
Next == x' = x
====
"#,
        r#"INIT Init
NEXT Next
"#,
        &["--no-deadlock"],
    );

    assert!(
        out.status.success(),
        "expected exit code 0\nstderr:\n{stderr}\nstdout:\n{stdout}",
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );
    assert!(
        out.stderr.is_empty(),
        "expected tool mode to avoid untagged stderr output\nstderr:\n{stderr}",
        stderr = String::from_utf8_lossy(&out.stderr),
    );

    let stdout = std::str::from_utf8(&out.stdout).expect("stdout utf-8");
    let messages = parse_tool_output(stdout);

    assert!(
        has_msg(&messages, "2262", "0"),
        "expected TLC_VERSION message (EC 2262, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2187", "0"),
        "expected TLC_MODE_MC message (EC 2187, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2185", "0"),
        "expected TLC_STARTING message (EC 2185, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2220", "0"),
        "expected TLC_SANY_START message (EC 2220, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2189", "0"),
        "expected TLC_COMPUTING_INIT message (EC 2189, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2190", "0"),
        "expected TLC_INIT_GENERATED1 message (EC 2190, MP.NONE)\nmessages:\n{messages:#?}"
    );

    let success = find_msg(&messages, "2193", "0");
    assert!(
        success
            .body
            .starts_with("Model checking completed. No error has been found."),
        "unexpected TLC_SUCCESS body:\n{body}",
        body = success.body
    );
    assert!(
        !success.body.contains("@!@!@STARTMSG") && !success.body.contains("@!@!@ENDMSG"),
        "success message body must not contain tag sentinels\n{body}",
        body = success.body
    );
    assert!(
        has_msg(&messages, "2186", "0"),
        "expected TLC_FINISHED message (EC 2186, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2219", "0"),
        "expected TLC_SANY_END message (EC 2219, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2199", "0"),
        "expected TLC_STATS message (EC 2199, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2194", "0"),
        "expected TLC_SEARCH_DEPTH message (EC 2194, MP.NONE)\nmessages:\n{messages:#?}"
    );

    let stats = find_msg(&messages, "2199", "0");
    let (gen_s, rest) = stats
        .body
        .split_once(" states generated, ")
        .expect("TLC_STATS: parse states generated");
    let (distinct_s, rest) = rest
        .split_once(" distinct states found, ")
        .expect("TLC_STATS: parse distinct states");
    let (left_s, rest) = rest
        .split_once(" states left on queue.")
        .expect("TLC_STATS: parse left on queue");
    assert!(
        rest.is_empty(),
        "unexpected TLC_STATS trailing text: {rest:?}\nfull_body:\n{body}",
        body = stats.body
    );

    let generated: u64 = gen_s.replace(',', "").parse().expect("parse generated");
    let distinct: u64 = distinct_s.replace(',', "").parse().expect("parse distinct");
    let left: u64 = left_s.replace(',', "").parse().expect("parse left");
    assert!(
        generated >= distinct,
        "expected generated >= distinct\nbody:\n{body}",
        body = stats.body
    );
    assert_eq!(
        left,
        0,
        "expected left-on-queue to be 0 at end of run\nbody:\n{body}",
        body = stats.body
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn tool_flag_emits_tagged_output() {
    let out = run_check_tool_flag(
        r#"---- MODULE Tmp ----
EXTENDS Naturals
VARIABLES x

Init == x = 0
Next == x' = x
====
"#,
        r#"INIT Init
NEXT Next
"#,
        &["--no-deadlock"],
    );

    assert!(
        out.status.success(),
        "expected exit code 0\nstderr:\n{stderr}\nstdout:\n{stdout}",
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );
    assert!(
        out.stderr.is_empty(),
        "expected tool mode to avoid untagged stderr output\nstderr:\n{stderr}",
        stderr = String::from_utf8_lossy(&out.stderr),
    );

    let stdout = std::str::from_utf8(&out.stdout).expect("stdout utf-8");
    let messages = parse_tool_output(stdout);

    assert!(
        has_msg(&messages, "2193", "0"),
        "expected TLC_SUCCESS message (EC 2193, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2186", "0"),
        "expected TLC_FINISHED message (EC 2186, MP.NONE)\nmessages:\n{messages:#?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn tlc_tool_rejects_parallel_workers_to_preserve_trace_compatibility() {
    let out = run_check_tool_with_workers(
        2,
        r#"---- MODULE Tmp ----
EXTENDS Naturals
VARIABLES x

Init == x = 0
Next == x' = x
====
"#,
        r#"INIT Init
NEXT Next
"#,
        &["--no-deadlock"],
    );

    assert!(
        !out.status.success(),
        "expected non-zero exit code\nstderr:\n{stderr}\nstdout:\n{stdout}",
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );
    assert!(
        out.stderr.is_empty(),
        "expected tool mode to avoid untagged stderr output\nstderr:\n{stderr}",
        stderr = String::from_utf8_lossy(&out.stderr),
    );

    let stdout = std::str::from_utf8(&out.stdout).expect("stdout utf-8");
    let messages = parse_tool_output(stdout);
    let err = find_msg(&messages, "1000", "1");
    assert!(
        err.body.contains("--workers 1"),
        "expected tool-mode worker error to mention --workers 1\nbody:\n{body}",
        body = err.body
    );
    assert!(
        has_msg(&messages, "2186", "0"),
        "expected TLC_FINISHED message (EC 2186, MP.NONE)\nmessages:\n{messages:#?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn tlc_tool_tla_parse_error_is_tagged_and_finishes() {
    let out = run_check_tool(
        r#"---- MODULE Tmp ----
EXTENDS Naturals
VARIABLES x

Init == x =
Next == x' = x
====
"#,
        r#"INIT Init
NEXT Next
"#,
        &[],
    );

    assert!(
        !out.status.success(),
        "expected non-zero exit code\nstderr:\n{stderr}\nstdout:\n{stdout}",
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );
    assert!(
        out.stderr.is_empty(),
        "expected tool mode to avoid untagged stderr output\nstderr:\n{stderr}",
        stderr = String::from_utf8_lossy(&out.stderr),
    );

    let stdout = std::str::from_utf8(&out.stdout).expect("stdout utf-8");
    let messages = parse_tool_output(stdout);
    assert!(
        has_msg(&messages, "2262", "0"),
        "expected TLC_VERSION message (EC 2262, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2187", "0"),
        "expected TLC_MODE_MC message (EC 2187, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2185", "0"),
        "expected TLC_STARTING message (EC 2185, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2220", "0"),
        "expected TLC_SANY_START message (EC 2220, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "1000", "1"),
        "expected general error message (EC 1000, MP.ERROR)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2186", "0"),
        "expected TLC_FINISHED message (EC 2186, MP.NONE)\nmessages:\n{messages:#?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn tlc_tool_cfg_parse_error_is_tagged_and_finishes() {
    let out = run_check_tool(
        r#"---- MODULE Tmp ----
EXTENDS Naturals
VARIABLES x

Init == x = 0
Next == x' = x
====
"#,
        r#"INIT
NEXT Next
"#,
        &[],
    );

    assert!(
        !out.status.success(),
        "expected non-zero exit code\nstderr:\n{stderr}\nstdout:\n{stdout}",
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );
    assert!(
        out.stderr.is_empty(),
        "expected tool mode to avoid untagged stderr output\nstderr:\n{stderr}",
        stderr = String::from_utf8_lossy(&out.stderr),
    );

    let stdout = std::str::from_utf8(&out.stdout).expect("stdout utf-8");
    let messages = parse_tool_output(stdout);
    assert!(
        has_msg(&messages, "2262", "0"),
        "expected TLC_VERSION message (EC 2262, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2187", "0"),
        "expected TLC_MODE_MC message (EC 2187, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2185", "0"),
        "expected TLC_STARTING message (EC 2185, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2220", "0"),
        "expected TLC_SANY_START message (EC 2220, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "1000", "1"),
        "expected general error message (EC 1000, MP.ERROR)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2186", "0"),
        "expected TLC_FINISHED message (EC 2186, MP.NONE)\nmessages:\n{messages:#?}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn tlc_tool_semantic_error_is_tagged_and_finishes() {
    let out = run_check_tool(
        r#"---- MODULE Tmp ----
EXTENDS Naturals
VARIABLES x

Init == x = 0
Next == x' = y
====
"#,
        r#"INIT Init
NEXT Next
"#,
        &[],
    );

    assert!(
        !out.status.success(),
        "expected non-zero exit code\nstderr:\n{stderr}\nstdout:\n{stdout}",
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );
    assert!(
        out.stderr.is_empty(),
        "expected tool mode to avoid untagged stderr output\nstderr:\n{stderr}",
        stderr = String::from_utf8_lossy(&out.stderr),
    );

    let stdout = std::str::from_utf8(&out.stdout).expect("stdout utf-8");
    let messages = parse_tool_output(stdout);
    assert!(
        has_msg(&messages, "2262", "0"),
        "expected TLC_VERSION message (EC 2262, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2187", "0"),
        "expected TLC_MODE_MC message (EC 2187, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2185", "0"),
        "expected TLC_STARTING message (EC 2185, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2220", "0"),
        "expected TLC_SANY_START message (EC 2220, MP.NONE)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "1000", "1"),
        "expected general error message (EC 1000, MP.ERROR)\nmessages:\n{messages:#?}"
    );
    assert!(
        has_msg(&messages, "2186", "0"),
        "expected TLC_FINISHED message (EC 2186, MP.NONE)\nmessages:\n{messages:#?}"
    );
}
