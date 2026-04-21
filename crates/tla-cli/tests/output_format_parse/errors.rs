// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::helpers::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_json_loader_error_includes_error_code() {
    let out = run_check_with_spec(
        "json",
        r#"---- MODULE Tmp ----
EXTENDS Naturals, TLC
VARIABLES x

I == INSTANCE Missing

Init == x = 0
Next == x' = x
====
"#,
    );
    assert_failure(&out);
    assert_exit_code_2(&out, "module loader failure");
    let v = parse_json(&out);
    assert_cli_error_result(&out, &v, "SYS_SETUP_ERROR");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_jsonl_loader_error_includes_error_code() {
    let out = run_check_with_spec(
        "jsonl",
        r#"---- MODULE Tmp ----
EXTENDS Naturals, TLC
VARIABLES x

I == INSTANCE Missing

Init == x = 0
Next == x' = x
====
"#,
    );
    assert_failure(&out);
    assert_exit_code_2(&out, "module loader failure");

    let values = parse_json_lines(&out);
    let v = find_jsonl_summary(&values, &out);
    assert_cli_error_result(&out, v, "SYS_SETUP_ERROR");
}

/// Part of #3706: POR is now accepted; --por should succeed, not error.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn output_json_por_accepted() {
    let out = run_check_with_spec_args("json", default_spec_src(), &["--por"]);
    assert_success(&out);
}

/// Part of #3706: POR is now accepted; --por should succeed, not error.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn output_jsonl_por_accepted() {
    let out = run_check_with_spec_args("jsonl", default_spec_src(), &["--por"]);
    assert_success(&out);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_json_completeness_gate_error_includes_error_code() {
    let out = run_check_with_spec_args("json", default_spec_src(), &["--require-exhaustive"]);
    assert_failure(&out);
    assert_exit_code_2(&out, "completeness gate failure");
    let v = parse_json(&out);
    assert_cli_error_result(&out, &v, "SYS_COMPLETENESS_GATED");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_jsonl_completeness_gate_error_includes_error_code() {
    let out = run_check_with_spec_args("jsonl", default_spec_src(), &["--require-exhaustive"]);
    assert_failure(&out);
    assert_exit_code_2(&out, "completeness gate failure");
    let values = parse_json_lines(&out);
    let v = find_jsonl_summary(&values, &out);
    assert_cli_error_result(&out, v, "SYS_COMPLETENESS_GATED");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_json_missing_cfg_emits_cli_error() {
    let out = run_check_custom("json", default_spec_src(), None, false);
    assert_failure(&out);
    assert_exit_code_2(&out, "missing cfg");
    let v = parse_json(&out);
    assert_cli_error_result(&out, &v, "SYS_SETUP_ERROR");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_jsonl_missing_cfg_emits_cli_error() {
    let out = run_check_custom("jsonl", default_spec_src(), None, false);
    assert_failure(&out);
    assert_exit_code_2(&out, "missing cfg");
    let values = parse_json_lines(&out);
    let v = find_jsonl_summary(&values, &out);
    assert_cli_error_result(&out, v, "SYS_SETUP_ERROR");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_json_cfg_parse_error_emits_cli_error() {
    let out = run_check_custom("json", default_spec_src(), Some("INIT\n"), true);
    assert_failure(&out);
    assert_exit_code_2(&out, "cfg parse error");
    let v = parse_json(&out);
    assert_cli_error_result(&out, &v, "CFG_PARSE_ERROR");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_jsonl_cfg_parse_error_emits_cli_error() {
    let out = run_check_custom("jsonl", default_spec_src(), Some("INIT\n"), true);
    assert_failure(&out);
    assert_exit_code_2(&out, "cfg parse error");
    let values = parse_json_lines(&out);
    let v = find_jsonl_summary(&values, &out);
    assert_cli_error_result(&out, v, "CFG_PARSE_ERROR");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_json_tla_parse_error_emits_cli_error() {
    let out = run_check_custom(
        "json",
        "---- MODULE Tmp ----\nVARIABLES x\nInit == x = 0\nNext == x' = x\n",
        Some("INIT Init\nNEXT Next\n"),
        true,
    );
    assert_failure(&out);
    assert_exit_code_2(&out, "tla parse error");
    let v = parse_json(&out);
    assert_cli_error_result(&out, &v, "TLA_PARSE_ERROR");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_jsonl_tla_parse_error_emits_cli_error() {
    let out = run_check_custom(
        "jsonl",
        "---- MODULE Tmp ----\nVARIABLES x\nInit == x = 0\nNext == x' = x\n",
        Some("INIT Init\nNEXT Next\n"),
        true,
    );
    assert_failure(&out);
    assert_exit_code_2(&out, "tla parse error");
    let values = parse_json_lines(&out);
    let v = find_jsonl_summary(&values, &out);
    assert_cli_error_result(&out, v, "TLA_PARSE_ERROR");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_json_tla_lower_error_emits_cli_error() {
    let out = run_check_custom(
        "json",
        r#"---- MODULE Tmp ----
EXTENDS Naturals
VARIABLES x

Init == x = 0
Next == [Nat -> Nat]_x
====
"#,
        Some("INIT Init\nNEXT Next\n"),
        true,
    );
    assert_failure(&out);
    assert_exit_code_2(&out, "tla lower error");
    let v = parse_json(&out);
    assert_cli_error_result(&out, &v, "TLA_LOWER_ERROR");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_jsonl_tla_lower_error_emits_cli_error() {
    let out = run_check_custom(
        "jsonl",
        r#"---- MODULE Tmp ----
EXTENDS Naturals
VARIABLES x

Init == x = 0
Next == [Nat -> Nat]_x
====
"#,
        Some("INIT Init\nNEXT Next\n"),
        true,
    );
    assert_failure(&out);
    assert_exit_code_2(&out, "tla lower error");
    let values = parse_json_lines(&out);
    let v = find_jsonl_summary(&values, &out);
    assert_cli_error_result(&out, v, "TLA_LOWER_ERROR");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_json_semantic_resolution_error_emits_cli_error() {
    let out = run_check_custom(
        "json",
        r#"---- MODULE Tmp ----
CONSTANTS x
VARIABLES x

Init == x = 0
Next == x' = x
====
"#,
        Some("INIT Init\nNEXT Next\n"),
        true,
    );
    assert_failure(&out);
    assert_exit_code_2(&out, "semantic resolution error");
    let v = parse_json(&out);
    assert_cli_error_result(&out, &v, "SYS_SETUP_ERROR");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn output_jsonl_semantic_resolution_error_emits_cli_error() {
    let out = run_check_custom(
        "jsonl",
        r#"---- MODULE Tmp ----
CONSTANTS x
VARIABLES x

Init == x = 0
Next == x' = x
====
"#,
        Some("INIT Init\nNEXT Next\n"),
        true,
    );
    assert_failure(&out);
    assert_exit_code_2(&out, "semantic resolution error");
    let values = parse_json_lines(&out);
    let v = find_jsonl_summary(&values, &out);
    assert_cli_error_result(&out, v, "SYS_SETUP_ERROR");
}
