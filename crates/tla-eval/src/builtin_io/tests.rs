// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::{EvalCtx, Expr, Spanned, Value};
use super::csv::format_csv_write_line;
use super::io_utils::{apply_template_substitutions, exec_command, is_io_exec_allowed, set_io_exec_allowed};
use super::resolve_input_path;
use crate::value::intern_string;

fn unique_temp_dir(prefix: &str) -> std::path::PathBuf {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock before unix epoch")
        .as_nanos();
    let pid = std::process::id();
    std::env::temp_dir().join(format!("{}_{}_{}", prefix, pid, nanos))
}

#[test]
fn resolve_input_path_prefers_spec_base_dir_for_relative_filenames() {
    let root = unique_temp_dir("tla2_builtin_io_base");
    let spec_dir = root.join("specs").join("ewd998");
    std::fs::create_dir_all(&spec_dir).expect("create spec dir");
    let data_path = spec_dir.join("EWD998ChanTrace.ndjson");
    std::fs::write(&data_path, "{}\n").expect("write ndjson fixture");

    let ctx = EvalCtx::new();
    ctx.set_input_base_dir(Some(spec_dir.clone()));

    let resolved = resolve_input_path(&ctx, "EWD998ChanTrace.ndjson");
    assert_eq!(resolved, data_path);

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn resolve_input_path_uses_spec_ancestor_for_repo_relative_path() {
    let root = unique_temp_dir("tla2_builtin_io_ancestor");
    let spec_dir = root.join("specifications").join("ewd998");
    std::fs::create_dir_all(&spec_dir).expect("create spec dir");
    let repo_relative = std::path::Path::new("specifications")
        .join("ewd998")
        .join("EWD998ChanTrace.ndjson");
    let data_path = root.join(&repo_relative);
    std::fs::write(&data_path, "{}\n").expect("write ndjson fixture");

    let ctx = EvalCtx::new();
    ctx.set_input_base_dir(Some(spec_dir));

    let repo_relative_str = repo_relative.to_string_lossy();
    let resolved = resolve_input_path(&ctx, &repo_relative_str);
    assert_eq!(resolved, data_path);

    let _ = std::fs::remove_dir_all(root);
}

#[test]
fn format_csv_write_line_requires_sequence_argument() {
    let err = format_csv_write_line("%s", &Value::int(1), None)
        .expect_err("CSVWrite should reject non-sequence tuple arguments");
    let rendered = err.to_string();
    assert!(
        rendered.contains("Sequence") || rendered.contains("sequence"),
        "expected sequence type error, got: {rendered}"
    );
}

#[test]
fn format_csv_write_line_supports_sequential_and_positional_placeholders() {
    let tuple = Value::Tuple(vec![Value::int(7), Value::String(intern_string("ok"))].into());

    let sequential =
        format_csv_write_line("value=%s status=%s", &tuple, None).expect("sequential format");
    assert_eq!(sequential, "value=7 status=\"ok\"");

    let positional =
        format_csv_write_line("%2$s <- %1$s", &tuple, None).expect("positional format");
    assert_eq!(positional, "\"ok\" <- 7");
}

#[test]
fn apply_template_substitutions_rejects_non_string_substitutions() {
    let cmd = Value::Tuple(vec![Value::String(intern_string("echo %s"))].into());
    let subs = Value::Tuple(vec![Value::int(1)].into());

    let err = apply_template_substitutions(&cmd, &subs, "IOExecTemplate", None)
        .expect_err("IOExecTemplate substitutions should require strings");
    let rendered = err.to_string();
    assert!(
        rendered.contains("strings"),
        "expected string element error, got: {rendered}"
    );
}

#[test]
fn exec_command_rejects_non_string_command_elements() {
    let cmd = Value::Tuple(vec![Value::int(1)].into());

    let err = exec_command(&cmd, None, "IOExec", None).expect_err("IOExec should require strings");
    let rendered = err.to_string();
    assert!(
        rendered.contains("strings"),
        "expected string element error, got: {rendered}"
    );
}

#[test]
fn exec_command_requires_record_env() {
    let cmd = Value::Tuple(vec![Value::String(intern_string("/bin/pwd"))].into());
    let err = exec_command(&cmd, Some(&Value::int(1)), "IOEnvExec", None)
        .expect_err("IOEnvExec should require a record environment");
    let rendered = err.to_string();
    assert!(
        rendered.contains("Record") || rendered.contains("record"),
        "expected record type error, got: {rendered}"
    );
}

#[test]
fn exec_command_uses_process_working_directory_not_input_base_dir() {
    let root = unique_temp_dir("tla2_builtin_io_exec");
    let spec_dir = root.join("specs");
    std::fs::create_dir_all(&spec_dir).expect("create spec dir");

    let ctx = EvalCtx::new();
    ctx.set_input_base_dir(Some(spec_dir.clone()));

    let cmd = Value::Tuple(vec![Value::String(intern_string("/bin/pwd"))].into());
    let result = exec_command(&cmd, None, "IOExec", None).expect("pwd command should run");
    let stdout = result
        .as_record()
        .and_then(|record| record.get("stdout"))
        .and_then(Value::as_string)
        .expect("stdout field should be present")
        .trim();

    let expected = std::env::current_dir().expect("current dir");
    assert_eq!(std::path::PathBuf::from(stdout), expected);
    assert_ne!(std::path::PathBuf::from(stdout), spec_dir);

    let _ = std::fs::remove_dir_all(root);
}

// === Security gate tests for #3965 ===
//
// The IO_EXEC_ALLOWED gate is a global AtomicBool shared across all tests.
// To avoid race conditions with parallel test execution, all gate-dependent
// tests are consolidated into a single test that runs sequentially.
// A mutex ensures no other test can flip the gate concurrently.

use std::sync::Mutex;

/// Mutex to serialize all tests that touch the IO_EXEC_ALLOWED global.
static IO_GATE_TEST_LOCK: Mutex<()> = Mutex::new(());

/// Helper: build a Spanned<Expr> tuple of string literals, e.g. <<"/bin/echo", "hello">>.
fn make_string_tuple_expr(strings: &[&str]) -> Spanned<Expr> {
    let elements: Vec<Spanned<Expr>> = strings
        .iter()
        .map(|s| Spanned::dummy(Expr::String(s.to_string())))
        .collect();
    Spanned::dummy(Expr::Tuple(elements))
}

/// Verify that check_io_exec_gate blocks or permits all 4 IOExec operators
/// and does not block non-exec operators. Runs both blocked and allowed
/// paths sequentially under a mutex to avoid global-state races.
#[test]
fn test_io_exec_security_gate() {
    let _lock = IO_GATE_TEST_LOCK.lock().expect("IO gate test lock");
    let ctx = EvalCtx::new();

    // --- Phase 1: Gate disabled (default) ---
    set_io_exec_allowed(false);
    assert!(!is_io_exec_allowed(), "gate should be disabled");

    // IOExec: should be blocked
    {
        let cmd_arg = make_string_tuple_expr(&["/bin/echo", "test"]);
        let result = super::io_utils::eval(&ctx, "IOExec", &[cmd_arg], None);
        let err = result.expect_err("IOExec should be blocked when gate is disabled");
        let rendered = err.to_string();
        assert!(
            rendered.contains("command execution is disabled by default for security"),
            "expected security gate error for IOExec, got: {rendered}"
        );
        assert!(
            rendered.contains("--allow-io"),
            "error should mention --allow-io flag, got: {rendered}"
        );
    }

    // IOEnvExec: should be blocked
    {
        let env_arg = make_string_tuple_expr(&[]);
        let cmd_arg = make_string_tuple_expr(&["/bin/echo"]);
        let result = super::io_utils::eval(&ctx, "IOEnvExec", &[env_arg, cmd_arg], None);
        let err = result.expect_err("IOEnvExec should be blocked when gate is disabled");
        let rendered = err.to_string();
        assert!(
            rendered.contains("command execution is disabled by default for security"),
            "expected security gate error for IOEnvExec, got: {rendered}"
        );
    }

    // IOExecTemplate: should be blocked
    {
        let cmd_arg = make_string_tuple_expr(&["/bin/echo", "%s"]);
        let subs_arg = make_string_tuple_expr(&["hello"]);
        let result =
            super::io_utils::eval(&ctx, "IOExecTemplate", &[cmd_arg, subs_arg], None);
        let err = result.expect_err("IOExecTemplate should be blocked when gate is disabled");
        let rendered = err.to_string();
        assert!(
            rendered.contains("command execution is disabled by default for security"),
            "expected security gate error for IOExecTemplate, got: {rendered}"
        );
    }

    // IOEnvExecTemplate: should be blocked
    {
        let env_arg = make_string_tuple_expr(&[]);
        let cmd_arg = make_string_tuple_expr(&["/bin/echo"]);
        let subs_arg = make_string_tuple_expr(&["hello"]);
        let result = super::io_utils::eval(
            &ctx,
            "IOEnvExecTemplate",
            &[env_arg, cmd_arg, subs_arg],
            None,
        );
        let err =
            result.expect_err("IOEnvExecTemplate should be blocked when gate is disabled");
        let rendered = err.to_string();
        assert!(
            rendered.contains("command execution is disabled by default for security"),
            "expected security gate error for IOEnvExecTemplate, got: {rendered}"
        );
    }

    // Non-exec operators: should NOT be blocked even with gate disabled
    {
        let result = super::io_utils::eval(&ctx, "IOEnv", &[], None);
        assert!(result.is_ok(), "IOEnv should not be blocked by IO exec gate");

        let str_arg = Spanned::dummy(Expr::String("42".to_string()));
        let result = super::io_utils::eval(&ctx, "atoi", &[str_arg], None);
        let value = result
            .expect("atoi should not be blocked by IO exec gate")
            .expect("atoi should return Some(value)");
        assert_eq!(value.as_i64(), Some(42));
    }

    // --- Phase 2: Gate enabled ---
    set_io_exec_allowed(true);
    assert!(is_io_exec_allowed(), "gate should be enabled");

    // IOExec: should succeed
    {
        let cmd_arg = make_string_tuple_expr(&["/bin/echo", "hello"]);
        let result = super::io_utils::eval(&ctx, "IOExec", &[cmd_arg], None);
        let value = result
            .expect("IOExec should succeed when gate is enabled")
            .expect("IOExec should return Some(value)");
        let record = value.as_record().expect("IOExec result should be a record");
        let exit_val = record.get("exitValue").expect("should have exitValue field");
        assert_eq!(exit_val.as_i64(), Some(0), "echo should exit with 0");
        let stdout = record
            .get("stdout")
            .and_then(Value::as_string)
            .expect("should have stdout field");
        assert_eq!(stdout.trim(), "hello");
    }

    // --- Phase 3: Gate can be re-disabled ---
    set_io_exec_allowed(false);
    assert!(!is_io_exec_allowed(), "gate should be disabled again");

    {
        let cmd_arg = make_string_tuple_expr(&["/bin/echo", "test"]);
        let result = super::io_utils::eval(&ctx, "IOExec", &[cmd_arg], None);
        assert!(
            result.is_err(),
            "IOExec should be blocked after gate is re-disabled"
        );
    }

    // Leave gate disabled for other tests
    set_io_exec_allowed(false);
}
