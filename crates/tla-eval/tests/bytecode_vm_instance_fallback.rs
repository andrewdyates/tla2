// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::ffi::OsString;
use std::sync::{Mutex, MutexGuard};
use tla_core::ast::Module;
use tla_core::{lower, parse_to_syntax_tree, FileId};
use tla_eval::tir::TirProgram;
use tla_eval::{bytecode_vm_stats, clear_for_run_reset, clear_for_test_reset, EvalCtx};
use tla_value::Value;

static ENV_VAR_LOCK: Mutex<()> = Mutex::new(());

struct EnvVarGuard {
    entries: Vec<(&'static str, Option<OsString>)>,
    lock: Option<MutexGuard<'static, ()>>,
}

impl EnvVarGuard {
    fn set_many(vars: &[(&'static str, &'static str)]) -> Self {
        let lock = ENV_VAR_LOCK.lock().expect("env var lock");
        let mut entries = Vec::with_capacity(vars.len());
        for (key, value) in vars {
            entries.push((*key, std::env::var_os(key)));
            std::env::set_var(key, value);
        }
        Self {
            entries,
            lock: Some(lock),
        }
    }
}

impl Drop for EnvVarGuard {
    fn drop(&mut self) {
        for (key, previous) in self.entries.drain(..).rev() {
            match previous {
                Some(value) => std::env::set_var(key, value),
                None => std::env::remove_var(key),
            }
        }
        let _ = self.lock.take();
    }
}

fn parse_module(src: &str, file_id: u32) -> Module {
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(file_id), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lowering errors: {:?}",
        lower_result.errors
    );
    lower_result.module.expect("module should parse")
}

#[test]
fn test_bytecode_vm_named_instance_operator_capturing_lambda_compiles() {
    // Part of #3697: capturing lambda `LET y == 1 IN (LAMBDA x: x + y)`
    // should compile to MakeClosure instead of falling back to AST.
    let inner = parse_module(
        "\
---- MODULE BytecodeInstanceInner3670 ----
Make == LET y == 1 IN (LAMBDA x: x + y)
====",
        0,
    );
    let wrapper = parse_module(
        "\
---- MODULE BytecodeInstanceWrapper3670 ----
I == INSTANCE BytecodeInstanceInner3670
Use == I!Make
====",
        1,
    );
    let _guard =
        EnvVarGuard::set_many(&[("TLA2_BYTECODE_VM", "1"), ("TLA2_BYTECODE_VM_STATS", "1")]);
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_modules(&[&wrapper, &inner]);
    // Bind an empty state array so the bytecode VM can execute.
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&wrapper, &[&inner]);
    let value = program
        .eval_named_op(&ctx, "Use")
        .expect("INSTANCE-imported capturing lambda should compile and execute via bytecode");

    assert!(
        matches!(value, Value::Closure(_)),
        "INSTANCE-imported capturing lambda should produce a closure value, got: {value:?}"
    );
    let stats = bytecode_vm_stats();
    assert_eq!(
        stats.2, 0,
        "capturing lambda should compile successfully (0 compile failures), got: {stats:?}",
    );
    assert!(
        stats.0 > 0,
        "capturing lambda should execute via bytecode (executions > 0), got: {stats:?}",
    );

    clear_for_run_reset();
    let stats2 = bytecode_vm_stats();
    assert_eq!(
        stats2.2, 0,
        "bytecode VM diagnostics should survive run resets within a single checker run",
    );

    clear_for_test_reset();
    assert_eq!(bytecode_vm_stats(), (0, 0, 0));
}

#[test]
fn test_bytecode_vm_executes_unnamed_instance_parameterized_operator_reference() {
    let inner = parse_module(
        "\
---- MODULE BytecodeInstanceInner3693OpRef ----
CONSTANT K
AddK(x) == x + K
====",
        0,
    );
    let wrapper = parse_module(
        "\
---- MODULE BytecodeInstanceWrapper3693OpRef ----
Nodes == 1
INSTANCE BytecodeInstanceInner3693OpRef WITH K <- Nodes
Use == LET F == AddK IN F(41)
====",
        1,
    );
    let _guard =
        EnvVarGuard::set_many(&[("TLA2_BYTECODE_VM", "1"), ("TLA2_BYTECODE_VM_STATS", "1")]);
    clear_for_test_reset();

    let mut ctx = EvalCtx::new();
    ctx.load_modules(&[&wrapper, &inner]);
    let state_values: Vec<Value> = vec![];
    let _state_guard = ctx.bind_state_array_guard(&state_values);

    let program = TirProgram::from_modules(&wrapper, &[&inner]);
    let value = program
        .eval_named_op(&ctx, "Use")
        .expect("INSTANCE-imported parameterized operator reference should execute via bytecode");

    assert_eq!(
        value,
        Value::int(42),
        "bytecode-compiled operator reference must preserve INSTANCE substitution context",
    );
    assert_eq!(
        bytecode_vm_stats(),
        (1, 0, 0),
        "INSTANCE-imported parameterized operator reference should execute via bytecode",
    );
}
