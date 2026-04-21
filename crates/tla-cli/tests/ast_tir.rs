// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::process::Command;

mod common;
use common::TempDir;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn ast_without_tir_keeps_lowered_ast_output() {
    let dir = TempDir::new("tla2-ast-output");
    let main = dir.path.join("Main.tla");
    common::write_file(
        &main,
        br#"
---- MODULE Main ----
VARIABLE x
Init == x = 0
====
"#,
    );

    let bin = env!("CARGO_BIN_EXE_tla2");
    let out = Command::new(bin)
        .args(["ast", main.to_str().expect("utf-8 main path")])
        .output()
        .expect("run tla2 ast");

    assert!(
        out.status.success(),
        "expected success\nexit code: {code:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        code = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("Module {"), "stdout:\n{stdout}");
    assert!(!stdout.contains("TirModule"), "stdout:\n{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn ast_tir_dumps_bootstrap_tir_for_single_module() {
    let dir = TempDir::new("tla2-ast-tir");
    let main = dir.path.join("Main.tla");
    common::write_file(
        &main,
        br#"
---- MODULE Main ----
Sub == [Next]_vars
====
"#,
    );

    let bin = env!("CARGO_BIN_EXE_tla2");
    let out = Command::new(bin)
        .args(["ast", "--tir", main.to_str().expect("utf-8 main path")])
        .output()
        .expect("run tla2 ast --tir");

    assert!(
        out.status.success(),
        "expected success\nexit code: {code:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        code = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("TirModule {"), "stdout:\n{stdout}");
    assert!(stdout.contains("ActionSubscript"), "stdout:\n{stdout}");
    assert!(stdout.contains("name: \"Sub\""), "stdout:\n{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn ast_tir_loads_instance_modules_before_lowering() {
    let dir = TempDir::new("tla2-ast-tir-instance");
    let main = dir.path.join("Main.tla");
    let inner = dir.path.join("Inner.tla");

    common::write_file(
        &main,
        br#"
---- MODULE Main ----
I == INSTANCE Inner WITH Flag <- TRUE
Named == I!Safe
====
"#,
    );

    common::write_file(
        &inner,
        br#"
---- MODULE Inner ----
Flag == FALSE
Safe == Flag
====
"#,
    );

    let bin = env!("CARGO_BIN_EXE_tla2");
    let out = Command::new(bin)
        .args(["ast", "--tir", main.to_str().expect("utf-8 main path")])
        .output()
        .expect("run tla2 ast --tir with instance module");

    assert!(
        out.status.success(),
        "expected success\nexit code: {code:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        code = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("TirModule {"), "stdout:\n{stdout}");
    assert!(stdout.contains("name: \"Named\""), "stdout:\n{stdout}");
    assert!(
        stdout.contains("Const { value: TRUE, ty: Bool }"),
        "stdout:\n{stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn ast_tir_loads_imported_parameterized_instance_modules_before_lowering() {
    let dir = TempDir::new("tla2-ast-tir-imported-instance");
    let main = dir.path.join("Main.tla");
    let ext = dir.path.join("Ext.tla");
    let inner = dir.path.join("Inner.tla");

    common::write_file(
        &main,
        br#"
---- MODULE Main ----
EXTENDS Ext
Use == P(FALSE)!Safe
====
"#,
    );

    common::write_file(
        &ext,
        br#"
---- MODULE Ext ----
P(x) == INSTANCE Inner WITH Flag <- x
====
"#,
    );

    common::write_file(
        &inner,
        br#"
---- MODULE Inner ----
Flag == FALSE
Safe == Flag
====
"#,
    );

    let bin = env!("CARGO_BIN_EXE_tla2");
    let out = Command::new(bin)
        .args(["ast", "--tir", main.to_str().expect("utf-8 main path")])
        .output()
        .expect("run tla2 ast --tir with imported parameterized instance");

    assert!(
        out.status.success(),
        "expected success\nexit code: {code:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        code = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("TirModule {"), "stdout:\n{stdout}");
    assert!(stdout.contains("name: \"Use\""), "stdout:\n{stdout}");
    assert!(
        stdout.contains("Const { value: FALSE, ty: Bool }"),
        "stdout:\n{stdout}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn ast_tir_resolves_let_bound_instance_aliases() {
    let dir = TempDir::new("tla2-ast-tir-let-instance");
    let main = dir.path.join("Main.tla");
    let inner = dir.path.join("Inner.tla");

    common::write_file(
        &main,
        br#"
---- MODULE Main ----
Use == LET I == INSTANCE Inner WITH Flag <- TRUE
       IN I!Safe
====
"#,
    );

    common::write_file(
        &inner,
        br#"
---- MODULE Inner ----
Flag == FALSE
Safe == Flag
====
"#,
    );

    let bin = env!("CARGO_BIN_EXE_tla2");
    let out = Command::new(bin)
        .args(["ast", "--tir", main.to_str().expect("utf-8 main path")])
        .output()
        .expect("run tla2 ast --tir with let-bound instance");

    assert!(
        out.status.success(),
        "expected success\nexit code: {code:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        code = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("TirModule {"), "stdout:\n{stdout}");
    assert!(stdout.contains("name: \"Use\""), "stdout:\n{stdout}");
    assert!(
        stdout.contains("Const { value: TRUE, ty: Bool }"),
        "stdout:\n{stdout}"
    );
}
