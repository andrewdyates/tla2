// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::process::Command;

mod common;
use common::TempDir;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn codegen_loads_named_instance_modules() {
    let dir = TempDir::new("tla2-codegen-named-instance");

    let main = dir.path.join("Main.tla");
    let inner = dir.path.join("Inner.tla");

    common::write_file(
        &main,
        br#"
---- MODULE Main ----
VARIABLE x

I == INSTANCE Inner
Init == I!Init
Next == I!Next
InvNonNegative == I!InvNonNegative
====
"#,
    );

    common::write_file(
        &inner,
        br#"
---- MODULE Inner ----
Init == x = 0
Next == x' = x + 1
InvNonNegative == x >= 0
====
"#,
    );

    let bin = env!("CARGO_BIN_EXE_tla2");
    let out = Command::new(bin)
        .args(["codegen", main.to_str().expect("utf-8 main path")])
        .output()
        .expect("run tla2 codegen");

    assert!(
        out.status.success(),
        "expected success\nexit code: {code:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        code = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("fn check_inv_non_negative"),
        "stdout:\n{stdout}"
    );
    assert!(stdout.contains("(state.x >= 0_i64)"), "stdout:\n{stdout}");
    assert!(!stdout.contains("I!"), "stdout:\n{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn codegen_imports_standalone_instance_init_next_and_invariants() {
    let dir = TempDir::new("tla2-codegen-standalone-instance");

    let main = dir.path.join("Main.tla");
    let inner = dir.path.join("Inner.tla");

    common::write_file(
        &main,
        br#"
---- MODULE Main ----
VARIABLE x

INSTANCE Inner
====
"#,
    );

    common::write_file(
        &inner,
        br#"
---- MODULE Inner ----
Init == x = 0
Next == x' = x + 1
InvNonNegative == x >= 0
====
"#,
    );

    let bin = env!("CARGO_BIN_EXE_tla2");
    let out = Command::new(bin)
        .args(["codegen", main.to_str().expect("utf-8 main path")])
        .output()
        .expect("run tla2 codegen");

    assert!(
        out.status.success(),
        "expected success\nexit code: {code:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        code = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("fn init(&self) -> Vec<Self::State>"),
        "stdout:\n{stdout}"
    );
    assert!(
        stdout.contains("fn next(&self, state: &Self::State) -> Vec<Self::State>"),
        "stdout:\n{stdout}"
    );
    assert!(stdout.contains("\"InvNonNegative\""), "stdout:\n{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn codegen_imports_standalone_instance_with_substitutions() {
    let dir = TempDir::new("tla2-codegen-standalone-instance-with-substitutions");

    let main = dir.path.join("Main.tla");
    let inner = dir.path.join("Inner.tla");

    common::write_file(
        &main,
        br#"
---- MODULE Main ----
VARIABLE x

INSTANCE Inner WITH limit <- 5
InvLocal == x >= 0
====
"#,
    );

    common::write_file(
        &inner,
        br#"
---- MODULE Inner ----
CONSTANT limit

Init == x = limit
Next == x' = x + 1
InvBounded == x >= limit
====
"#,
    );

    let bin = env!("CARGO_BIN_EXE_tla2");
    let out = Command::new(bin)
        .args(["codegen", main.to_str().expect("utf-8 main path")])
        .output()
        .expect("run tla2 codegen");

    assert!(
        out.status.success(),
        "expected success\nexit code: {code:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        code = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("fn init(&self) -> Vec<Self::State>"),
        "stdout:\n{stdout}"
    );
    assert!(
        stdout.contains("fn next(&self, state: &Self::State) -> Vec<Self::State>"),
        "stdout:\n{stdout}"
    );
    assert!(stdout.contains("\"InvBounded\""), "stdout:\n{stdout}");
    assert!(stdout.contains("x: 5_i64"), "stdout:\n{stdout}");
    assert!(stdout.contains("(state.x >= 5_i64)"), "stdout:\n{stdout}");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn codegen_handles_parameterized_and_chained_instance_targets() {
    let dir = TempDir::new("tla2-codegen-param-chained-instance");

    let main = dir.path.join("Main.tla");
    let mid = dir.path.join("Mid.tla");
    let inner = dir.path.join("Inner.tla");
    let param = dir.path.join("Param.tla");

    common::write_file(
        &main,
        br#"
---- MODULE Main ----
VARIABLE x

P(n) == INSTANCE Param WITH limit <- n
I == INSTANCE Mid

Init == x = 0
Next == I!J!Next
InvBoth == P(5)!InvBounded /\ I!J!InvBounded
====
"#,
    );

    common::write_file(
        &mid,
        br#"
---- MODULE Mid ----
J == INSTANCE Inner
====
"#,
    );

    common::write_file(
        &inner,
        br#"
---- MODULE Inner ----
Next == x' = x + 1
InvBounded == x <= 10
====
"#,
    );

    common::write_file(
        &param,
        br#"
---- MODULE Param ----
InvBounded == x <= limit
====
"#,
    );

    let bin = env!("CARGO_BIN_EXE_tla2");
    let out = Command::new(bin)
        .args(["codegen", main.to_str().expect("utf-8 main path")])
        .output()
        .expect("run tla2 codegen");

    assert!(
        out.status.success(),
        "expected success\nexit code: {code:?}\nstderr:\n{stderr}\nstdout:\n{stdout}",
        code = out.status.code(),
        stderr = String::from_utf8_lossy(&out.stderr),
        stdout = String::from_utf8_lossy(&out.stdout),
    );

    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("(state.x <= 5_i64)"), "stdout:\n{stdout}");
    assert!(stdout.contains("(state.x <= 10_i64)"), "stdout:\n{stdout}");
}
