// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end integration tests: compile generated code to verify it is valid
//! Rust, then build and execute to verify runtime correctness.

mod common;

use std::path::{Path, PathBuf};

use common::parse_and_generate;
use tla_codegen::CodeGenOptions;

// ── Shared project helpers ──

/// Create a temporary Cargo project with tla-runtime dependency.
fn create_temp_project(name: &str, extra_toml: &str) -> (PathBuf, PathBuf) {
    use std::fs;
    let temp_dir = std::env::temp_dir().join(format!("tla2_{}_{}", name, std::process::id()));
    let src_dir = temp_dir.join("src");
    let _ = fs::remove_dir_all(&temp_dir);
    fs::create_dir_all(&src_dir).expect("Failed to create temp src directory");
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    let runtime_path = std::path::Path::new(&manifest_dir)
        .join("../tla-runtime")
        .canonicalize()
        .expect("Failed to find tla-runtime path");
    let cargo_toml = format!(
        "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\
         \n{extra_toml}[dependencies]\ntla-runtime = {{ path = \"{}\" }}\n",
        runtime_path.display()
    );
    fs::write(temp_dir.join("Cargo.toml"), &cargo_toml).expect("Failed to write Cargo.toml");
    (temp_dir, src_dir)
}

/// Run `cargo check` on a temp project; panic with generated-file debug info on failure.
fn cargo_check_or_panic(temp_dir: &Path, src_dir: &Path, spec_names: &[&str]) {
    use std::fs;
    use std::process::Command;
    let output = Command::new("cargo")
        .args(["check", "--message-format=short"])
        .current_dir(temp_dir)
        .output()
        .expect("Failed to execute cargo check");
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let mut debug_info = String::new();
        for name in spec_names {
            let mod_name = name.to_lowercase();
            let mod_file = src_dir.join(format!("{}.rs", mod_name));
            if let Ok(content) = fs::read_to_string(&mod_file) {
                use std::fmt::Write as _;
                write!(debug_info, "\n=== {}.rs ===\n{}\n", mod_name, content).unwrap();
            }
        }
        let _ = fs::remove_dir_all(temp_dir);
        panic!(
            "Generated code failed to compile!\n\nstdout:\n{}\n\nstderr:\n{}\n\nGenerated files:\n{}",
            stdout, stderr, debug_info
        );
    }
    let _ = fs::remove_dir_all(temp_dir);
}

/// Build and run a binary in a temp project; verify "All tests passed!" in output.
fn cargo_build_run_or_panic(temp_dir: &Path) {
    use std::fs;
    use std::process::Command;
    let build_output = Command::new("cargo")
        .args(["build", "--release"])
        .current_dir(temp_dir)
        .output()
        .expect("Failed to execute cargo build");
    if !build_output.status.success() {
        let stderr = String::from_utf8_lossy(&build_output.stderr);
        let _ = fs::remove_dir_all(temp_dir);
        panic!("Failed to build test binary:\n{}", stderr);
    }
    let run_output = Command::new("cargo")
        .args(["run", "--release"])
        .current_dir(temp_dir)
        .output()
        .expect("Failed to execute test binary");
    let _ = fs::remove_dir_all(temp_dir);
    if !run_output.status.success() {
        let stderr = String::from_utf8_lossy(&run_output.stderr);
        let stdout = String::from_utf8_lossy(&run_output.stdout);
        panic!(
            "Test binary failed!\nstdout:\n{}\nstderr:\n{}",
            stdout, stderr
        );
    }
    let stdout = String::from_utf8_lossy(&run_output.stdout);
    assert!(
        stdout.contains("All tests passed!"),
        "Test binary should print success message. Got:\n{}",
        stdout
    );
}

// ── Compile test: spec data ──

const COMPILE_SPECS: &[(&str, &str)] = &[
    (
        "Counter",
        r#"
---- MODULE Counter ----
VARIABLE count

Init == count = 0

Next == count' = count + 1

InvNonNegative == count >= 0
====
"#,
    ),
    (
        "SetOps",
        r#"
---- MODULE SetOps ----
VARIABLE s

Init == s = {1, 2, 3}

Next == s' = s \union {4}

InvHasOne == 1 \in s
====
"#,
    ),
    (
        "FunctionTest",
        r#"
---- MODULE FunctionTest ----
VARIABLE f

Init == f = [x \in {1, 2, 3} |-> x * 2]

Next == f' = [f EXCEPT ![1] = 10]

InvDomainSize == TRUE
====
"#,
    ),
    (
        "RecordTest",
        r#"
---- MODULE RecordTest ----
VARIABLE r

Init == r = [x |-> 1, y |-> 2]

Next == r' = r
====
"#,
    ),
    (
        "IfThenElse",
        r#"
---- MODULE IfThenElse ----
VARIABLE x

Init == x = 0

Next == x' = IF x < 10 THEN x + 1 ELSE x
====
"#,
    ),
    (
        "LetIn",
        r#"
---- MODULE LetIn ----
VARIABLE result

Init == result = 0

Next ==
    LET a == 10
        b == 20
    IN result' = a + b
====
"#,
    ),
    (
        "FuncSetTest",
        r#"
---- MODULE FuncSetTest ----
VARIABLE f

Init == f \in [{1, 2} -> {0, 1}]

Next == f' = f
====
"#,
    ),
];

// ── Execute test: spec data ──

const BOUNDED_COUNTER_SPEC: &str = r#"
---- MODULE BoundedCounter ----
VARIABLE count

Init == count = 0

Next == count' = IF count < 5 THEN count + 1 ELSE count

InvBounded == count >= 0 /\ count <= 5
====
"#;

const CONFLICT_SPEC: &str = r#"
---- MODULE Conflict ----
VARIABLE x

Init == x = 0
Next == x' = 1 /\ UNCHANGED x
====
"#;

const STRICT_COUNTER_SPEC: &str = r#"
---- MODULE StrictCounter ----
VARIABLE x

Init == x = 0
Next == x' = x + 1
====
"#;

const RECURSIVE_FACTORIAL_SPEC: &str = r#"
---- MODULE RecursiveFactorial ----
VARIABLE dummy

RECURSIVE Factorial(_)

Init == dummy = 0

Factorial(n) == IF n = 0 THEN 1 ELSE n * Factorial(n - 1)

InvFactorial == Factorial(5) = 120
====
"#;

const EXEC_TEST_MAIN_CODE: &str = r#"

use bounded_counter::BoundedCounter;
use conflict::Conflict;
use strict_counter::StrictCounter;
use tla_runtime::prelude::*;

impl conflict::checker::ToConflictState for conflict::ConflictState {
    fn to_conflict_state(&self) -> conflict::ConflictState {
        self.clone()
    }
}

impl strict_counter::checker::ToStrictCounterState for strict_counter::StrictCounterState {
    fn to_strict_counter_state(&self) -> strict_counter::StrictCounterState {
        self.clone()
    }
}

fn main() {
    let machine = BoundedCounter;

    // Test 1: Verify initial states
    let init_states = machine.init();
    assert_eq!(init_states.len(), 1, "Should have exactly one initial state");
    assert_eq!(init_states[0].count, 0, "Initial count should be 0");

    // Test 1b: checker::check_init
    let strict_machine = StrictCounter;
    let strict_init_states = strict_machine.init();
    assert_eq!(strict_init_states.len(), 1, "StrictCounter should have exactly one init state");
    assert_eq!(strict_init_states[0].x, 0, "StrictCounter init x should be 0");
    assert!(strict_counter::checker::check_init(&strict_counter::StrictCounterState { x: 0 }).is_ok());
    assert!(strict_counter::checker::check_init(&strict_counter::StrictCounterState { x: 1 }).is_err());

    // Test 2: Run model checker
    let result = model_check(&machine, 100);

    // We expect a deadlock since at count=5 the spec stays at 5 forever
    // (but all states still have a next state - themselves)
    // Actually: IF count < 5 THEN count + 1 ELSE count means no deadlock

    // Test 3: Verify state space
    let states = collect_states(&machine, 100);
    assert!(states.len() >= 6, "Should have at least 6 states (0-5), got {}", states.len());

    // Test 4: Verify counts are in expected range
    for state in &states {
        assert!(state.count >= 0 && state.count <= 5,
            "Count {} out of expected range [0, 5]", state.count);
    }

    // Test 5: Verify invariant holds on all states
    for state in &states {
        if let Some(holds) = machine.check_invariant(state) {
            assert!(holds, "Invariant violated at count={}", state.count);
        }
    }

    // Test 6: Check transitions are correct
    let state0 = bounded_counter::BoundedCounterState { count: 0 };
    let next_states = machine.next(&state0);
    assert_eq!(next_states.len(), 1);
    assert_eq!(next_states[0].count, 1, "From 0 should go to 1");

    let state5 = bounded_counter::BoundedCounterState { count: 5 };
    let next_from_5 = machine.next(&state5);
    assert_eq!(next_from_5.len(), 1);
    assert_eq!(next_from_5[0].count, 5, "From 5 should stay at 5");

    // Test 7: UNCHANGED/assignment overlap behaves as conjunction.
    //
    // Next == x' = 1 /\ UNCHANGED x  ==  (x_next == 1) /\ (x_next == x)
    // So the action is satisfiable iff x == 1, and the successor keeps x unchanged.
    let conflict = Conflict;
    let old0 = conflict::ConflictState { x: 0 };
    let next0 = conflict.next(&old0);
    assert!(next0.is_empty(), "From x=0, Next should be unsatisfiable");

    let old1 = conflict::ConflictState { x: 1 };
    let next1 = conflict.next(&old1);
    assert_eq!(next1.len(), 1, "From x=1, should have exactly one successor");
    assert_eq!(next1[0].x, 1, "Successor should keep x unchanged at 1");

    let err = conflict::checker::check_transition(&old0, &old0).unwrap_err();
    assert!(err.contains("old_state="), "expected old_state in error: {}", err);
    assert!(err.contains("new_state="), "expected new_state in error: {}", err);
    assert!(conflict::checker::check_transition(&old0, &old1).is_err());
    assert!(conflict::checker::check_transition(&old1, &old1).is_ok());

    // Test 8: stuttering-aware transition acceptance (even if raw Next disallows it).
    let strict_old = strict_counter::StrictCounterState { x: 0 };
    assert!(strict_counter::checker::check_transition(&strict_old, &strict_old).is_err());
    assert!(strict_counter::checker::check_transition_or_stutter(&strict_old, &strict_old).is_ok());

    println!("All tests passed!");
    println!("States explored: {}", states.len());
}
"#;

// ── Tests ──

/// End-to-end compile test: generates Rust code and compiles it to verify correctness.
///
/// This test creates a temporary Cargo project with generated code and runs `cargo check`
/// to ensure the generated code is valid, compilable Rust.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_end_to_end_compile() {
    use std::fs;

    let (temp_dir, src_dir) = create_temp_project("compile_test", "");
    let options = CodeGenOptions::default();
    let mut lib_content = String::new();

    for &(name, source) in COMPILE_SPECS {
        let code = parse_and_generate(source, &options)
            .unwrap_or_else(|e| panic!("Failed to generate {}: {}", name, e));
        let mod_name = name.to_lowercase();
        let mod_file = src_dir.join(format!("{}.rs", mod_name));
        fs::write(&mod_file, &code)
            .unwrap_or_else(|e| panic!("Failed to write {}.rs: {}", mod_name, e));
        {
            use std::fmt::Write as _;
            writeln!(lib_content, "pub mod {};", mod_name).unwrap();
        }
    }

    fs::write(src_dir.join("lib.rs"), lib_content).expect("Failed to write lib.rs");
    let names: Vec<&str> = COMPILE_SPECS.iter().map(|&(n, _)| n).collect();
    cargo_check_or_panic(&temp_dir, &src_dir, &names);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_end_to_end_compile_recursive_operator() {
    use std::fs;

    let (temp_dir, src_dir) = create_temp_project("compile_recursive_test", "");
    let code = parse_and_generate(RECURSIVE_FACTORIAL_SPEC, &CodeGenOptions::default())
        .expect("recursive spec should codegen");
    fs::write(src_dir.join("recursive_factorial.rs"), &code)
        .expect("failed to write recursive_factorial.rs");
    fs::write(src_dir.join("lib.rs"), "pub mod recursive_factorial;\n")
        .expect("failed to write lib.rs");
    cargo_check_or_panic(&temp_dir, &src_dir, &["RecursiveFactorial"]);
}

/// End-to-end test that generates code, compiles it, and executes it
/// to verify semantic correctness of the generated state machine.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_end_to_end_execute() {
    use std::fs;

    let bin_toml = "[[bin]]\nname = \"exec_test\"\npath = \"src/main.rs\"\n\n";
    let (temp_dir, src_dir) = create_temp_project("exec_test", bin_toml);
    let options = CodeGenOptions {
        module_name: None,
        generate_proptest: false,
        generate_kani: false,
        generate_checker: true,
        checker_map: None,
    };

    for (name, source) in [
        ("bounded_counter", BOUNDED_COUNTER_SPEC),
        ("conflict", CONFLICT_SPEC),
        ("strict_counter", STRICT_COUNTER_SPEC),
    ] {
        let code = parse_and_generate(source, &options)
            .unwrap_or_else(|e| panic!("Failed to generate {}: {}", name, e));
        fs::write(src_dir.join(format!("{name}.rs")), &code)
            .unwrap_or_else(|e| panic!("Failed to write {name}.rs: {e}"));
    }

    fs::write(src_dir.join("main.rs"), EXEC_TEST_MAIN_CODE).expect("Failed to write main.rs");
    cargo_build_run_or_panic(&temp_dir);
}
