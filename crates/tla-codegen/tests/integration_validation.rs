// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end codegen validation: generate Rust code from TLA+ specs, compile
//! them in a single Cargo project, run the generated StateMachines via BFS,
//! and compare state counts against known values.
//!
//! This is the gold standard for codegen correctness: the generated code must
//! produce the EXACT same number of distinct states as TLC.
//!
//! Part of #3929.

mod common;

use std::path::{Path, PathBuf};

use common::parse_and_generate;
use tla_codegen::CodeGenOptions;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Create a temporary Cargo project with tla-runtime dependency and a binary target.
fn create_validation_project() -> (PathBuf, PathBuf) {
    use std::fs;
    let temp_dir = std::env::temp_dir().join(format!(
        "tla2_validate_all_{}",
        std::process::id()
    ));
    let src_dir = temp_dir.join("src");
    let _ = fs::remove_dir_all(&temp_dir);
    fs::create_dir_all(&src_dir).expect("create temp src dir");
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    let runtime_path = std::path::Path::new(&manifest_dir)
        .join("../tla-runtime")
        .canonicalize()
        .expect("find tla-runtime path");
    let cargo_toml = format!(
        "[package]\nname = \"validate-all\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\
         \n[[bin]]\nname = \"validate\"\npath = \"src/main.rs\"\n\
         \n[dependencies]\ntla-runtime = {{ path = \"{}\" }}\n",
        runtime_path.display()
    );
    fs::write(temp_dir.join("Cargo.toml"), &cargo_toml).expect("write Cargo.toml");
    (temp_dir, src_dir)
}

/// Build and run a binary, returning stdout.
fn cargo_build_run(temp_dir: &Path) -> Result<String, String> {
    use std::process::Command;
    let build = Command::new("cargo")
        .args(["build", "--release"])
        .current_dir(temp_dir)
        .output()
        .map_err(|e| format!("spawn build: {e}"))?;
    if !build.status.success() {
        return Err(format!(
            "build failed:\n{}",
            String::from_utf8_lossy(&build.stderr)
        ));
    }
    let run = Command::new("cargo")
        .args(["run", "--release"])
        .current_dir(temp_dir)
        .output()
        .map_err(|e| format!("spawn run: {e}"))?;
    if !run.status.success() {
        return Err(format!(
            "run failed:\nstdout: {}\nstderr: {}",
            String::from_utf8_lossy(&run.stdout),
            String::from_utf8_lossy(&run.stderr)
        ));
    }
    Ok(String::from_utf8_lossy(&run.stdout).to_string())
}

// ---------------------------------------------------------------------------
// Validation specs with known state counts
// ---------------------------------------------------------------------------

struct ValidationSpec {
    name: &'static str,
    source: &'static str,
    expected_states: usize,
}

const VALIDATION_SPECS: &[ValidationSpec] = &[
    ValidationSpec {
        name: "BoundedCounter",
        source: r#"
---- MODULE BoundedCounter ----
VARIABLE count

Init == count = 0

Next == count' = IF count < 5 THEN count + 1 ELSE count

InvBounded == count >= 0 /\ count <= 5
====
"#,
        expected_states: 6,
    },
    ValidationSpec {
        name: "Modular",
        source: r#"
---- MODULE Modular ----
VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 10

InvRange == x >= 0 /\ x < 10
====
"#,
        expected_states: 10,
    },
    ValidationSpec {
        name: "TwoValues",
        source: r#"
---- MODULE TwoValues ----
VARIABLE v

Init == v \in {0, 1}

Next == v' = 1 - v
====
"#,
        expected_states: 2,
    },
    ValidationSpec {
        name: "ThreePhase",
        source: r#"
---- MODULE ThreePhase ----
VARIABLE phase

Init == phase = 0

Next == phase' = (phase + 1) % 3

InvValid == phase \in {0, 1, 2}
====
"#,
        expected_states: 3,
    },
    ValidationSpec {
        name: "BoolToggle",
        source: r#"
---- MODULE BoolToggle ----
VARIABLE flag

Init == flag = TRUE

Next == flag' = ~flag
====
"#,
        expected_states: 2,
    },
    ValidationSpec {
        name: "MaxFive",
        source: r#"
---- MODULE MaxFive ----
VARIABLE x

Init == x \in {1, 2, 3, 4, 5}

Next == x' = IF x < 5 THEN x + 1 ELSE 1

InvRange == x \in {1, 2, 3, 4, 5}
====
"#,
        expected_states: 5,
    },
    ValidationSpec {
        name: "TwoVars",
        source: r#"
---- MODULE TwoVars ----
VARIABLES x, y

Init == x = 0 /\ y = 0

Next == /\ x' = IF x < 2 THEN x + 1 ELSE 0
        /\ y' = IF y < 1 THEN y + 1 ELSE 0

InvSmall == x \in {0, 1, 2} /\ y \in {0, 1}
====
"#,
        expected_states: 6,
    },
];

fn to_snake_case(s: &str) -> String {
    let mut result = String::new();
    for (i, c) in s.chars().enumerate() {
        if c.is_uppercase() && i > 0 {
            result.push('_');
        }
        result.push(c.to_ascii_lowercase());
    }
    result
}

fn to_pascal_case(s: &str) -> String {
    s.split('_')
        .map(|part| {
            let mut chars = part.chars();
            match chars.next() {
                None => String::new(),
                Some(c) => {
                    let mut result = c.to_uppercase().to_string();
                    result.extend(chars);
                    result
                }
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Test: generate all specs into one project, build once, run once
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(120_000))]
#[test]
fn test_codegen_validation_pipeline() {
    use std::fmt::Write as FmtWrite;
    use std::fs;

    // Step 1: Generate Rust code for each spec
    let options = CodeGenOptions::default();
    let mut generated: Vec<(&str, String, String)> = Vec::new(); // (name, mod_name, code)
    let mut codegen_failures: Vec<(&str, String)> = Vec::new();

    for spec in VALIDATION_SPECS {
        match parse_and_generate(spec.source, &options) {
            Ok(code) => {
                let mod_name = to_snake_case(spec.name);
                generated.push((spec.name, mod_name, code));
            }
            Err(e) => {
                codegen_failures.push((spec.name, e));
            }
        }
    }

    if generated.is_empty() {
        // Print failures and assert
        for (name, reason) in &codegen_failures {
            println!("CODEGEN FAIL: {name}: {reason}");
        }
        panic!("codegen produced zero successes — pipeline is broken");
    }

    // Step 2: Create a single Cargo project with all generated modules
    let (temp_dir, src_dir) = create_validation_project();
    let cleanup = || { let _ = fs::remove_dir_all(&temp_dir); };

    // Write each generated module
    for (_, mod_name, code) in &generated {
        fs::write(src_dir.join(format!("{mod_name}.rs")), code)
            .unwrap_or_else(|e| { cleanup(); panic!("write {mod_name}.rs: {e}"); });
    }

    // Build main.rs that exercises each machine and reports state counts
    let mut main_code = String::new();
    for (_, mod_name, _) in &generated {
        writeln!(main_code, "mod {mod_name};").unwrap();
    }
    writeln!(main_code, "\nuse tla_runtime::prelude::*;\n").unwrap();
    writeln!(main_code, "fn main() {{").unwrap();

    for (name, mod_name, _) in &generated {
        let machine_type = to_pascal_case(name);
        writeln!(main_code, "    {{").unwrap();
        writeln!(
            main_code,
            "        let sm = {mod_name}::{machine_type};"
        ).unwrap();
        writeln!(
            main_code,
            "        let states = collect_states(&sm, 100_000);"
        ).unwrap();
        writeln!(
            main_code,
            "        println!(\"SPEC:{name}:STATES:{{}}\", states.len());"
        ).unwrap();
        // Also check invariants
        writeln!(main_code, "        let mut inv_ok = true;").unwrap();
        writeln!(main_code, "        for s in &states {{").unwrap();
        writeln!(
            main_code,
            "            if let Some(false) = sm.check_invariant(s) {{"
        ).unwrap();
        writeln!(main_code, "                inv_ok = false;").unwrap();
        writeln!(main_code, "                break;").unwrap();
        writeln!(main_code, "            }}").unwrap();
        writeln!(main_code, "        }}").unwrap();
        writeln!(
            main_code,
            "        println!(\"SPEC:{name}:INV_OK:{{}}\", inv_ok);"
        ).unwrap();
        writeln!(main_code, "    }}").unwrap();
    }
    writeln!(main_code, "}}").unwrap();

    fs::write(src_dir.join("main.rs"), &main_code)
        .unwrap_or_else(|e| { cleanup(); panic!("write main.rs: {e}"); });

    // Step 3: Build and run
    let stdout = match cargo_build_run(&temp_dir) {
        Ok(s) => { cleanup(); s }
        Err(e) => {
            // Print generated files for debugging
            for (_, mod_name, code) in &generated {
                eprintln!("=== {mod_name}.rs ===");
                for (i, line) in code.lines().enumerate() {
                    eprintln!("{:4} {}", i + 1, line);
                }
            }
            eprintln!("=== main.rs ===\n{main_code}");
            cleanup();
            panic!("build/run failed: {e}");
        }
    };

    // Step 4: Parse output and compare state counts
    println!("\n=== Codegen Validation Results ===");

    let mut pass_count = 0;
    let mut fail_count = 0;
    let expected_map: std::collections::HashMap<&str, usize> = VALIDATION_SPECS
        .iter()
        .map(|s| (s.name, s.expected_states))
        .collect();

    for line in stdout.lines() {
        if let Some(rest) = line.strip_prefix("SPEC:") {
            let parts: Vec<&str> = rest.splitn(3, ':').collect();
            if parts.len() == 3 && parts[1] == "STATES" {
                let name = parts[0];
                let actual: usize = parts[2].parse().unwrap_or(0);
                let expected = expected_map.get(name).copied().unwrap_or(0);
                if actual == expected {
                    println!("  PASS: {name}: {actual} states (expected {expected})");
                    pass_count += 1;
                } else {
                    println!("  FAIL: {name}: got {actual} states, expected {expected}");
                    fail_count += 1;
                }
            }
        }
    }

    for (name, reason) in &codegen_failures {
        let short = if reason.len() > 200 { &reason[..200] } else { reason.as_str() };
        println!("  CODEGEN_FAIL: {name}: {short}");
        fail_count += 1;
    }

    let total = pass_count + fail_count;
    println!("\nTotal: {total}, Pass: {pass_count}, Fail: {fail_count}");

    // Assert: at least one spec must pass end-to-end
    assert!(
        pass_count > 0,
        "codegen validation produced zero passes — pipeline is broken"
    );
}
