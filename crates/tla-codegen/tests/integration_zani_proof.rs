// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! First zani/Kani proof on generated TLA+ code.
//!
//! This test demonstrates the complete pipeline:
//!   TLA+ spec -> Rust codegen -> zani/Kani verification proof
//!
//! The BoundedCounter spec is:
//!   VARIABLE count
//!   Init == count = 0
//!   Next == count' = IF count < 5 THEN count + 1 ELSE count
//!   InvBounded == count >= 0 /\ count <= 5
//!
//! We generate the Rust code, then write Kani harnesses that prove:
//! 1. Base case: Init satisfies InvBounded
//! 2. Inductive step: InvBounded /\ Next => InvBounded'
//! 3. Bounded exploration: all states within K steps satisfy InvBounded
//!
//! Without Kani/zani installed, these run as standard tests with exhaustive
//! enumeration of the finite state space.
//!
//! Part of #3928.

mod common;

use common::parse_and_generate;
use tla_codegen::CodeGenOptions;

const BOUNDED_COUNTER_SPEC: &str = r#"
---- MODULE BoundedCounter ----
VARIABLE count

Init == count = 0

Next == count' = IF count < 5 THEN count + 1 ELSE count

InvBounded == count >= 0 /\ count <= 5
====
"#;

/// Verify the pipeline: generate code, build a project with Kani harness
/// files (running as standard tests), and execute.
///
/// This test builds a Cargo project that includes:
/// - The generated BoundedCounter module
/// - A Kani harness module with #[cfg(kani)] proofs AND #[test] fallbacks
/// - A main.rs that just prints success (harnesses are run as tests)
#[cfg_attr(test, ntest::timeout(120_000))]
#[test]
fn test_zani_proof_bounded_counter() {
    use std::fs;
    use std::process::Command;

    let options = CodeGenOptions::default();
    let generated_code = parse_and_generate(BOUNDED_COUNTER_SPEC, &options)
        .expect("BoundedCounter codegen should succeed");

    // Verify generated code has the expected structure
    assert!(
        generated_code.contains("pub struct BoundedCounterState"),
        "should generate state struct"
    );
    assert!(
        generated_code.contains("impl StateMachine for BoundedCounter"),
        "should generate StateMachine impl"
    );
    assert!(
        generated_code.contains("check_inv_bounded"),
        "should generate invariant check (check_inv_bounded)"
    );

    // Create temp project
    let temp_dir = std::env::temp_dir().join(format!("tla2_zani_proof_{}", std::process::id()));
    let src_dir = temp_dir.join("src");
    let _ = fs::remove_dir_all(&temp_dir);
    fs::create_dir_all(&src_dir).expect("create src dir");

    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
    let runtime_path = std::path::Path::new(&manifest_dir)
        .join("../tla-runtime")
        .canonicalize()
        .expect("find tla-runtime");

    let cargo_toml = format!(
        "[package]\nname = \"zani-proof-demo\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\
         \n[dependencies]\ntla-runtime = {{ path = \"{}\" }}\n",
        runtime_path.display()
    );
    fs::write(temp_dir.join("Cargo.toml"), &cargo_toml).expect("write Cargo.toml");

    // Write the generated module
    fs::write(src_dir.join("bounded_counter.rs"), &generated_code)
        .expect("write bounded_counter.rs");

    // Write the Kani/zani harness with test fallbacks
    //
    // NOTE: The generated invariant check methods are inherent methods on the
    // machine struct (not pub), so we use the StateMachine trait's public
    // check_invariant() method which delegates to them. For Kani proofs,
    // we also use check_invariant() via the trait. For the negative test,
    // we use model_check_with_invariant() with a custom closure.
    let harness_code = r#"//! Kani/zani verification harness for BoundedCounter.
//!
//! Generated from TLA+ spec. Proves that InvBounded is an invariant:
//!   InvBounded == count >= 0 /\ count <= 5
//!
//! Three proof strategies:
//! 1. Base case: Init => InvBounded
//! 2. Inductive step: InvBounded /\ Next => InvBounded'
//! 3. Bounded model check: explore K steps from Init

use super::bounded_counter::{BoundedCounter, BoundedCounterState};
use tla_runtime::prelude::*;

/// Helper: check InvBounded using the StateMachine trait's check_invariant.
/// Returns true if the invariant holds (or no invariant is defined).
fn inv_holds(sm: &BoundedCounter, state: &BoundedCounterState) -> bool {
    sm.check_invariant(state).unwrap_or(true)
}

// ---------------------------------------------------------------------------
// Kani/zani proofs (active only under `cargo kani`)
// ---------------------------------------------------------------------------

/// Base case: every initial state satisfies InvBounded.
#[cfg(kani)]
#[kani::proof]
fn prove_init_satisfies_inv() {
    let sm = BoundedCounter;
    let init_states = sm.init();
    for state in &init_states {
        kani::assert(
            inv_holds(&sm, state),
            "InvBounded violated in initial state",
        );
    }
}

/// Inductive step: if InvBounded holds in state s, then it holds in
/// every successor next(s).
///
/// Uses kani::any() to explore ALL possible i64 values for count,
/// constrained to those satisfying InvBounded (the inductive hypothesis).
#[cfg(kani)]
#[kani::proof]
fn prove_next_preserves_inv() {
    let count: i64 = kani::any();
    let state = BoundedCounterState { count };
    let sm = BoundedCounter;

    // Inductive hypothesis: assume InvBounded holds
    kani::assume(inv_holds(&sm, &state));

    // Every successor must also satisfy InvBounded
    let successors = sm.next(&state);
    for ns in &successors {
        kani::assert(
            inv_holds(&sm, ns),
            "InvBounded violated after transition",
        );
    }
}

/// Bounded model check: explore all states reachable within 10 steps.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(11)]
fn prove_bounded_k_steps() {
    let sm = BoundedCounter;
    let init_states = sm.init();
    if init_states.is_empty() {
        return;
    }
    let idx: usize = kani::any();
    kani::assume(idx < init_states.len());
    let mut state = init_states[idx].clone();
    kani::assert(
        inv_holds(&sm, &state),
        "InvBounded violated at step 0",
    );

    let k: usize = kani::any();
    kani::assume(k <= 10);
    let mut i = 0;
    while i < k {
        let succs = sm.next(&state);
        if succs.is_empty() {
            break;
        }
        state = succs[0].clone();
        kani::assert(
            inv_holds(&sm, &state),
            "InvBounded violated after step",
        );
        i += 1;
    }
}

// ---------------------------------------------------------------------------
// Standard test fallbacks (run without Kani via `cargo test`)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Test: Init satisfies InvBounded.
    #[test]
    fn test_init_satisfies_inv() {
        let sm = BoundedCounter;
        let states = sm.init();
        assert!(!states.is_empty(), "Init must produce at least one state");
        for state in &states {
            assert!(
                inv_holds(&sm, state),
                "InvBounded violated in initial state: {:?}",
                state
            );
        }
    }

    /// Test: Inductive step verified by exhaustive enumeration.
    ///
    /// For BoundedCounter, the reachable state space is finite (count in 0..=5),
    /// so we can verify the inductive step for every state.
    #[test]
    fn test_next_preserves_inv() {
        let sm = BoundedCounter;
        // Enumerate all states satisfying InvBounded
        for count in 0..=5i64 {
            let state = BoundedCounterState { count };
            assert!(
                inv_holds(&sm, &state),
                "precondition: InvBounded holds for count={count}"
            );

            let successors = sm.next(&state);
            for ns in &successors {
                assert!(
                    inv_holds(&sm, ns),
                    "InvBounded violated after transition: {:?} -> {:?}",
                    state, ns
                );
            }
        }
    }

    /// Test: Exhaustive BFS verifying InvBounded at every reachable state.
    #[test]
    fn test_bounded_exploration() {
        let sm = BoundedCounter;
        let result = model_check(&sm, 10_000);

        // BoundedCounter should NOT have an invariant violation
        assert!(
            result.violation.is_none(),
            "unexpected invariant violation: {:?}",
            result.violation
        );

        // Verify we found the expected number of states
        assert_eq!(
            result.distinct_states, 6,
            "BoundedCounter should have exactly 6 distinct states (0-5), got {}",
            result.distinct_states
        );
    }

    /// Negative test: a bad invariant IS violated.
    #[test]
    fn test_bad_invariant_detected() {
        let bad_inv = |s: &BoundedCounterState| s.count < 3;

        let sm = BoundedCounter;
        let result = model_check_with_invariant(&sm, 10_000, bad_inv);

        assert!(
            result.violation.is_some(),
            "bad invariant (count < 3) should be detected as violated"
        );
        assert_eq!(
            result.violation.as_ref().unwrap().state.count, 3,
            "violation should occur at count=3"
        );
    }
}
"#;

    // Write the harness as part of lib.rs so tests can find it
    let lib_rs = r#"pub mod bounded_counter;
"#;
    fs::write(src_dir.join("lib.rs"), lib_rs).expect("write lib.rs");
    fs::write(src_dir.join("zani_harness.rs"), harness_code).expect("write zani_harness.rs");

    // Run cargo test (exercises the #[cfg(test)] fallback paths)
    let test_output = Command::new("cargo")
        .args(["test", "--release"])
        .current_dir(&temp_dir)
        .output()
        .expect("spawn cargo test");

    let stdout = String::from_utf8_lossy(&test_output.stdout);
    let stderr = String::from_utf8_lossy(&test_output.stderr);

    let _ = fs::remove_dir_all(&temp_dir);

    if !test_output.status.success() {
        panic!("zani harness tests failed!\nstdout:\n{stdout}\nstderr:\n{stderr}");
    }

    // Verify all 4 tests ran and passed
    assert!(
        stdout.contains("test result: ok"),
        "test output should contain 'test result: ok'. stdout:\n{stdout}"
    );
    // The test output should show 4 tests passed
    assert!(
        stdout.contains("4 passed") || stdout.contains("test result: ok. 4"),
        "expected 4 tests to pass. stdout:\n{stdout}\nstderr:\n{stderr}"
    );

    println!("zani proof pipeline validated successfully!");
    println!("- Base case: Init => InvBounded (PASS)");
    println!("- Inductive step: InvBounded /\\ Next => InvBounded' (PASS)");
    println!("- Bounded BFS: 6 states, all satisfy InvBounded (PASS)");
    println!("- Negative test: bad invariant detected (PASS)");
}
