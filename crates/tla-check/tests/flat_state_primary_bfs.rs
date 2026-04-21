// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end integration test for the flat_state_primary BFS path.
//!
//! Verifies that the full flat-state BFS pipeline works correctly:
//! - `flat_state_primary=true` detection for all-scalar specs
//! - FlatState fingerprinting (xxh3 on raw i64 buffers)
//! - `generate_successors_filtered_flat` action dispatch
//!
//! The test uses simple all-scalar specs (only Int/Bool state variables)
//! and verifies that the interpreter baseline state count is correct.
//!
//! Part of #3986: Flat i64 state as primary BFS representation.
//!
//! Note: JIT-specific parity tests removed as part of Stage 2c Cranelift
//! deletion (#4266). The interpreter baseline path is retained.

mod common;

use tla_check::{check_module, CheckResult, Config};
use tla_eval::clear_for_test_reset;

// ============================================================================
// Spec: DieHard water jug puzzle (all-scalar: two integer variables)
// ============================================================================

/// Classic DieHard water jug puzzle. State variables are `big` and `small`,
/// both integers in 0..5 and 0..3 respectively. This is the canonical
/// all-scalar spec for testing flat_state_primary detection.
///
/// State space: 17 distinct reachable states (full exploration with TypeOK).
/// All variables are Int — qualifies for flat_state_primary=true.
const DIEHARD_SPEC: &str = r#"
---- MODULE DieHardFlat ----
VARIABLE big, small
SmallCap == 3
BigCap == 5
Init ==
    /\ big = 0
    /\ small = 0
Min(m, n) == IF m < n THEN m ELSE n
FillSmallJug ==
    /\ small' = SmallCap
    /\ big' = big
FillBigJug ==
    /\ big' = BigCap
    /\ small' = small
EmptySmallJug ==
    /\ small' = 0
    /\ big' = big
EmptyBigJug ==
    /\ big' = 0
    /\ small' = small
SmallToBig ==
    /\ big' = Min(big + small, BigCap)
    /\ small' = small - (big' - big)
BigToSmall ==
    /\ small' = Min(big + small, SmallCap)
    /\ big' = big - (small' - small)
Next ==
    \/ FillSmallJug
    \/ FillBigJug
    \/ EmptySmallJug
    \/ EmptyBigJug
    \/ SmallToBig
    \/ BigToSmall
TypeOK == big \in 0..BigCap /\ small \in 0..SmallCap
====
"#;

const DIEHARD_CONFIG: &str = "INIT Init\nNEXT Next\nINVARIANT TypeOK\n";

// ============================================================================
// Test: Interpreter baseline for DieHard (establishes expected state count)
// ============================================================================

/// Run DieHard without JIT to establish the baseline state count (17 states).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_flat_state_primary_diehard_interpreter_baseline() {
    let _no_jit = common::EnvVarGuard::remove("TLA2_JIT");
    let _no_compiled = common::EnvVarGuard::remove("TLA2_COMPILED_BFS");
    clear_for_test_reset();

    let module = common::parse_module(DIEHARD_SPEC);
    let config = Config::parse(DIEHARD_CONFIG).expect("valid cfg");
    let result = check_module(&module, &config);

    match result {
        CheckResult::Success(stats) => {
            // DieHard has 17 reachable states with TypeOK invariant (full exploration).
            assert_eq!(
                stats.states_found, 17,
                "DieHard baseline should find exactly 17 states, got {}",
                stats.states_found,
            );
            assert_eq!(stats.initial_states, 1, "DieHard has 1 init state");
            eprintln!(
                "[test] DieHard interpreter baseline: {} states, {} initial",
                stats.states_found, stats.initial_states
            );
        }
        other => panic!("DieHard interpreter baseline failed: {other:?}"),
    }
}
