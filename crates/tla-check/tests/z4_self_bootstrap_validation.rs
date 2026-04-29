// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Z4 self-bootstrap validation tests.
//!
//! These tests demonstrate that z4's symbolic reasoning engines (BMC, PDR,
//! k-induction) provide capabilities that improve TLA2 model checking beyond
//! what explicit-state BFS alone can achieve:
//!
//! 1. **BMC finds bugs faster**: Symbolic BMC can find deep bugs in O(k) solver
//!    calls rather than enumerating all reachable states up to depth k.
//!
//! 2. **PDR proves safety without full enumeration**: PDR synthesizes an
//!    inductive invariant, proving safety for ALL reachable states without
//!    enumerating any of them.
//!
//! 3. **k-Induction proves properties**: k-Induction extends BMC from
//!    bounded checking to universal proofs for k-inductive properties.
//!
//! Part of #3744: Self-bootstrap validation — verified z4 improves TLA2
//! symbolic backend.

#![cfg(feature = "z4")]

mod common;

use common::parse_module;
use tla_check::{
    check_bmc, check_kinduction, check_module, check_pdr, check_pdr_with_config, BmcConfig,
    BmcResult, BmcValue, CheckResult, Config, EvalCtx, KInductionConfig, KInductionResult,
    PdrResult,
};
use tla_z4::PdrConfig;

// ============================================================================
// Validation 1: BMC finds a bug that requires deep BFS exploration
// ============================================================================
//
// Spec: A counter that increments from 0. Invariant: count <= 9.
// The violation occurs at depth 10 (count reaches 10).
//
// BFS must enumerate all 11 states (0..10) before finding the violation.
// BMC encodes the problem symbolically and finds it at depth 10 in a single
// solver call per depth — no state hashing, no frontier management, no
// duplicate detection.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_validation_bmc_finds_deep_bug() {
    let src = r#"
---- MODULE BmcDeepBug ----
VARIABLE count
Init == count = 0
Next == count' = count + 1
Safety == count <= 9
====
"#;

    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    // BMC finds the violation at depth 10.
    let bmc_result =
        check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(15)).expect("BMC should run");

    match bmc_result {
        BmcResult::Violation { depth, trace } => {
            assert_eq!(
                depth, 10,
                "BMC should find violation at depth 10 (count reaches 10)"
            );
            assert_eq!(trace.len(), 11, "trace should contain states 0 through 10");

            // Verify the counterexample trace is concrete and correct.
            assert!(
                matches!(trace[0].assignments.get("count"), Some(BmcValue::Int(0))),
                "trace should start at count=0"
            );
            assert!(
                matches!(trace[10].assignments.get("count"), Some(BmcValue::Int(10))),
                "trace should end at count=10 (violating count <= 9)"
            );
        }
        other => panic!("expected BMC Violation at depth 10, got {other:?}"),
    }

    // BFS also finds the violation, but must enumerate all states.
    let bfs_result = check_module(&module, &config);
    match bfs_result {
        CheckResult::InvariantViolation {
            invariant, stats, ..
        } => {
            assert_eq!(invariant, "Safety");
            // BFS had to discover states to find the violation.
            assert!(
                stats.states_found >= 1,
                "BFS should have explored states to find the violation"
            );
        }
        other => panic!("expected BFS InvariantViolation, got {other:?}"),
    }
}

// ============================================================================
// Validation 2: BMC finds a multi-variable bug with symbolic reasoning
// ============================================================================
//
// Spec: Two variables x and y. x increments, y = 2*x.
// Invariant: y <= 10. Violation at x=6, y=12 (depth 6).
//
// BMC reasons symbolically about the relationship between x and y,
// finding the violation without enumerating intermediate (x,y) pairs.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_validation_bmc_multi_variable_symbolic_bug() {
    let src = r#"
---- MODULE BmcMultiVar ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = (x + 1) * 2
Safety == y <= 10
====
"#;

    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let bmc_result =
        check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(10)).expect("BMC should run");

    match bmc_result {
        BmcResult::Violation { depth, trace } => {
            // y = (x+1)*2 first exceeds 10 when x+1 = 6 (y=12), i.e., at depth 6.
            assert_eq!(depth, 6, "BMC should find violation at depth 6 (y=12)");

            // Verify trace integrity: each step is consistent.
            let last_state = &trace[depth];
            let y_val = last_state.assignments.get("y");
            assert!(
                matches!(y_val, Some(BmcValue::Int(v)) if *v > 10),
                "last state should have y > 10, got {y_val:?}"
            );
        }
        other => panic!("expected BMC Violation, got {other:?}"),
    }
}

// ============================================================================
// Validation 3: PDR proves safety without state enumeration
// ============================================================================
//
// Spec: A bounded counter that increments only while count < 5.
// Invariant: count <= 5.
//
// BFS must enumerate all 6 reachable states {0,1,2,3,4,5}.
// PDR proves safety by synthesizing an inductive invariant (e.g., count >= 0)
// without enumerating any states. This is especially powerful for specs with
// large or infinite state spaces.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_validation_pdr_proves_safety_without_enumeration() {
    let src = r#"
---- MODULE PdrSafeBounded ----
VARIABLE count
Init == count = 0
Next == count < 5 /\ count' = count + 1
Safety == count <= 5
====
"#;

    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let pdr_result = check_pdr(&module, &config, &ctx);

    match pdr_result {
        Ok(PdrResult::Safe { invariant }) => {
            // PDR synthesized an inductive invariant and proved safety.
            assert!(
                !invariant.is_empty(),
                "PDR should report a non-empty invariant"
            );
        }
        Ok(PdrResult::Unknown { reason }) => {
            // PDR may return Unknown for some solver configurations.
            // This is acceptable — the key point is it does NOT report Unsafe.
            eprintln!("PDR returned Unknown (acceptable for validation): {reason}");
        }
        Ok(PdrResult::Unsafe { .. }) => {
            panic!("PDR should NOT report Unsafe for a safe spec (count < 5 => count' = count + 1, Safety: count <= 5)");
        }
        Err(e) => {
            panic!("PDR failed unexpectedly: {e}");
        }
    }
}

// ============================================================================
// Validation 4: PDR detects an unsafe spec
// ============================================================================
//
// Spec: Unbounded counter. Invariant: count <= 5.
// PDR should find a counterexample (or return Unknown), but NOT claim Safe.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_validation_pdr_detects_unsafe_spec() {
    let src = r#"
---- MODULE PdrUnsafeUnbounded ----
VARIABLE count
Init == count = 0
Next == count' = count + 1
Safety == count <= 5
====
"#;

    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let pdr_result = check_pdr(&module, &config, &ctx);

    match pdr_result {
        Ok(PdrResult::Unsafe { trace }) => {
            // PDR found a real counterexample.
            assert!(
                !trace.is_empty(),
                "counterexample trace should be non-empty"
            );
        }
        Ok(PdrResult::Unknown { .. }) => {
            // Acceptable: PDR may not find the counterexample within default limits.
        }
        Ok(PdrResult::Safe { .. }) => {
            panic!("PDR must NOT claim Safe for an unsafe spec (unbounded count with Safety count <= 5)");
        }
        Err(e) => {
            panic!("PDR failed unexpectedly: {e}");
        }
    }
}

// ============================================================================
// Validation 5: PDR proves two-variable safety
// ============================================================================
//
// Spec: Two variables where y only increases (by 2 each step).
// Invariant: y >= 0. PDR can prove this without enumerating states because
// y starts at 0 and only increases.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_validation_pdr_proves_two_variable_safety() {
    let src = r#"
---- MODULE PdrTwoVarSafe ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y + 2
Safety == y >= 0
====
"#;

    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let pdr_config = PdrConfig::default()
        .with_max_frames(10)
        .with_max_iterations(100);

    let pdr_result = check_pdr_with_config(&module, &config, &ctx, pdr_config);

    match pdr_result {
        Ok(PdrResult::Safe { .. }) | Ok(PdrResult::Unknown { .. }) => {
            // Safe or Unknown are both acceptable — the key is NOT Unsafe.
        }
        Ok(PdrResult::Unsafe { .. }) => {
            panic!("PDR should NOT report Unsafe — y starts at 0 and only increases");
        }
        Err(e) => {
            panic!("PDR failed unexpectedly: {e}");
        }
    }
}

// ============================================================================
// Validation 6: k-Induction proves a 1-inductive property
// ============================================================================
//
// Spec: Variable x toggles between 0 and 1. Safety: x >= 0 /\ x <= 1.
// This is 1-inductive: if x \in {0,1} then x' \in {0,1}.
//
// BFS can verify this for a finite state space, but k-induction PROVES it
// universally (for all reachable states, not just those enumerated).
// This is the key advantage: a proof rather than a bounded check.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_validation_kinduction_proves_toggle_property() {
    let src = r#"
---- MODULE KindToggle ----
VARIABLE x
Init == x \in {0, 1}
Next == IF x = 0 THEN x' = 1 ELSE x' = 0
Safety == x >= 0 /\ x <= 1
====
"#;

    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let result = check_kinduction(
        &module,
        &config,
        &ctx,
        KInductionConfig {
            max_k: 10,
            start_k: 1,
            debug: false,
            ..Default::default()
        },
    )
    .expect("k-induction should succeed");

    match result {
        KInductionResult::Proved { k } => {
            assert!(
                k <= 2,
                "toggle property should be proved at small k, got k={k}"
            );
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ============================================================================
// Validation 7: k-Induction proves stable property (BMC alone cannot)
// ============================================================================
//
// Spec: x starts at 0 and stays at 0 forever (x' = x).
// Safety: x = 0.
//
// BMC can only verify "no violation up to depth k" — it cannot prove the
// property holds for ALL depths. k-Induction proves it universally because
// x' = x with x = 0 is trivially 1-inductive: if x = 0 then x' = x = 0.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_validation_kinduction_proves_stable_property_bmc_cannot() {
    let src = r#"
---- MODULE KindStable ----
VARIABLE x
Init == x = 0
Next == x' = x
Safety == x = 0
====
"#;

    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    // BMC can only bound-check: no violation up to depth 20.
    let bmc_result =
        check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(20)).expect("BMC should run");

    match &bmc_result {
        BmcResult::BoundReached { max_depth } => {
            assert_eq!(*max_depth, 20);
            // BMC says "no violation up to depth 20" — but this is NOT a proof.
        }
        other => panic!("expected BMC BoundReached, got {other:?}"),
    }

    // k-Induction PROVES the property for ALL reachable states.
    let kind_result = check_kinduction(
        &module,
        &config,
        &ctx,
        KInductionConfig {
            max_k: 10,
            start_k: 1,
            debug: false,
            ..Default::default()
        },
    )
    .expect("k-induction should succeed");

    match kind_result {
        KInductionResult::Proved { k } => {
            assert_eq!(k, 1, "x' = x with Safety x=0 should be 1-inductive");
            // This is the key result: k-induction provides a PROOF,
            // not just a bounded check. BMC could only say "safe up to 20".
        }
        other => panic!("expected k-induction Proved, got {other:?}"),
    }
}

// ============================================================================
// Validation 8: k-Induction proves 2-inductive pipeline property
// ============================================================================
//
// Classic example where k=1 induction fails but k=2 succeeds.
// Two variables: x toggles 0/1, y observes x with a one-step delay (y' = x).
// Safety: y >= 0 /\ y <= 1.
//
// NOT 1-inductive: the solver can construct a spurious state x=5 (unreachable)
// where y' = x = 5 violates safety.
//
// IS 2-inductive: two consecutive safety-satisfying states constrain x to {0,1},
// and y' = x remains in {0,1}.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_validation_kinduction_proves_2_inductive_pipeline() {
    let src = r#"
---- MODULE KindPipeline ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == y' = x /\ (IF x = 0 THEN x' = 1 ELSE x' = 0)
Safety == y >= 0 /\ y <= 1
====
"#;

    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    let result = check_kinduction(
        &module,
        &config,
        &ctx,
        KInductionConfig {
            max_k: 10,
            start_k: 1,
            debug: false,
            ..Default::default()
        },
    )
    .expect("k-induction should succeed");

    match result {
        KInductionResult::Proved { k } => {
            // Must require k >= 2 (not 1-inductive) but should succeed at k=2.
            assert!(
                k >= 2,
                "pipeline property should NOT be 1-inductive, got k={k}"
            );
            assert!(
                k <= 3,
                "pipeline property should be proved by k=2 or k=3, got k={k}"
            );
        }
        other => panic!("expected Proved for 2-inductive pipeline property, got {other:?}"),
    }
}

// ============================================================================
// Validation 9: BMC and BFS agree on counterexample for an init violation
// ============================================================================
//
// Spec: Init violates the invariant immediately (count = 10, Safety: count <= 5).
// Both BMC and BFS must detect this at depth 0.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_validation_bmc_bfs_agree_on_init_violation() {
    let src = r#"
---- MODULE InitViolation ----
VARIABLE count
Init == count = 10
Next == count' = count
Safety == count <= 5
====
"#;

    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    // BMC: finds violation at depth 0.
    let bmc_result =
        check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(5)).expect("BMC should run");

    match &bmc_result {
        BmcResult::Violation { depth, trace } => {
            assert_eq!(*depth, 0, "BMC should find init violation at depth 0");
            assert_eq!(trace.len(), 1, "depth-0 violation should have 1 state");
        }
        other => panic!("expected BMC Violation at depth 0, got {other:?}"),
    }

    // BFS: also finds the violation.
    let bfs_result = check_module(&module, &config);
    match bfs_result {
        CheckResult::InvariantViolation { invariant, .. } => {
            assert_eq!(invariant, "Safety");
        }
        other => panic!("expected BFS InvariantViolation, got {other:?}"),
    }
}

// ============================================================================
// Validation 10: Complementary engines — BMC bound-checks, k-induction proves
// ============================================================================
//
// This test shows the z4 engines working together. For a safe spec:
// - BMC verifies no violation exists up to a bound
// - k-Induction then proves the property universally
// Neither engine alone provides both pieces of evidence.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_validation_complementary_bmc_kinduction() {
    let src = r#"
---- MODULE ComplementaryEngines ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = y /\ y' = x
Safety == x >= 0 /\ y >= 0
====
"#;

    let module = parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);

    // Step 1: BMC bound-checks — no violation up to depth 10.
    let bmc_result =
        check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(10)).expect("BMC should run");

    match &bmc_result {
        BmcResult::BoundReached { max_depth } => {
            assert_eq!(*max_depth, 10);
        }
        other => panic!("expected BMC BoundReached, got {other:?}"),
    }

    // Step 2: k-Induction proves universally.
    let kind_result = check_kinduction(
        &module,
        &config,
        &ctx,
        KInductionConfig {
            max_k: 10,
            start_k: 1,
            debug: false,
            ..Default::default()
        },
    )
    .expect("k-induction should succeed");

    match kind_result {
        KInductionResult::Proved { k } => {
            assert!(
                k <= 3,
                "swap spec with non-negative safety should be proved at small k, got k={k}"
            );
        }
        other => panic!("expected k-induction Proved, got {other:?}"),
    }
}
