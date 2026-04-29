// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use super::*;
use crate::bind_constants_from_config;
use crate::test_support::parse_module;
use tla_z4::BmcValue;

fn check_spec(src: &str, max_depth: usize) -> Result<BmcResult, BmcError> {
    let module = parse_module(src);
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(max_depth))
}

/// Check a spec using incremental BMC (reuses solver across depths). Part of #3724.
fn check_spec_incremental(src: &str, max_depth: usize) -> Result<BmcResult, BmcError> {
    let module = parse_module(src);
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    check_bmc(
        &module,
        &config,
        &ctx,
        BmcConfig {
            max_depth,
            incremental: true,
            ..BmcConfig::default()
        },
    )
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_end_to_end_violation_depth() {
    let src = r#"
---- MODULE UnsafeCounter ----
VARIABLE count
Init == count = 0
Next == count' = count + 1
Safety == count <= 5
====
"#;

    let result = check_spec(src, 10).expect("BMC should succeed");
    match result {
        BmcResult::Violation { depth, trace } => {
            assert_eq!(depth, 6, "violation should be discovered at depth 6");
            assert_eq!(trace.len(), 7, "trace should contain states 0 through 6");
            assert!(matches!(
                trace[6].assignments.get("count"),
                Some(BmcValue::Int(6))
            ));
        }
        other => panic!("expected Violation, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_end_to_end_bound_reached() {
    let src = r#"
---- MODULE StableCounter ----
VARIABLE x
Init == x \in {0, 1}
Next == x' = x
Safety == x >= 0
====
"#;

    let result = check_spec(src, 5).expect("BMC should succeed");
    match result {
        BmcResult::BoundReached { max_depth } => assert_eq!(max_depth, 5),
        other => panic!("expected BoundReached, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_end_to_end_init_violation_depth_zero() {
    let src = r#"
---- MODULE InitViolation ----
VARIABLE count
Init == count = 10
Next == count' = count
Safety == count <= 5
====
"#;

    let result = check_spec(src, 5).expect("BMC should succeed");
    match result {
        BmcResult::Violation { depth, trace } => {
            assert_eq!(
                depth, 0,
                "initial-state violation should be discovered at depth 0"
            );
            assert_eq!(
                trace.len(),
                1,
                "depth-0 violation should only report the init state"
            );
        }
        other => panic!("expected Violation, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_end_to_end_with_operator_expansion() {
    let src = r#"
---- MODULE OperatorExpansion ----
VARIABLE count
Inc == count' = count + 1
Init == count = 0
Next == count < 5 /\ Inc
Safety == count <= 5
====
"#;

    let result = check_spec(src, 5).expect("BMC should succeed");
    match result {
        BmcResult::BoundReached { max_depth } => assert_eq!(max_depth, 5),
        other => panic!("expected BoundReached, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_end_to_end_with_unchanged() {
    let src = r#"
---- MODULE UnchangedTest ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ UNCHANGED y
Safety == y = 0
====
"#;

    let result = check_spec(src, 5).expect("BMC should succeed");
    match result {
        BmcResult::BoundReached { max_depth } => assert_eq!(max_depth, 5),
        other => panic!("expected BoundReached, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_resolves_replacement_routed_next() {
    let src = r#"
---- MODULE BmcReplacementNext ----
VARIABLE x
Init == x = 0
Next == x' = x
MCNext == IF x < 2 THEN x' = x + 1 ELSE x' = x
Safety == x <= 1
====
"#;

    let module = parse_module(src);
    let mut config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };
    config.constants.insert(
        "Next".to_string(),
        crate::ConstantValue::Replacement("MCNext".to_string()),
    );

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let result = check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(3))
        .expect("replacement-routed NEXT should be accepted by symbolic BMC");
    match result {
        BmcResult::Violation { depth, trace } => {
            assert_eq!(
                depth, 2,
                "replacement-routed next should reach x = 2 at depth 2"
            );
            assert!(matches!(
                trace.last().and_then(|state| state.assignments.get("x")),
                Some(BmcValue::Int(2))
            ));
        }
        other => panic!("expected Violation via replacement-routed NEXT, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_with_zero_timeout_returns_unknown() {
    let src = r#"
---- MODULE TimeoutCounter ----
VARIABLE count
Init == count = 0
Next == count' = count + 1
Safety == count <= 5
====
"#;

    let module = parse_module(src);
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let result = check_bmc(
        &module,
        &config,
        &ctx,
        BmcConfig {
            max_depth: 10,
            solve_timeout: Some(Duration::ZERO),
            debug: false,
            incremental: false,
        },
    )
    .expect("zero-timeout BMC should return Unknown, not error");

    match result {
        BmcResult::Unknown { reason, .. } => {
            assert!(
                reason.contains("timed out") || reason.contains("unknown"),
                "unexpected unknown reason: {reason}"
            );
        }
        other => panic!("expected Unknown under zero timeout, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_reifies_config_constants_in_shared_expansion() {
    let src = r#"
---- MODULE BmcConfigConstant ----
CONSTANT N
VARIABLE x
Init == x \in 0..N
Next == x' = x
Safety == x <= N
====
"#;

    let module = parse_module(src);
    let mut config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };
    config.constants.insert(
        "N".to_string(),
        crate::ConstantValue::Value("3".to_string()),
    );

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);
    bind_constants_from_config(&mut ctx, &config).expect("config constants should bind");

    let result = check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(2))
        .expect("BMC should accept config-constant ranges");
    match result {
        BmcResult::BoundReached { max_depth } => assert_eq!(max_depth, 2),
        other => panic!("expected BoundReached, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Incremental BMC tests (Part of #3724)
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_incremental_violation_depth() {
    let src = r#"
---- MODULE IncrUnsafeCounter ----
VARIABLE count
Init == count = 0
Next == count' = count + 1
Safety == count <= 5
====
"#;

    let result = check_spec_incremental(src, 10).expect("incremental BMC should succeed");
    match result {
        BmcResult::Violation { depth, trace } => {
            assert_eq!(
                depth, 6,
                "incremental: violation should be discovered at depth 6"
            );
            assert_eq!(
                trace.len(),
                7,
                "incremental: trace should contain states 0 through 6"
            );
            assert!(matches!(
                trace[6].assignments.get("count"),
                Some(BmcValue::Int(6))
            ));
        }
        other => panic!("expected Violation, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_incremental_bound_reached() {
    let src = r#"
---- MODULE IncrStableCounter ----
VARIABLE x
Init == x \in {0, 1}
Next == x' = x
Safety == x >= 0
====
"#;

    let result = check_spec_incremental(src, 5).expect("incremental BMC should succeed");
    match result {
        BmcResult::BoundReached { max_depth } => assert_eq!(max_depth, 5),
        other => panic!("expected BoundReached, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_incremental_init_violation_depth_zero() {
    let src = r#"
---- MODULE IncrInitViolation ----
VARIABLE count
Init == count = 10
Next == count' = count
Safety == count <= 5
====
"#;

    let result = check_spec_incremental(src, 5).expect("incremental BMC should succeed");
    match result {
        BmcResult::Violation { depth, trace } => {
            assert_eq!(
                depth, 0,
                "incremental: initial-state violation should be discovered at depth 0"
            );
            assert_eq!(
                trace.len(),
                1,
                "incremental: depth-0 violation should only report the init state"
            );
        }
        other => panic!("expected Violation, got {other:?}"),
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_incremental_with_unchanged() {
    let src = r#"
---- MODULE IncrUnchangedTest ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ UNCHANGED y
Safety == y = 0
====
"#;

    let result = check_spec_incremental(src, 5).expect("incremental BMC should succeed");
    match result {
        BmcResult::BoundReached { max_depth } => assert_eq!(max_depth, 5),
        other => panic!("expected BoundReached, got {other:?}"),
    }
}

/// Verify that incremental and non-incremental BMC produce identical results. Part of #3724.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_incremental_matches_per_depth() {
    let src = r#"
---- MODULE IncrMatchCheck ----
VARIABLE count
Init == count = 0
Next == count' = count + 1
Safety == count <= 5
====
"#;

    let result_per_depth = check_spec(src, 10).expect("per-depth BMC should succeed");
    let result_incremental =
        check_spec_incremental(src, 10).expect("incremental BMC should succeed");

    match (&result_per_depth, &result_incremental) {
        (
            BmcResult::Violation {
                depth: d1,
                trace: t1,
            },
            BmcResult::Violation {
                depth: d2,
                trace: t2,
            },
        ) => {
            assert_eq!(
                d1, d2,
                "violation depth must match between per-depth and incremental"
            );
            assert_eq!(t1.len(), t2.len(), "trace length must match");
        }
        _ => panic!(
            "expected both Violation, got per_depth={result_per_depth:?}, incr={result_incremental:?}"
        ),
    }
}

// ---------------------------------------------------------------------------
// Compound type end-to-end tests (sets, functions, sequences)
// Part of #3778 (sets), #3786 (functions), #3793 (sequences).
// ---------------------------------------------------------------------------

/// Test: Set-typed variable stays safe when x remains in the set.
///
/// `x \in {1,2,3}` across 3 steps — safety `x <= 3` always holds.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_e2e_set_membership_safe() {
    let src = r#"
---- MODULE SetMemberSafe ----
VARIABLE x
Init == x \in {1, 2, 3}
Next == x' \in {1, 2, 3}
Safety == x <= 3
====
"#;

    let result = check_spec(src, 3).expect("BMC should succeed");
    match result {
        BmcResult::BoundReached { max_depth } => assert_eq!(max_depth, 3),
        other => panic!("expected BoundReached, got {other:?}"),
    }
}

/// Test: x increments past the safe range — violation detected by BMC.
///
/// Init: x = 0, Next: x' = x + 1, Safety: x \in {0,1,2,3,4,5}
/// At depth 6, x = 6 which violates Safety.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_e2e_set_membership_violation() {
    let src = r#"
---- MODULE SetMemberViolation ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safety == x \in {0, 1, 2, 3, 4, 5}
====
"#;

    let result = check_spec(src, 10).expect("BMC should succeed");
    match result {
        BmcResult::Violation { depth, trace } => {
            assert_eq!(depth, 6, "violation at depth 6 when x = 6 leaves the set");
            assert_eq!(trace.len(), 7);
        }
        other => panic!("expected Violation, got {other:?}"),
    }
}

/// Test: Range membership violation — x exceeds the range.
///
/// Init: x = 0, Next: x' = x + 1, Safety: x \in 0..5
/// At depth 6, x = 6 is NOT in 0..5.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_e2e_range_membership_violation() {
    let src = r#"
---- MODULE RangeMemberViolation ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safety == x \in 0..5
====
"#;

    let result = check_spec(src, 10).expect("BMC should succeed");
    match result {
        BmcResult::Violation { depth, trace } => {
            assert_eq!(depth, 6, "violation at depth 6 when x = 6 leaves 0..5");
            assert_eq!(trace.len(), 7);
        }
        other => panic!("expected Violation, got {other:?}"),
    }
}

/// Test: Multiple variables with set membership safety.
///
/// x increments, y decrements. Safety: x <= 5 /\ y >= 0.
/// y reaches -1 at depth 4.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_e2e_multi_var_set_membership() {
    let src = r#"
---- MODULE MultiVarSet ----
VARIABLES x, y
Init == x = 0 /\ y = 3
Next == x' = x + 1 /\ y' = y - 1
Safety == x <= 5 /\ y >= 0
====
"#;

    let result = check_spec(src, 10).expect("BMC should succeed");
    match result {
        BmcResult::Violation { depth, trace } => {
            assert_eq!(depth, 4, "y becomes -1 at depth 4");
            assert_eq!(trace.len(), 5);
        }
        other => panic!("expected Violation, got {other:?}"),
    }
}

/// Test: Disjunctive Next with safety violation.
///
/// x starts at 0, can increment by 1 or 2 each step.
/// Safety: x <= 3. Fastest violation: 0 -> 2 -> 4 at depth 2.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_e2e_disjunctive_next_violation() {
    let src = r#"
---- MODULE DisjunctiveNext ----
VARIABLE x
Init == x = 0
Next == x' = x + 1 \/ x' = x + 2
Safety == x <= 3
====
"#;

    let result = check_spec(src, 5).expect("BMC should succeed");
    match result {
        BmcResult::Violation { depth, .. } => {
            // Shortest path: 0 -> 2 -> 4 (depth 2)
            assert!(
                depth <= 4,
                "violation must be reachable within 4 steps; got depth {depth}"
            );
        }
        other => panic!("expected Violation, got {other:?}"),
    }
}

/// Test: Two variables with UNCHANGED — only one variable evolves.
///
/// x increments, y stays at 0 via UNCHANGED.
/// Safety: y = 0 always holds (BoundReached).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bmc_e2e_unchanged_compound_safe() {
    let src = r#"
---- MODULE UnchangedCompoundSafe ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ UNCHANGED y
Safety == y = 0
====
"#;

    let result = check_spec(src, 5).expect("BMC should succeed");
    match result {
        BmcResult::BoundReached { max_depth } => assert_eq!(max_depth, 5),
        other => panic!("expected BoundReached, got {other:?}"),
    }
}
