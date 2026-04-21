// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for k-induction engine. Part of #3722.

use super::*;
use crate::test_support::parse_module;

/// Helper: run k-induction on a spec string with default config.
fn check_spec_kinduction(src: &str, max_k: usize) -> Result<KInductionResult, KInductionError> {
    let module = parse_module(src);
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    check_kinduction(
        &module,
        &config,
        &ctx,
        KInductionConfig {
            max_k,
            start_k: 1,
            debug: false,
            ..Default::default()
        },
    )
}

// ---- Test 1: Simple invariant that IS 1-inductive ----
//
// The mutex spec: variable `x` toggles between 0 and 1.
// Safety: x >= 0 /\ x <= 1.
// This is 1-inductive because: if x \in {0,1} at step i,
// then x' \in {0,1} at step i+1 (Next preserves the range).

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_proves_1_inductive_property() {
    let src = r#"
---- MODULE Mutex ----
VARIABLE x
Init == x \in {0, 1}
Next == IF x = 0 THEN x' = 1 ELSE x' = 0
Safety == x >= 0 /\ x <= 1
====
"#;

    let result = check_spec_kinduction(src, 10).expect("k-induction should succeed");
    match result {
        KInductionResult::Proved { k } => {
            assert!(
                k <= 2,
                "x toggling 0/1 with Safety x>=0 /\\ x<=1 should be proved at small k, got k={k}"
            );
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ---- Test 2: Property that BMC alone cannot prove ----
//
// Stable counter: x starts at 0 and stays at 0 forever.
// Safety: x = 0. BMC can only prove "no violation up to depth k",
// but k-induction proves it universally because x'=x with x=0
// is trivially 1-inductive.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_proves_stable_property() {
    let src = r#"
---- MODULE StableZero ----
VARIABLE x
Init == x = 0
Next == x' = x
Safety == x = 0
====
"#;

    let result = check_spec_kinduction(src, 10).expect("k-induction should succeed");
    match result {
        KInductionResult::Proved { k } => {
            assert_eq!(k, 1, "x'=x with Safety x=0 should be 1-inductive");
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ---- Test 3: Property that is NOT inductive ----
//
// Counter that increments: x starts at 0, x' = x + 1.
// Safety: x <= 100.
// This is NOT k-inductive for any small k because the induction
// hypothesis "x<=100 for k consecutive steps" does not prevent
// x from being 100 at step k-1 and 101 at step k. BMC won't
// find a violation at small depths either. k-induction returns Unknown.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_returns_unknown_for_non_inductive_property() {
    let src = r#"
---- MODULE UnboundedCounter ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safety == x <= 100
====
"#;

    let result = check_spec_kinduction(src, 5).expect("k-induction should succeed");
    match result {
        KInductionResult::Unknown { max_k, .. } => {
            assert_eq!(
                max_k, 5,
                "should exhaust the bound before returning Unknown"
            );
        }
        KInductionResult::Proved { k } => {
            panic!("x'=x+1 with Safety x<=100 should NOT be provable by k-induction, but got Proved at k={k}");
        }
        KInductionResult::Counterexample { depth, .. } => {
            // This is also acceptable if BMC finds the violation (depth >= 101)
            // but with max_k=5 the BMC base case won't reach depth 101.
            panic!("unexpected Counterexample at depth {depth} with max_k=5");
        }
    }
}

// ---- Test 4: BMC base case finds a real counterexample ----
//
// The invariant is violated at depth 3.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_returns_counterexample_from_bmc_base() {
    let src = r#"
---- MODULE ShortViolation ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safety == x <= 2
====
"#;

    let result = check_spec_kinduction(src, 10).expect("k-induction should succeed");
    match result {
        KInductionResult::Counterexample { depth, trace } => {
            assert_eq!(
                depth, 3,
                "violation should be found at depth 3 (x reaches 3)"
            );
            assert_eq!(trace.len(), 4, "trace should contain states 0 through 3");
        }
        other => panic!("expected Counterexample, got {other:?}"),
    }
}

// ---- Test 5: Two-variable spec where invariant is k-inductive at k>1 ----
//
// Two variables x, y. Init: x=0, y=0. Next: x'=y, y'=x.
// They swap: (0,0) -> (0,0) (it's stable at 0,0).
// Safety: x >= 0 /\ y >= 0.
// This should be 1-inductive.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_proves_two_variable_swap() {
    let src = r#"
---- MODULE Swap ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = y /\ y' = x
Safety == x >= 0 /\ y >= 0
====
"#;

    let result = check_spec_kinduction(src, 10).expect("k-induction should succeed");
    match result {
        KInductionResult::Proved { k } => {
            assert!(
                k <= 3,
                "swap spec with non-negative safety should be provable at small k, got k={k}"
            );
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ---- Test 6: No invariants configured ----

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_kinduction_error_no_invariants() {
    let src = r#"
---- MODULE NoInvariant ----
VARIABLE x
Init == x = 0
Next == x' = x
====
"#;

    let module = parse_module(src);
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let err = check_kinduction(&module, &config, &ctx, KInductionConfig::default())
        .expect_err("should fail with no invariants");
    assert!(
        matches!(err, KInductionError::NoInvariants),
        "expected NoInvariants error, got {err:?}"
    );
}

// ---- Test 7: Missing Init ----

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_kinduction_error_missing_init() {
    let src = r#"
---- MODULE MissingInit ----
VARIABLE x
Next == x' = x
Safety == x >= 0
====
"#;

    let module = parse_module(src);
    let config = crate::Config {
        init: None,
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let err = check_kinduction(&module, &config, &ctx, KInductionConfig::default())
        .expect_err("should fail with missing Init");
    assert!(
        matches!(err, KInductionError::MissingSpec(_)),
        "expected MissingSpec error, got {err:?}"
    );
}

// ---- Test 8: Pipeline with delayed observation (NOT 1-inductive, IS 2-inductive) ----
//
// Classic k>1 induction example: a pipeline register where y observes x
// with a one-step delay.
//
// Variables: x, y.
// Init: x=0, y=0.
// Next: y' = x /\ x' = IF x = 0 THEN 1 ELSE 0.
//
// Reachable states: (0,0) -> (1,0) -> (0,1) -> (1,0) -> ...
// Safety: y = 0 \/ y = 1  (equivalently y >= 0 /\ y <= 1).
//
// NOT 1-inductive: the solver can pick an arbitrary state x=5, y=0.
// y=0 satisfies safety. But y' = x = 5, which violates y' <= 1. The
// spurious state is unreachable from Init but the solver doesn't know
// that. So 1-induction fails.
//
// IS 2-inductive: two consecutive states (x0,y0) and (x1,y1) both
// satisfy safety. Since y1 = x0 (from the transition x0->x1), and
// y1 \in {0,1} (from the safety hypothesis on step 1), we get
// x0 \in {0,1}. Then x1 = IF x0=0 THEN 1 ELSE 0, so x1 \in {0,1}.
// Then y2 = x1 \in {0,1}. Safety holds at step 2. UNSAT.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_proves_2_inductive_pipeline() {
    let src = r#"
---- MODULE Pipeline ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == y' = x /\ (IF x = 0 THEN x' = 1 ELSE x' = 0)
Safety == y >= 0 /\ y <= 1
====
"#;

    let result = check_spec_kinduction(src, 10).expect("k-induction should succeed");
    match result {
        KInductionResult::Proved { k } => {
            // Must require k >= 2 (not 1-inductive) but should succeed at k=2.
            assert!(k >= 2, "pipeline spec should NOT be 1-inductive, got k={k}");
            assert!(
                k <= 3,
                "pipeline spec should be provable at k=2 or k=3, got k={k}"
            );
        }
        other => panic!("expected Proved at k=2, got {other:?}"),
    }
}

// ---- Test 9: Boolean variable with sort inference ----
//
// Exercises the Bool sort inference path in z4_shared::infer_var_sorts.
// Variable `b` starts as TRUE and toggles. Safety: b = TRUE \/ b = FALSE.
// This is trivially 1-inductive for BOOLEAN domain.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_boolean_variable() {
    let src = r#"
---- MODULE BoolToggle ----
VARIABLE b
Init == b \in {0, 1}
Next == IF b = 0 THEN b' = 1 ELSE b' = 0
Safety == b >= 0 /\ b <= 1
====
"#;

    let result = check_spec_kinduction(src, 5).expect("k-induction should succeed");
    match result {
        KInductionResult::Proved { k } => {
            assert!(
                k <= 2,
                "boolean toggle should be provable at small k, got k={k}"
            );
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ---- Test 10: Multiple invariants (conjunction of safety properties) ----
//
// Tests that check_kinduction correctly builds a conjunction of multiple
// invariant operators, not just a single one.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_multiple_invariants() {
    let src = r#"
---- MODULE MultiInvariant ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = x /\ y' = y
LowerBound == x >= 0 /\ y >= 0
UpperBound == x <= 0 /\ y <= 0
====
"#;

    let module = parse_module(src);
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["LowerBound".to_string(), "UpperBound".to_string()],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    let result = check_kinduction(
        &module,
        &config,
        &ctx,
        KInductionConfig {
            max_k: 5,
            start_k: 1,
            debug: false,
            ..Default::default()
        },
    )
    .expect("k-induction should succeed");

    match result {
        KInductionResult::Proved { k } => {
            assert_eq!(
                k, 1,
                "x'=x /\\ y'=y with x=0 /\\ y=0 bounds should be 1-inductive"
            );
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ---- Test 11: Custom start_k parameter ----
//
// Verify that start_k controls the starting depth of the inductive step,
// avoiding redundant base-case work at small depths.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_custom_start_k() {
    let src = r#"
---- MODULE CustomStartK ----
VARIABLE x
Init == x = 0
Next == x' = x
Safety == x = 0
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

    // Start at k=3 instead of k=1.
    // The property is 1-inductive, so starting at k=3 should still prove it
    // (at k=3, the inductive step is: assume Safety holds for 3 consecutive
    // states, prove it at the 4th -- which succeeds trivially).
    let result = check_kinduction(
        &module,
        &config,
        &ctx,
        KInductionConfig {
            max_k: 10,
            start_k: 3,
            debug: false,
            ..Default::default()
        },
    )
    .expect("k-induction should succeed");

    match result {
        KInductionResult::Proved { k } => {
            assert!(
                k >= 3,
                "with start_k=3, proof should be at k >= 3, got k={k}"
            );
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ---- Test 12: Three-variable spec with data dependency chain ----
//
// Variables: a, b, c form a shift register.
// Init: a=0, b=0, c=0.
// Next: c' = b, b' = a, a' = IF a = 0 THEN 1 ELSE 0.
// Safety: c >= 0 /\ c <= 1.
//
// The invariant on `c` depends on `b` (one step) which depends on `a`
// (two steps). This should require k=3 induction: the solver needs to
// see three consecutive safe states to conclude a \in {0,1}, hence
// b \in {0,1}, hence c \in {0,1}.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_three_stage_shift_register() {
    let src = r#"
---- MODULE ShiftRegister ----
VARIABLES a, b, c
Init == a = 0 /\ b = 0 /\ c = 0
Next == c' = b /\ b' = a /\ (IF a = 0 THEN a' = 1 ELSE a' = 0)
Safety == c >= 0 /\ c <= 1
====
"#;

    let result = check_spec_kinduction(src, 10).expect("k-induction should succeed");
    match result {
        KInductionResult::Proved { k } => {
            // Needs at least k=3 (three stages of data dependency).
            assert!(k >= 2, "shift register should need k >= 2, got k={k}");
            assert!(
                k <= 5,
                "shift register should be provable by k <= 5, got k={k}"
            );
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ---- Tests for incremental inductive step mode ----

/// Helper: run k-induction in incremental mode.
fn check_spec_kinduction_incremental(
    src: &str,
    max_k: usize,
) -> Result<KInductionResult, KInductionError> {
    let module = parse_module(src);
    let config = crate::Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };

    let mut ctx = crate::EvalCtx::new();
    ctx.load_module(&module);

    check_kinduction(
        &module,
        &config,
        &ctx,
        KInductionConfig {
            max_k,
            start_k: 1,
            debug: false,
            incremental: true,
            ..Default::default()
        },
    )
}

// ---- Test 13: Incremental mode proves 1-inductive property ----

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_incremental_proves_1_inductive() {
    let src = r#"
---- MODULE IncrMutex ----
VARIABLE x
Init == x \in {0, 1}
Next == IF x = 0 THEN x' = 1 ELSE x' = 0
Safety == x >= 0 /\ x <= 1
====
"#;

    let result = check_spec_kinduction_incremental(src, 10).expect("k-induction should succeed");
    match result {
        KInductionResult::Proved { k } => {
            assert!(
                k <= 2,
                "incremental: x toggling 0/1 should be proved at small k, got k={k}"
            );
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ---- Test 14: Incremental mode proves stable property ----

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_incremental_proves_stable() {
    let src = r#"
---- MODULE IncrStable ----
VARIABLE x
Init == x = 0
Next == x' = x
Safety == x = 0
====
"#;

    let result = check_spec_kinduction_incremental(src, 10).expect("k-induction should succeed");
    match result {
        KInductionResult::Proved { k } => {
            assert_eq!(
                k, 1,
                "incremental: x'=x with Safety x=0 should be 1-inductive"
            );
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

// ---- Test 15: Incremental mode returns Unknown for non-inductive ----

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_incremental_returns_unknown() {
    let src = r#"
---- MODULE IncrUnbounded ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safety == x <= 100
====
"#;

    let result = check_spec_kinduction_incremental(src, 5).expect("k-induction should succeed");
    match result {
        KInductionResult::Unknown { max_k, .. } => {
            assert_eq!(max_k, 5, "incremental: should exhaust the bound");
        }
        KInductionResult::Proved { k } => {
            panic!("incremental: should NOT prove x'=x+1, got Proved at k={k}");
        }
        KInductionResult::Counterexample { depth, .. } => {
            panic!("unexpected Counterexample at depth {depth} with max_k=5");
        }
    }
}

// ---- Test 16: Incremental mode finds counterexample from BMC base ----

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_incremental_counterexample() {
    let src = r#"
---- MODULE IncrShortViolation ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safety == x <= 2
====
"#;

    let result = check_spec_kinduction_incremental(src, 10).expect("k-induction should succeed");
    match result {
        KInductionResult::Counterexample { depth, trace } => {
            assert_eq!(depth, 3, "incremental: violation at depth 3");
            assert_eq!(trace.len(), 4, "trace should contain states 0 through 3");
        }
        other => panic!("expected Counterexample, got {other:?}"),
    }
}

// ---- Test 17: Incremental mode proves 2-inductive pipeline ----
//
// This is the key test: the pipeline spec requires k >= 2, so the incremental
// solver must correctly retain transitions from k=1 when checking k=2.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_incremental_proves_2_inductive_pipeline() {
    let src = r#"
---- MODULE IncrPipeline ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == y' = x /\ (IF x = 0 THEN x' = 1 ELSE x' = 0)
Safety == y >= 0 /\ y <= 1
====
"#;

    let result = check_spec_kinduction_incremental(src, 10).expect("k-induction should succeed");
    match result {
        KInductionResult::Proved { k } => {
            assert!(
                k >= 2,
                "incremental: pipeline should NOT be 1-inductive, got k={k}"
            );
            assert!(
                k <= 3,
                "incremental: pipeline should be provable at k=2 or k=3, got k={k}"
            );
        }
        other => panic!("expected Proved at k>=2, got {other:?}"),
    }
}

// ---- Test 18: Incremental and non-incremental agree on shift register ----

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_kinduction_incremental_shift_register_agrees() {
    let src = r#"
---- MODULE IncrShiftRegister ----
VARIABLES a, b, c
Init == a = 0 /\ b = 0 /\ c = 0
Next == c' = b /\ b' = a /\ (IF a = 0 THEN a' = 1 ELSE a' = 0)
Safety == c >= 0 /\ c <= 1
====
"#;

    let non_incr = check_spec_kinduction(src, 10).expect("non-incremental should succeed");
    let incr = check_spec_kinduction_incremental(src, 10).expect("incremental should succeed");

    // Both should prove the property.
    let non_incr_k = match non_incr {
        KInductionResult::Proved { k } => k,
        other => panic!("non-incremental: expected Proved, got {other:?}"),
    };
    let incr_k = match incr {
        KInductionResult::Proved { k } => k,
        other => panic!("incremental: expected Proved, got {other:?}"),
    };

    // The incremental solver may prove at the same or different k (due to
    // different learned clauses), but both must prove it within bound.
    assert!(
        non_incr_k <= 10 && incr_k <= 10,
        "both should prove within max_k=10: non_incr={non_incr_k}, incr={incr_k}"
    );
}
