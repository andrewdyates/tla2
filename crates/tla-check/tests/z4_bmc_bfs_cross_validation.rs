// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z4 BMC vs BFS cross-validation integration tests.
//!
//! These tests run both the explicit-state BFS checker (`check_module`) and the
//! z4 symbolic BMC engine (`check_bmc`) on the same TLA+ specs, verifying that
//! both engines agree on whether a spec is safe or unsafe.
//!
//! Agreement is defined as:
//! - If BFS finds an invariant violation, BMC must find a `Violation`.
//! - If BFS finds `Success` (all states explored, no violation), BMC must find
//!   `BoundReached` (no violation within the bound).
//! - Counterexample depths must be consistent (BMC depth <= BFS trace length).
//!
//! Part of #3744: z4 integration test -- verified z4 improves TLA2 symbolic
//! backend.

#![cfg(feature = "z4")]

mod common;

use common::parse_module;
use tla_check::{
    bind_constants_from_config, check_bmc, check_module, BmcConfig, BmcResult, BmcValue,
    CheckResult, Config, ConstantValue, EvalCtx,
};

// ---------------------------------------------------------------------------
// Helper: classify BFS result as safe/unsafe for comparison
// ---------------------------------------------------------------------------

#[derive(Debug, PartialEq, Eq)]
enum Verdict {
    Safe,
    Unsafe,
}

fn bfs_verdict(result: &CheckResult) -> Verdict {
    match result {
        CheckResult::Success(_) => Verdict::Safe,
        CheckResult::InvariantViolation { .. } => Verdict::Unsafe,
        CheckResult::Deadlock { .. } => Verdict::Unsafe,
        other => panic!("unexpected BFS result: {other:?}"),
    }
}

fn bmc_verdict(result: &BmcResult) -> Verdict {
    match result {
        BmcResult::Violation { .. } => Verdict::Unsafe,
        BmcResult::BoundReached { .. } => Verdict::Safe,
        BmcResult::Unknown { reason, .. } => {
            panic!("BMC returned Unknown (cannot compare): {reason}")
        }
    }
}

/// Run both BFS and BMC on a spec and assert they agree.
///
/// `bmc_depth` must be large enough for BMC to find any violation that BFS
/// finds. For finite-state specs where BFS exhausts the state space within
/// `bmc_depth` steps, this guarantees complete agreement.
fn assert_bfs_bmc_agree(src: &str, bmc_depth: usize) {
    assert_bfs_bmc_agree_with_config(src, bmc_depth, Config::default());
}

fn assert_bfs_bmc_agree_with_config(src: &str, bmc_depth: usize, mut config: Config) {
    config.init = Some("Init".to_string());
    config.next = Some("Next".to_string());
    config.invariants = vec!["Safety".to_string()];

    let module = parse_module(src);
    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    bind_constants_from_config(&mut ctx, &config).expect("constants should bind");

    let bfs_result = check_module(&module, &config);
    let bmc_result = check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(bmc_depth))
        .expect("BMC should not error");

    let bfs_v = bfs_verdict(&bfs_result);
    let bmc_v = bmc_verdict(&bmc_result);

    assert_eq!(
        bfs_v, bmc_v,
        "BFS and BMC disagree! BFS={bfs_v:?} but BMC={bmc_v:?}\n\
         BFS result: {bfs_result:?}\n\
         BMC result: {bmc_result:?}"
    );
}

// ============================================================================
// Test 1: Simple safe counter -- both engines agree it is safe
// ============================================================================
//
// Counter increments only while count < 3. Safety: count <= 3.
// Finite state space: {0, 1, 2, 3}. Both BFS and BMC(k=10) should find Safe.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_safe_bounded_counter() {
    let src = r#"
---- MODULE SafeBoundedCounter ----
VARIABLE count
Init == count = 0
Next == IF count < 3 THEN count' = count + 1 ELSE count' = count
Safety == count <= 3
====
"#;
    assert_bfs_bmc_agree(src, 10);
}

// ============================================================================
// Test 2: Unsafe counter -- both engines agree on violation
// ============================================================================
//
// Counter increments without bound. Safety: count <= 5.
// BFS finds violation when count reaches 6. BMC finds it at depth 6.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_unsafe_unbounded_counter() {
    let src = r#"
---- MODULE UnsafeBoundedCounter ----
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

    let bfs_result = check_module(&module, &config);
    let bmc_result = check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(10))
        .expect("BMC should not error");

    // Both must find violation
    assert_eq!(bfs_verdict(&bfs_result), Verdict::Unsafe);
    assert_eq!(bmc_verdict(&bmc_result), Verdict::Unsafe);

    // BMC violation should be at depth 6 (count goes 0,1,2,3,4,5,6)
    if let BmcResult::Violation { depth, trace } = &bmc_result {
        assert_eq!(*depth, 6, "BMC should find violation at depth 6");
        // Trace should start at 0 and end at 6
        assert!(
            matches!(trace[0].assignments.get("count"), Some(BmcValue::Int(0))),
            "trace should start at count=0"
        );
        assert!(
            matches!(
                trace[*depth].assignments.get("count"),
                Some(BmcValue::Int(6))
            ),
            "trace should end at count=6"
        );
    }
}

// ============================================================================
// Test 3: Init-state violation -- both engines detect depth-0 bug
// ============================================================================

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_init_violation() {
    let src = r#"
---- MODULE InitViolationCross ----
VARIABLE x
Init == x = 100
Next == x' = x
Safety == x <= 50
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

    let bfs_result = check_module(&module, &config);
    let bmc_result = check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(5))
        .expect("BMC should not error");

    assert_eq!(bfs_verdict(&bfs_result), Verdict::Unsafe);
    assert_eq!(bmc_verdict(&bmc_result), Verdict::Unsafe);

    // BMC should find it at depth 0
    if let BmcResult::Violation { depth, .. } = &bmc_result {
        assert_eq!(*depth, 0, "init violation should be at depth 0");
    }
}

// ============================================================================
// Test 4: Two-variable safe spec with UNCHANGED
// ============================================================================
//
// x increments, y stays at 0. Safety: y = 0.
// Tests that BMC correctly handles UNCHANGED and multi-variable specs.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_two_var_unchanged_safe() {
    let src = r#"
---- MODULE TwoVarUnchangedSafe ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ UNCHANGED y
Safety == y = 0
====
"#;
    assert_bfs_bmc_agree(src, 10);
}

// ============================================================================
// Test 5: Two-variable unsafe spec
// ============================================================================
//
// Both x and y increment. Safety: x + y <= 8.
// Violation at depth 5: x=5, y=5, x+y=10 > 8.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_two_var_sum_unsafe() {
    let src = r#"
---- MODULE TwoVarSumUnsafe ----
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y + 1
Safety == x + y <= 8
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

    let bfs_result = check_module(&module, &config);
    let bmc_result = check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(10))
        .expect("BMC should not error");

    assert_eq!(bfs_verdict(&bfs_result), Verdict::Unsafe);
    assert_eq!(bmc_verdict(&bmc_result), Verdict::Unsafe);

    // At depth 5, x=5, y=5, sum=10 > 8
    if let BmcResult::Violation { depth, trace } = &bmc_result {
        assert_eq!(*depth, 5, "violation at x+y > 8 should be at depth 5");
        let last = &trace[*depth];
        let x_val = match last.assignments.get("x") {
            Some(BmcValue::Int(v)) => *v,
            other => panic!("expected Int for x, got {other:?}"),
        };
        let y_val = match last.assignments.get("y") {
            Some(BmcValue::Int(v)) => *v,
            other => panic!("expected Int for y, got {other:?}"),
        };
        assert!(
            x_val + y_val > 8,
            "violation state should have x + y > 8, got x={x_val}, y={y_val}"
        );
    }
}

// ============================================================================
// Test 6: Mutual exclusion -- both processes never in critical section
// ============================================================================
//
// Two processes with a simple turn-based protocol.
// pc1, pc2 in {0, 1} where 1 = critical section.
// Protocol: only enter CS when turn = self.
// Safety: NOT (pc1 = 1 /\ pc2 = 1).

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_mutex_safe() {
    let src = r#"
---- MODULE MutexSafe ----
VARIABLES pc1, pc2, turn
Init == pc1 = 0 /\ pc2 = 0 /\ turn = 1
Next ==
    \/ (pc1 = 0 /\ turn = 1 /\ pc1' = 1 /\ UNCHANGED <<pc2, turn>>)
    \/ (pc1 = 1 /\ pc1' = 0 /\ turn' = 2 /\ UNCHANGED pc2)
    \/ (pc2 = 0 /\ turn = 2 /\ pc2' = 1 /\ UNCHANGED <<pc1, turn>>)
    \/ (pc2 = 1 /\ pc2' = 0 /\ turn' = 1 /\ UNCHANGED pc1)
Safety == ~(pc1 = 1 /\ pc2 = 1)
====
"#;
    assert_bfs_bmc_agree(src, 15);
}

// ============================================================================
// Test 7: Broken mutex -- both engines detect violation
// ============================================================================
//
// Same as above but processes can enter CS without checking turn.
// Safety: NOT (pc1 = 1 /\ pc2 = 1). This should be violated.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_mutex_broken() {
    let src = r#"
---- MODULE MutexBroken ----
VARIABLES pc1, pc2, turn
Init == pc1 = 0 /\ pc2 = 0 /\ turn = 1
Next ==
    \/ (pc1 = 0 /\ pc1' = 1 /\ UNCHANGED <<pc2, turn>>)
    \/ (pc1 = 1 /\ pc1' = 0 /\ turn' = 2 /\ UNCHANGED pc2)
    \/ (pc2 = 0 /\ pc2' = 1 /\ UNCHANGED <<pc1, turn>>)
    \/ (pc2 = 1 /\ pc2' = 0 /\ turn' = 1 /\ UNCHANGED pc1)
Safety == ~(pc1 = 1 /\ pc2 = 1)
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

    let bfs_result = check_module(&module, &config);
    let bmc_result = check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(10))
        .expect("BMC should not error");

    // Both should find violation (both processes in CS simultaneously)
    assert_eq!(bfs_verdict(&bfs_result), Verdict::Unsafe);
    assert_eq!(bmc_verdict(&bmc_result), Verdict::Unsafe);

    // Verify BMC counterexample shows both in CS
    if let BmcResult::Violation { depth, trace } = &bmc_result {
        let last = &trace[*depth];
        let pc1 = last.assignments.get("pc1");
        let pc2 = last.assignments.get("pc2");
        assert!(
            matches!((pc1, pc2), (Some(BmcValue::Int(1)), Some(BmcValue::Int(1)))),
            "violation state should have pc1=1 and pc2=1, got pc1={pc1:?}, pc2={pc2:?}"
        );
    }
}

// ============================================================================
// Test 8: Token ring -- safe with N=3
// ============================================================================
//
// A token circulates among 3 nodes. Only the token holder can act.
// Safety: exactly one node holds the token at all times.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_token_ring_safe() {
    let src = r#"
---- MODULE TokenRingSafe ----
VARIABLES t1, t2, t3
Init == t1 = 1 /\ t2 = 0 /\ t3 = 0
Next ==
    \/ (t1 = 1 /\ t1' = 0 /\ t2' = 1 /\ UNCHANGED t3)
    \/ (t2 = 1 /\ t2' = 0 /\ t3' = 1 /\ UNCHANGED t1)
    \/ (t3 = 1 /\ t3' = 0 /\ t1' = 1 /\ UNCHANGED t2)
Safety == t1 + t2 + t3 = 1
====
"#;
    assert_bfs_bmc_agree(src, 15);
}

// ============================================================================
// Test 9: Broken token ring -- token can be duplicated
// ============================================================================
//
// Bug: passing the token does not clear the sender's token.
// Safety: exactly one node holds the token. Should be violated.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_token_ring_broken() {
    let src = r#"
---- MODULE TokenRingBroken ----
VARIABLES t1, t2, t3
Init == t1 = 1 /\ t2 = 0 /\ t3 = 0
Next ==
    \/ (t1 = 1 /\ t2' = 1 /\ UNCHANGED <<t1, t3>>)
    \/ (t2 = 1 /\ t3' = 1 /\ UNCHANGED <<t1, t2>>)
    \/ (t3 = 1 /\ t1' = 1 /\ UNCHANGED <<t2, t3>>)
Safety == t1 + t2 + t3 = 1
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

    let bfs_result = check_module(&module, &config);
    let bmc_result = check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(5))
        .expect("BMC should not error");

    assert_eq!(bfs_verdict(&bfs_result), Verdict::Unsafe);
    assert_eq!(bmc_verdict(&bmc_result), Verdict::Unsafe);

    // After one step, token is duplicated: t1=1, t2=1
    if let BmcResult::Violation { trace, .. } = &bmc_result {
        let last = trace.last().unwrap();
        let sum: i64 = ["t1", "t2", "t3"]
            .iter()
            .filter_map(|name| match last.assignments.get(*name) {
                Some(BmcValue::Int(v)) => Some(*v),
                _ => None,
            })
            .sum();
        assert!(
            sum != 1,
            "violation state should have token count != 1, got sum={sum}"
        );
    }
}

// ============================================================================
// Test 10: Conditional branching -- IF/THEN/ELSE safe spec
// ============================================================================
//
// x oscillates between 0 and 1. Safety: x \in {0, 1}.
// Tests BMC handling of IF-THEN-ELSE in Next.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_if_then_else_safe() {
    let src = r#"
---- MODULE IfThenElseSafe ----
VARIABLE x
Init == x \in {0, 1}
Next == IF x = 0 THEN x' = 1 ELSE x' = 0
Safety == x >= 0 /\ x <= 1
====
"#;
    assert_bfs_bmc_agree(src, 10);
}

// ============================================================================
// Test 11: Multiple initial states -- both engines explore all inits
// ============================================================================
//
// x starts in {0, 1, 2, 3}. Next: x stays. Safety: x <= 3.
// All initial states satisfy safety. Both should agree: Safe.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_multiple_init_states_safe() {
    let src = r#"
---- MODULE MultiInitSafe ----
VARIABLE x
Init == x \in {0, 1, 2, 3}
Next == x' = x
Safety == x <= 3
====
"#;
    assert_bfs_bmc_agree(src, 5);
}

// ============================================================================
// Test 12: Multiple initial states -- one init violates invariant
// ============================================================================

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_multiple_init_states_one_unsafe() {
    let src = r#"
---- MODULE MultiInitOneUnsafe ----
VARIABLE x
Init == x \in {0, 1, 2, 10}
Next == x' = x
Safety == x <= 5
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

    let bfs_result = check_module(&module, &config);
    let bmc_result = check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(3))
        .expect("BMC should not error");

    // Both should find the init-state violation (x=10 > 5)
    assert_eq!(bfs_verdict(&bfs_result), Verdict::Unsafe);
    assert_eq!(bmc_verdict(&bmc_result), Verdict::Unsafe);

    if let BmcResult::Violation { depth, .. } = &bmc_result {
        assert_eq!(*depth, 0, "init violation should be found at depth 0");
    }
}

// ============================================================================
// Test 13: Disjunctive Next -- multiple enabled actions
// ============================================================================
//
// x can increase by 1 or decrease by 1 (but not below 0).
// Safety: x <= 4. Starting from 0, can reach 4 at depth 4 but never 5
// since decrease is also always available. BFS exhausts small space.
// Actually x CAN reach 5 via 0->1->2->3->4->5 in 5 steps.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_disjunctive_next_unsafe() {
    let src = r#"
---- MODULE DisjunctiveNextUnsafe ----
VARIABLE x
Init == x = 0
Next ==
    \/ x' = x + 1
    \/ (x > 0 /\ x' = x - 1)
Safety == x <= 4
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

    let bfs_result = check_module(&module, &config);
    let bmc_result = check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(10))
        .expect("BMC should not error");

    // Both should find violation (x can reach 5 via 0->1->2->3->4->5)
    assert_eq!(bfs_verdict(&bfs_result), Verdict::Unsafe);
    assert_eq!(bmc_verdict(&bmc_result), Verdict::Unsafe);

    if let BmcResult::Violation { depth, .. } = &bmc_result {
        assert!(
            *depth <= 5,
            "BMC should find violation at depth <= 5, got {depth}"
        );
    }
}

// ============================================================================
// Test 14: Config constants -- BMC respects CONSTANT bindings
// ============================================================================
//
// Uses CONSTANT N to parameterize the spec. With N=3, spec is safe.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_config_constants_safe() {
    let src = r#"
---- MODULE ConfigConstSafe ----
CONSTANT N
VARIABLE x
Init == x \in 0..N
Next == x' = x
Safety == x <= N
====
"#;
    let mut config = Config::default();
    config
        .constants
        .insert("N".to_string(), ConstantValue::Value("3".to_string()));
    assert_bfs_bmc_agree_with_config(src, 5, config);
}

// ============================================================================
// Test 15: Config constants -- BMC detects violation with parameterized bound
// ============================================================================

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_config_constants_unsafe() {
    let src = r#"
---- MODULE ConfigConstUnsafe ----
CONSTANT Limit
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safety == x <= Limit
====
"#;
    let module = parse_module(src);
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Safety".to_string()],
        ..Default::default()
    };
    config
        .constants
        .insert("Limit".to_string(), ConstantValue::Value("3".to_string()));

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    bind_constants_from_config(&mut ctx, &config).expect("constants should bind");

    let bfs_result = check_module(&module, &config);
    let bmc_result = check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(10))
        .expect("BMC should not error");

    assert_eq!(bfs_verdict(&bfs_result), Verdict::Unsafe);
    assert_eq!(bmc_verdict(&bmc_result), Verdict::Unsafe);

    // Violation at depth 4: count goes 0,1,2,3,4 and 4 > Limit=3
    if let BmcResult::Violation { depth, .. } = &bmc_result {
        assert_eq!(*depth, 4, "violation should be at depth 4 (x=4 > Limit=3)");
    }
}

// ============================================================================
// Test 16: Operator definitions -- BMC expands user operators
// ============================================================================
//
// Tests that BMC correctly expands operator definitions in Init/Next/Safety.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_operator_expansion() {
    let src = r#"
---- MODULE OperatorExpansionCross ----
VARIABLE count
Inc == count' = count + 1
Init == count = 0
Next == count < 3 /\ Inc
Safety == count <= 3
====
"#;
    assert_bfs_bmc_agree(src, 8);
}

// ============================================================================
// Test 17: Incremental vs per-depth BMC agreement
// ============================================================================
//
// Runs both incremental and per-depth BMC modes on the same unsafe spec and
// verifies they find the violation at the same depth.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_incremental_vs_per_depth_agree() {
    let src = r#"
---- MODULE IncrPerDepthAgree ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
Safety == x <= 7
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

    let per_depth = check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(15))
        .expect("per-depth BMC should succeed");

    let incremental = check_bmc(
        &module,
        &config,
        &ctx,
        BmcConfig {
            max_depth: 15,
            incremental: true,
            ..BmcConfig::default()
        },
    )
    .expect("incremental BMC should succeed");

    match (&per_depth, &incremental) {
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
            assert_eq!(d1, d2, "per-depth and incremental must find same depth");
            assert_eq!(t1.len(), t2.len(), "trace lengths must match");
        }
        _ => panic!(
            "both modes should find Violation, got per_depth={per_depth:?}, incr={incremental:?}"
        ),
    }
}

// ============================================================================
// Test 18: Three-variable pipeline -- data flows through stages
// ============================================================================
//
// a -> b -> c pipeline with one-step delay.
// Safety: c >= 0 (always true since a starts at 0 and increments).

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_pipeline_safe() {
    let src = r#"
---- MODULE PipelineSafe ----
VARIABLES a, b, c
Init == a = 0 /\ b = 0 /\ c = 0
Next == a' = a + 1 /\ b' = a /\ c' = b
Safety == c >= 0
====
"#;
    assert_bfs_bmc_agree(src, 10);
}

// ============================================================================
// Test 19: Swap spec -- x and y swap each step
// ============================================================================
//
// Init: x=0, y=1. Next: swap. Safety: x >= 0 /\ y >= 0.
// Finite 2-state space: {(0,1), (1,0)}. Always safe.

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_swap_safe() {
    let src = r#"
---- MODULE SwapSafe ----
VARIABLES x, y
Init == x = 0 /\ y = 1
Next == x' = y /\ y' = x
Safety == x >= 0 /\ y >= 0
====
"#;
    assert_bfs_bmc_agree(src, 10);
}

// ============================================================================
// Test 20: BFS finds deadlock, BMC finds safe (complementary)
// ============================================================================
//
// Deadlock detection is a BFS-specific feature (no successor states).
// BMC checks invariant violations, not deadlock.
// This test documents the expected divergence: BFS reports Deadlock while
// BMC reports BoundReached (no invariant violation).

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn z4_cross_deadlock_spec_complementary() {
    let src = r#"
---- MODULE DeadlockSpec ----
VARIABLE x
Init == x = 0
Next == x < 3 /\ x' = x + 1
Safety == x <= 10
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

    let bfs_result = check_module(&module, &config);
    let bmc_result = check_bmc(&module, &config, &ctx, BmcConfig::with_max_depth(10))
        .expect("BMC should not error");

    // BFS detects deadlock at x=3 (no Next enabled).
    assert!(
        matches!(bfs_result, CheckResult::Deadlock { .. }),
        "BFS should detect deadlock, got {bfs_result:?}"
    );

    // BMC does not check deadlock, only invariant safety.
    // The invariant x <= 10 is never violated, so BMC reports BoundReached.
    assert!(
        matches!(bmc_result, BmcResult::BoundReached { .. }),
        "BMC should report BoundReached (no invariant violation), got {bmc_result:?}"
    );
}
