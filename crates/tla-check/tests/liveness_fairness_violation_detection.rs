// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Liveness WF/SF fairness violation detection tests for #2903.
//!
//! Exercises the liveness checker's ability to detect fairness violations
//! through the full model checker pipeline (parse → check → liveness).
//!
//! Key gaps addressed:
//! - WF violation: action perpetually enabled but never taken in a cycle
//! - SF violation: action infinitely often enabled but taken finitely often
//! - WF insufficiency: WF on Next ≠ WF on sub-actions

use tla_check::Config;
use tla_check::{resolve_spec_from_config, CheckResult};
use tla_core::{lower, parse_to_syntax_tree, FileId};

mod common;

/// Helper: parse, resolve, and check a spec with a PROPERTY config.
fn check_liveness_spec(src: &str, property: &str) -> CheckResult {
    let _guard = common::EnvVarGuard::remove("TLA2_SKIP_LIVENESS");

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.expect("module lowering should succeed");

    let spec_config = Config {
        specification: Some("Spec".to_string()),
        ..Default::default()
    };
    let resolved =
        resolve_spec_from_config(&spec_config, &tree).expect("spec resolution should succeed");

    let config = Config {
        init: Some(resolved.init.clone()),
        next: Some(resolved.next.clone()),
        properties: vec![property.to_string()],
        ..Default::default()
    };

    let mut checker = tla_check::ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    checker.set_store_states(true);
    checker.set_fairness(resolved.fairness);
    checker.set_stuttering_allowed(resolved.stuttering_allowed);
    checker.check()
}

// ============================================================================
// Test 1: WF violation — no fairness, action perpetually enabled but untaken
// ============================================================================

/// Without fairness, an action can be perpetually enabled but never taken.
/// The cycle x=0 →(B) x=0 is allowed even though A (x=0→x=1) is enabled.
/// Property []<>(x=1) fails: the unfair cycle never visits x=1.
///
/// TLC: 2 states, liveness violation for []<>(x=1).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn wf_violation_no_fairness_action_perpetually_enabled() {
    let src = r#"
---- MODULE WFViolation ----
EXTENDS Integers

VARIABLE x

Init == x = 0

A == x = 0 /\ x' = 1
B == x' = x

Next == A \/ B

\* No fairness — unfair cycles allowed
Spec == Init /\ [][Next]_x

Live == []<>(x = 1)

====
"#;
    let result = check_liveness_spec(src, "Live");
    match &result {
        CheckResult::LivenessViolation { .. } => {
            // Correct: without WF, the stutter cycle x=0→x=0 violates []<>(x=1).
        }
        CheckResult::Success(_) => {
            panic!(
                "expected LivenessViolation for []<>(x=1) without fairness, \
                 got Success — liveness checker missed the unfair stutter cycle"
            );
        }
        other => panic!("expected LivenessViolation without fairness, got: {other:?}"),
    }
}

// ============================================================================
// Test 2: WF on Next is insufficient for sub-action properties
// ============================================================================

/// WF_x(Next) only guarantees that SOME state-changing action fires, not which one.
/// With A (x=0→x=1), C (x=0→x=2), and B (x∈{1,2}→x=0), WF_x(Next) is satisfied
/// as long as some action changes x. The cycle x=0→(C)2→(B)0→(C)2→... satisfies
/// WF_x(Next) but never visits x=1. Property []<>(x=1) fails.
///
/// Contrast with `wf_on_subaction_sufficient` where WF_x(A) forces A specifically.
///
/// TLC: 3 states, liveness violation for []<>(x=1).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn wf_on_next_insufficient_for_subaction() {
    let src = r#"
---- MODULE WFNextInsufficient ----
EXTENDS Integers

VARIABLE x

Init == x = 0

A == x = 0 /\ x' = 1
C == x = 0 /\ x' = 2
B == x \in {1, 2} /\ x' = 0

Next == A \/ B \/ C

\* WF on Next as a whole — not on individual actions
Spec == Init /\ [][Next]_x /\ WF_x(Next)

Live == []<>(x = 1)

====
"#;
    let result = check_liveness_spec(src, "Live");
    match &result {
        CheckResult::LivenessViolation { .. } => {
            // Correct: WF_x(Next) allows C+B to cycle (0→2→0→2...) forever,
            // satisfying WF (x changes) but never reaching x=1.
        }
        CheckResult::Success(_) => {
            panic!(
                "expected LivenessViolation for []<>(x=1) with WF_x(Next) only, \
                 got Success — WF on Next should not guarantee specific sub-action A fires"
            );
        }
        other => panic!("expected LivenessViolation with WF_x(Next), got: {other:?}"),
    }
}

/// WF_x(A) on a continuously-enabled sub-action forces A to fire.
/// A (x'=1) is enabled at every reachable state where x != 1 (i.e., x=0 and x=2).
/// The problematic cycle x=0->(C)2->(B)0 has A continuously enabled
/// (ENABLED<<A>>_x holds at both x=0 and x=2). WF_x(A) excludes this cycle.
/// Property []<>(x=1) passes because any fair behavior must eventually take A.
///
/// TLC: 3 states, no error.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn wf_on_subaction_sufficient() {
    let src = r#"
---- MODULE WFSubactionSufficient ----
EXTENDS Integers

VARIABLE x

Init == x = 0

A == x' = 1
C == x \in {0, 1} /\ x' = 2
B == x = 2 /\ x' = 0

Next == A \/ B \/ C

\* WF on sub-action A — A is always enabled (x'=1 changes x unless x=1),
\* so WF forces A to fire in any cycle where x != 1
Spec == Init /\ [][Next]_x /\ WF_x(A)

Live == []<>(x = 1)

====
"#;
    let result = check_liveness_spec(src, "Live");
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 3, "expected 3 states (x=0, x=1, x=2)");
        }
        other => panic!("expected Success for []<>(x=1) with WF_x(A), got: {other:?}"),
    }
}

// ============================================================================
// Test 3: SF violation — WF insufficient, action intermittently enabled
// ============================================================================

/// Classic SF scenario: Flip toggles `t` between TRUE/FALSE. Act requires t=TRUE.
/// WF_vars(Act) is trivially satisfied because Act is never *continuously* enabled —
/// Flip keeps disabling it. But Act is *infinitely often* enabled. Without SF, the
/// scheduler can always choose Flip at t=TRUE, preventing Act from ever firing.
/// Property []<>(x=1) fails: x stays 0 forever.
///
/// TLC: 4 states, liveness violation.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn sf_violation_wf_insufficient_intermittent_enable() {
    let src = r#"
---- MODULE SFViolation ----
EXTENDS Integers

VARIABLES x, t

Vars == <<x, t>>

Init == x = 0 /\ t = FALSE

Flip == t' = ~t /\ x' = x
Act == t /\ x' = 1 /\ t' = t

Next == Flip \/ Act

\* WF on Act — but Act is only intermittently enabled, so WF is trivially satisfied
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next) /\ WF_Vars(Act)

Live == []<>(x = 1)

====
"#;
    let result = check_liveness_spec(src, "Live");
    match &result {
        CheckResult::LivenessViolation { .. } => {
            // Correct: WF_Vars(Act) is trivially satisfied (Act never continuously
            // enabled), so the unfair cycle t=F→T→F→T... with x=0 is allowed.
        }
        CheckResult::Success(_) => {
            panic!(
                "expected LivenessViolation for []<>(x=1) with only WF on intermittently-enabled Act, \
                 got Success — WF should be insufficient for intermittently-enabled actions"
            );
        }
        other => panic!("expected LivenessViolation with WF-only (SF needed), got: {other:?}"),
    }
}

/// Same spec as above, but with SF_Vars(Act) instead of WF_Vars(Act).
/// SF guarantees: if Act is *infinitely often* enabled, it must fire.
/// Since Flip keeps toggling t to TRUE (enabling Act), SF forces Act to fire.
/// Property []<>(x=1) passes.
///
/// TLC: 4 states, no error.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn sf_sufficient_intermittent_enable() {
    let src = r#"
---- MODULE SFSufficient ----
EXTENDS Integers

VARIABLES x, t

Vars == <<x, t>>

Init == x = 0 /\ t = FALSE

Flip == t' = ~t /\ x' = x
Act == t /\ x' = 1 /\ t' = t

Next == Flip \/ Act

\* SF on Act — Act is infinitely often enabled, so SF forces it to fire
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next) /\ SF_Vars(Act)

Live == []<>(x = 1)

====
"#;
    let result = check_liveness_spec(src, "Live");
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(stats.states_found, 4, "expected 4 states");
        }
        other => panic!("expected Success for []<>(x=1) with SF_Vars(Act), got: {other:?}"),
    }
}

// ============================================================================
// Test 4: WF violation with cycle detection — multi-action spec
// ============================================================================

/// Three processes: Produce (x→x+1), Consume (x→x-1 when x>0), Reset (x→0).
/// WF on Next only. Property: []<>(x=0). Without WF on specific actions,
/// Produce can fire forever, growing x. But wait — x is bounded by the state
/// space. With x bounded at 2: Produce is enabled at x=0,1. Consume at x=1,2.
/// Reset at any state. The cycle x=0→1→2→1→2→... never visits x=0 if Reset
/// never fires. WF_x(Next) allows this because Next fires every step.
///
/// TLC: 3 states, liveness violation for []<>(x=0).
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn wf_violation_multi_action_cycle() {
    let src = r#"
---- MODULE WFMultiAction ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Produce == x < 2 /\ x' = x + 1
Consume == x > 0 /\ x' = x - 1
Reset == x' = 0

Next == Produce \/ Consume \/ Reset

\* WF on Next only — doesn't guarantee Reset fires
Spec == Init /\ [][Next]_x /\ WF_x(Next)

Live == []<>(x = 0)

====
"#;
    let result = check_liveness_spec(src, "Live");
    match &result {
        CheckResult::LivenessViolation { .. } => {
            // Correct: WF_x(Next) allows Produce/Consume to cycle at x=1,2
            // without ever firing Reset, violating []<>(x=0).
        }
        CheckResult::Success(_) => {
            panic!(
                "expected LivenessViolation for []<>(x=0) with WF_x(Next) only, \
                 got Success — WF on Next should not guarantee Reset fires"
            );
        }
        other => panic!("expected LivenessViolation for multi-action WF test, got: {other:?}"),
    }
}
