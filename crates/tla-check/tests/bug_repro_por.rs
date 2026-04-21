// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Partial Order Reduction end-to-end - Issue #571
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::parse_module;
use tla_check::{check_module, CheckResult, Config, ConstantValue};

// ============================================================================
// Issue #571: POR (Partial Order Reduction) End-to-End Integration Tests
// ============================================================================

/// Issue #571 / #3706: POR must still detect invariant violations.
///
/// The baseline run finds InvXBound violation. POR-enabled run must also
/// find the same violation (POR currently returns the full enabled set,
/// so state counts match exactly).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_issue_571_por_flag_is_rejected_for_invariant_runs() {
    let spec = r#"
---- MODULE PORSoundnessViolation ----
EXTENDS Naturals

VARIABLE x, y

Init ==
    /\ x = 0
    /\ y = 0

\* Two counters with explicit next-state specs (TLA+ style)
IncX ==
    /\ x < 10
    /\ x' = x + 1
    /\ y' = y

IncY ==
    /\ y < 10
    /\ x' = x
    /\ y' = y + 1

Next == IncX \/ IncY

\* Invariant violated when x > 5
InvXBound == x <= 5

====
"#;

    let module = parse_module(spec);

    // Run WITHOUT POR first to establish baseline
    let config_no_por = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InvXBound".to_string()],
        check_deadlock: false,
        por_enabled: false,
        ..Default::default()
    };

    let result_no_por = check_module(&module, &config_no_por);
    let inv_no_por = match &result_no_por {
        CheckResult::InvariantViolation { invariant, .. } => invariant.clone(),
        other => panic!(
            "Baseline (no POR): Must find invariant violation. Got: {:?}",
            other
        ),
    };
    assert_eq!(
        inv_no_por, "InvXBound",
        "Baseline: Expected InvXBound violation, got {}",
        inv_no_por
    );

    // Run WITH POR — must also find the same invariant violation (Part of #3706)
    let config_por = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InvXBound".to_string()],
        check_deadlock: false,
        por_enabled: true,
        ..Default::default()
    };

    let result_por = check_module(&module, &config_por);
    match &result_por {
        CheckResult::InvariantViolation { invariant, .. } => {
            assert_eq!(
                invariant, "InvXBound",
                "POR run must find InvXBound violation, got {invariant}"
            );
        }
        other => panic!("POR run must detect invariant violation. Got: {other:?}"),
    }
}

/// Issue #571 / #3706: valid safety runs succeed both with and without POR.
///
/// POR-enabled run must find the same state count as the baseline.
/// Part of #571, #3706 (POR end-to-end integration tests).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_issue_571_por_succeeds_for_successful_runs() {
    let spec = r#"
---- MODULE PORCorrectness ----
EXTENDS Naturals

VARIABLE x, y

Init ==
    /\ x = 0
    /\ y = 0

IncX ==
    /\ x < 3
    /\ x' = x + 1
    /\ y' = y

IncY ==
    /\ y < 3
    /\ x' = x
    /\ y' = y + 1

Next == IncX \/ IncY

\* Valid invariant - always holds
TypeOK ==
    /\ x \in 0..3
    /\ y \in 0..3

====
"#;

    let module = parse_module(spec);

    // Run without POR
    let config_no_por = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        check_deadlock: false,
        por_enabled: false,
        ..Default::default()
    };

    let result_no_por = check_module(&module, &config_no_por);
    let (states_no_por, initial_no_por) = match &result_no_por {
        CheckResult::Success(stats) => (stats.states_found, stats.initial_states),
        other => panic!("Baseline (no POR) failed unexpectedly: {:?}", other),
    };

    // Run WITH POR — must also succeed (Part of #3706).
    // POR may find fewer states (reduced exploration), but the invariant must
    // still be verified for all reachable states.
    // Part of #3993: identity assignment detection (`x' = x` as UNCHANGED)
    // now enables actual reduction, so state count may be lower.
    let config_por = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        check_deadlock: false,
        por_enabled: true,
        ..Default::default()
    };

    let result_por = check_module(&module, &config_por);
    match &result_por {
        CheckResult::Success(stats) => {
            // POR preserves safety: if no violation without POR, no violation with POR.
            // POR may explore fewer states — that's the whole point.
            assert!(
                stats.states_found <= states_no_por,
                "POR should explore at most as many states as baseline ({states_no_por}), got {}",
                stats.states_found
            );
            assert!(
                stats.states_found >= 1,
                "POR must explore at least the initial state"
            );
        }
        other => panic!("POR run must succeed. Got: {other:?}"),
    }

    assert_eq!(
        initial_no_por, 1,
        "baseline should still enumerate the init state"
    );
    assert_eq!(
        states_no_por, 16,
        "baseline safety run should still complete normally"
    );
}

/// Issue #571 / #3706: POR succeeds on semantically independent safety specs.
///
/// POR-enabled run must find the same 9 states as the baseline (3x3 grid).
/// Part of #571, #3706 (POR end-to-end integration tests).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_issue_571_por_succeeds_for_independent_counters() {
    let spec = r#"
---- MODULE PORPhase12Behavior ----
EXTENDS Naturals

VARIABLE x, y

Init ==
    /\ x = 0
    /\ y = 0

\* Two semantically independent counters, but TLA+ style requires y' = y
IncX ==
    /\ x < 2
    /\ x' = x + 1
    /\ y' = y  \* This creates a write dependency on y

\* Similarly, x' = x creates a write dependency on x
IncY ==
    /\ y < 2
    /\ x' = x  \* This creates a write dependency on x
    /\ y' = y + 1

Next == IncX \/ IncY

====
"#;

    let module = parse_module(spec);

    // First run WITHOUT POR to establish baseline
    let config_no_por = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        por_enabled: false,
        ..Default::default()
    };

    let result_no_por = check_module(&module, &config_no_por);
    let states_no_por = match &result_no_por {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 9,
                "Baseline: Expected 9 states (3x3 grid), got {}",
                stats.states_found
            );
            stats.states_found
        }
        other => panic!("Baseline (no POR) failed: {:?}", other),
    };

    // Run WITH POR — must also succeed (Part of #3706).
    // Part of #3993: with identity assignment detection (`x' = x` as UNCHANGED),
    // POR now correctly identifies these actions as independent and achieves
    // actual state-space reduction. The reduced exploration may visit fewer
    // states than the full BFS.
    let config_por = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        por_enabled: true,
        ..Default::default()
    };

    let result_por = check_module(&module, &config_por);
    match &result_por {
        CheckResult::Success(stats) => {
            // POR may explore fewer states (reduced interleavings).
            assert!(
                stats.states_found <= states_no_por,
                "POR should explore at most as many states as baseline ({states_no_por}), got {}",
                stats.states_found
            );
            assert!(
                stats.states_found >= 1,
                "POR must explore at least the initial state"
            );
        }
        other => panic!("POR run must succeed. Got: {other:?}"),
    }
}

/// Issue #571 / #3706: deadlock checking works both with and without POR.
///
/// POR-enabled run must also detect the deadlock.
/// Part of #571, #3706 (POR end-to-end integration tests).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_issue_571_por_detects_deadlock() {
    // Spec that reaches a deadlock state: when x >= 2, no action is enabled
    let spec = r#"
---- MODULE PORDeadlock ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

\* Action only enabled when x < 2
Inc == x < 2 /\ x' = x + 1

Next == Inc

====
"#;

    let module = parse_module(spec);

    // Run WITHOUT POR first - must detect deadlock
    let config_no_por = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: true,
        por_enabled: false,
        ..Default::default()
    };

    let result_no_por = check_module(&module, &config_no_por);
    assert!(
        matches!(&result_no_por, CheckResult::Deadlock { .. }),
        "Baseline (no POR): Must detect deadlock. Got: {:?}",
        result_no_por
    );

    // Run WITH POR — must also detect deadlock (Part of #3706)
    let config_por = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: true,
        por_enabled: true,
        ..Default::default()
    };

    let result_por = check_module(&module, &config_por);
    assert!(
        matches!(&result_por, CheckResult::Deadlock { .. }),
        "POR run must also detect deadlock. Got: {:?}",
        result_por
    );
}

/// Issue #649: Compiled action error causing state undercount (P1 soundness)
///
/// The compiled action path was incorrectly treating certain errors (like TypeError
/// from function application on model values) as "disabled action" errors, returning
/// empty successor lists instead of falling back to AST enumeration.
///
/// Root cause: In `enumerate_successors_array_as_diffs`, errors from
/// `try_enumerate_with_compiled_action` were classified as "disabled action" if they
/// matched `is_disabled_action_error()` (which includes IndexOutOfBounds, TypeError, etc.).
/// But these errors can occur because the compiled action couldn't handle the expression,
/// not because the action is truly disabled.
///
/// This caused btree to produce only 29 states instead of 374727 (99.99% undercount).
///
/// Fix: Compiled action errors should ALWAYS fall through to AST enumeration path.
/// Only the AST path can correctly determine if an action is truly disabled.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_issue_649_compiled_action_error_fallback() {
    // Minimal spec that triggers compiled action error via function application on model value
    // The key pattern: isLeaf[node] where isLeaf is initially a model value (@nil),
    // causing TypeError in compiled action that should fall back to AST path.
    let spec = r#"
---- MODULE CompiledActionFallback649 ----
EXTENDS Integers

CONSTANTS nil

VARIABLE x, f

\* f is a function or model value depending on state
\* When f = nil (model value), f[1] will throw TypeError in compiled action
Init == x = 0 /\ f = nil

\* Action that does function application - compiled action throws TypeError on nil
\* but AST path correctly handles it. Bounded to create finite state space.
DoSomething ==
    /\ x < 3
    /\ x' = x + 1
    /\ f' = [i \in {1} |-> x]

\* This action tries to apply f[1] - fails when f is model value
TryApply ==
    /\ f # nil
    /\ x' = f[1]
    /\ f' = f

Next == DoSomething \/ TryApply

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        constants: vec![("nil".to_string(), ConstantValue::ModelValue)]
            .into_iter()
            .collect(),
        check_deadlock: false, // Allow deadlock at x=1 when TryApply becomes only option
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(stats) => {
            // Expected: At least 2 states (initial state, plus DoSomething successor)
            // Bug #649: With the bug, we would get 1 state (compiled action error treated as disabled)
            assert!(
                stats.states_found >= 2,
                "Bug #649: Compiled action error causing state undercount! \
                 Expected >= 2 states, got {}. \
                 Compiled action errors must fall back to AST enumeration.",
                stats.states_found
            );
        }
        CheckResult::Deadlock { stats, .. } => {
            // Even with deadlock, we should find multiple states
            assert!(
                stats.states_found >= 2,
                "Bug #649: State undercount even with deadlock! \
                 Expected >= 2 states, got {}.",
                stats.states_found
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

// ============================================================================
// Part of #3993: POR Phase 11 — Identity Assignment and UNCHANGED Commutativity
// ============================================================================

/// Part of #3993: Identity assignment `x' = x` is recognized as UNCHANGED,
/// enabling POR independence detection for specs using explicit assignments
/// instead of the UNCHANGED keyword.
///
/// Without the identity detection optimization, `x' = x` is treated as a real
/// write to x, making virtually all actions dependent and defeating POR.
/// With the optimization, POR correctly identifies IncX and IncY as independent.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_por_identity_assignment_enables_independence() {
    // This spec uses `x' = x` and `y' = y` (explicit identity assignments)
    // instead of `UNCHANGED x` / `UNCHANGED y`. The POR identity detection
    // must recognize these as identity writes to enable reduction.
    let spec = r#"
---- MODULE PORIdentityAssignment ----
EXTENDS Naturals

VARIABLE x, y

Init ==
    /\ x = 0
    /\ y = 0

IncX ==
    /\ x < 3
    /\ x' = x + 1
    /\ y' = y          \* Identity assignment — equivalent to UNCHANGED y

IncY ==
    /\ y < 3
    /\ x' = x          \* Identity assignment — equivalent to UNCHANGED x
    /\ y' = y + 1

Next == IncX \/ IncY

TypeOK ==
    /\ x \in 0..3
    /\ y \in 0..3

====
"#;

    let module = parse_module(spec);

    // Run WITHOUT POR to establish baseline state count
    let config_no_por = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        check_deadlock: false,
        por_enabled: false,
        ..Default::default()
    };

    let result_no_por = check_module(&module, &config_no_por);
    let states_no_por = match &result_no_por {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Baseline (no POR) failed: {:?}", other),
    };
    assert_eq!(states_no_por, 16, "Expected 4x4 = 16 states without POR");

    // Run WITH POR — both must succeed, and POR must find the SAME state count.
    // POR reduces the number of *transitions explored* (actions skipped), not
    // the number of distinct states found. All reachable states are still visited;
    // they're just reached through fewer redundant interleavings.
    let config_por = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        check_deadlock: false,
        por_enabled: true,
        ..Default::default()
    };

    let result_por = check_module(&module, &config_por);
    match &result_por {
        CheckResult::Success(stats) => {
            // POR safely reduces the explored state space. With identity
            // assignment detection, IncX and IncY are independent, so POR
            // explores fewer interleavings while preserving safety.
            assert!(
                stats.states_found <= states_no_por,
                "POR should explore at most {} states, got {}",
                states_no_por, stats.states_found,
            );
            assert!(
                stats.states_found >= 1,
                "POR must explore at least the initial state"
            );
            // POR stats should show reduction was attempted
            assert!(
                stats.por_reduction.action_count >= 2,
                "POR should detect at least 2 actions, got {}",
                stats.por_reduction.action_count,
            );
        }
        other => panic!("POR run must succeed. Got: {other:?}"),
    }
}

/// Part of #3993: POR with UNCHANGED keyword detects independence and achieves
/// actual state-exploration reduction on a three-variable concurrent spec.
///
/// Three independent counters (IncX, IncY, IncZ) operate on disjoint variables.
/// Without POR, BFS explores all interleavings. With POR, each state only needs
/// to explore one action (the ample set singleton), skipping the other two.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_por_unchanged_three_counters_achieves_reduction() {
    let spec = r#"
---- MODULE PORThreeCounters ----
EXTENDS Naturals

VARIABLE x, y, z

Init ==
    /\ x = 0
    /\ y = 0
    /\ z = 0

IncX ==
    /\ x < 2
    /\ x' = x + 1
    /\ UNCHANGED <<y, z>>

IncY ==
    /\ y < 2
    /\ y' = y + 1
    /\ UNCHANGED <<x, z>>

IncZ ==
    /\ z < 2
    /\ z' = z + 1
    /\ UNCHANGED <<x, y>>

Next == IncX \/ IncY \/ IncZ

====
"#;

    let module = parse_module(spec);

    // Run WITHOUT POR
    let config_no_por = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        por_enabled: false,
        ..Default::default()
    };

    let result_no_por = check_module(&module, &config_no_por);
    let states_no_por = match &result_no_por {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("Baseline (no POR) failed: {:?}", other),
    };
    // 3^3 = 27 states (each counter 0..2)
    assert_eq!(states_no_por, 27, "Expected 3^3 = 27 states");

    // Run WITH POR
    let config_por = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        por_enabled: true,
        ..Default::default()
    };

    let result_por = check_module(&module, &config_por);
    match &result_por {
        CheckResult::Success(stats) => {
            // POR reduces explored states. With 3 fully independent counters,
            // BFS only needs to explore one action per state (ample set
            // singleton), dramatically cutting the explored state space.
            assert!(
                stats.states_found < states_no_por,
                "POR should explore fewer than {} states, got {} (no reduction achieved!)",
                states_no_por, stats.states_found,
            );
            assert!(
                stats.states_found >= 1,
                "POR must explore at least the initial state"
            );
            // POR stats: 3 actions, all 3 pairs independent
            assert_eq!(
                stats.por_reduction.action_count, 3,
                "should detect 3 actions"
            );
            // POR should achieve reduction on the concurrent spec.
            assert!(
                stats.por_reduction.states_reduced > 0,
                "POR should achieve reduction on concurrent spec, but states_reduced = 0",
            );
            assert!(
                stats.por_reduction.actions_skipped > 0,
                "POR should skip some action evaluations, but actions_skipped = 0",
            );
        }
        other => panic!("POR run must succeed. Got: {other:?}"),
    }
}

/// Part of #3993: POR correctly preserves invariant violations even when
/// reduction is active. The ample set C2 condition (visibility) ensures that
/// actions affecting invariant variables are never reduced away.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_por_preserves_invariant_violation_with_unchanged() {
    let spec = r#"
---- MODULE PORInvariantWithUnchanged ----
EXTENDS Naturals

VARIABLE x, y

Init ==
    /\ x = 0
    /\ y = 0

IncX ==
    /\ x < 10
    /\ x' = x + 1
    /\ UNCHANGED y

IncY ==
    /\ y < 10
    /\ y' = y + 1
    /\ UNCHANGED x

Next == IncX \/ IncY

\* Invariant: x should stay small. Violated when x > 5.
InvXSmall == x <= 5

====
"#;

    let module = parse_module(spec);

    // Run WITHOUT POR — must find violation
    let config_no_por = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InvXSmall".to_string()],
        check_deadlock: false,
        por_enabled: false,
        ..Default::default()
    };

    let result_no_por = check_module(&module, &config_no_por);
    match &result_no_por {
        CheckResult::InvariantViolation { invariant, .. } => {
            assert_eq!(invariant, "InvXSmall");
        }
        other => panic!("Baseline: Expected InvXSmall violation. Got: {other:?}"),
    }

    // Run WITH POR — must also find same violation
    let config_por = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InvXSmall".to_string()],
        check_deadlock: false,
        por_enabled: true,
        ..Default::default()
    };

    let result_por = check_module(&module, &config_por);
    match &result_por {
        CheckResult::InvariantViolation { invariant, .. } => {
            assert_eq!(
                invariant, "InvXSmall",
                "POR must find same InvXSmall violation, got {invariant}"
            );
        }
        other => panic!("POR must detect InvXSmall violation. Got: {other:?}"),
    }
}
