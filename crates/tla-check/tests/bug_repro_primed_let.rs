// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Primed variable assignments and LET bindings - Bugs #564, #304
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::parse_module;
use tla_check::{check_module, CheckResult, Config};

// ============================================================================
// Bug: Compiled assignments must allow primed RHS + correlated copies
// ============================================================================

/// Regression test: action-level assignments must be able to reference other primed vars.
///
/// Minimal pattern:
///   /\ lo' = 1
///   /\ buff' = lo'
///
/// The preprocessed/compiled Next enumerator must treat `lo'` as a next-state read
/// when compiling `buff'`'s RHS; otherwise it will either fail to enumerate the
/// transition or compute the wrong successor.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_action_assignment_can_reference_primed_var() {
    let spec = r#"
---- MODULE PrimedRhsAssignment ----
VARIABLES lo, buff

Init == /\ lo = 0 /\ buff = 0

Next ==
  /\ lo' = 1
  /\ buff' = lo'

Inv == lo = buff

Spec == Init /\ [][Next]_<<lo, buff>>
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 2,
                "Expected 2 states (0,0) and (1,1), got {}",
                stats.states_found
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Regression test: correlated copies x' = y' must preserve nondeterministic choices.
///
/// Minimal pattern:
///   /\ y' \in {0, 1}
///   /\ x' = y'
///
/// The successor set should contain exactly the states where x=y.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_action_assignment_copy_from_inset_prime() {
    let spec = r#"
---- MODULE PrimedCopyFromInSet ----
VARIABLES x, y

Init == /\ x = 0 /\ y = 0

Next ==
  /\ y' \in {0, 1}
  /\ x' = y'

Inv == x = y

Spec == Init /\ [][Next]_<<x, y>>
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 2,
                "Expected 2 states where x=y, got {}",
                stats.states_found
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

// ============================================================================
// Bug: LET bindings with primed variables (BufferedRandomAccessFile)
// ============================================================================

/// Regression test: LET bindings that reference primed variables must be handled
/// by substitution, not evaluation.
///
/// The BufferedRandomAccessFile spec uses patterns like:
///   LET diskPosA == lo' IN buff' = MkArray(...diskPosA...)
///
/// When we try to evaluate `lo'` without a next-state context, evaluation fails.
/// The fix substitutes the primed expression directly into the body.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_let_binding_with_primed_variable() {
    let spec = r#"
---- MODULE LetPrimeBinding ----
EXTENDS Naturals

VARIABLES lo, marker

Init == lo = 0 /\ marker = 0

\* LET x == lo' pattern - must use substitution
ComputeMarker ==
  LET x == lo' IN
  marker' = x * 10

ChangeLo(newLo) ==
  /\ lo' = newLo
  /\ ComputeMarker

Next == \E nl \in 0..3: ChangeLo(nl)

Spec == Init /\ [][Next]_<<lo, marker>>
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            // 4 states: lo \in {0, 1, 2, 3}, marker = lo * 10
            assert_eq!(
                stats.states_found, 4,
                "Expected 4 states (lo=0,1,2,3 with marker=lo*10), got {}",
                stats.states_found
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

// ============================================================================
// Bug #564: LET bindings not captured in symbolic assignment extraction
// ============================================================================

/// Bug #564: LET bindings must be captured when extracting symbolic assignments.
///
/// The bug: In extract_symbolic_assignments(), LET bindings were stored via
/// env.insert() but get_local_bindings() only returned local_stack entries.
/// This caused "Undefined variable" errors during deferred evaluation.
///
/// This test uses a pattern common in specs like MultiPaxos where LET-bound
/// values are used in primed variable expressions.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_564_let_binding_in_primed_expression() {
    let spec = r#"
---- MODULE LetBindingInPrimed ----
EXTENDS Integers

VARIABLE x, y

Init ==
    /\ x = 0
    /\ y = 0

\* Constrain state space by only incrementing when x < 3
Next ==
    /\ x < 3
    /\ LET c == x + 1
       IN /\ x' = c
          /\ y' = c * 2

Inv == y = x * 2
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    // This should NOT produce an "Undefined variable: c" error
    // With the fix, it explores states: (0,0), (1,2), (2,4), (3,6) = 4 states
    // The spec deadlocks when x=3 (no next action enabled), which is expected.
    let states = match &result {
        CheckResult::Success(stats) => stats.states_found,
        CheckResult::Deadlock { stats, .. } => stats.states_found,
        other => panic!("Expected success or deadlock, got: {:?}", other),
    };
    assert_eq!(states, 4, "Expected 4 states (x=0,1,2,3), got {}", states);
}

/// Bug #564 variant: nested LET bindings in deferred context
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_564_nested_let_in_primed() {
    let spec = r#"
---- MODULE NestedLetPrimed ----
EXTENDS Integers

VARIABLE v

Init == v = 0

\* Constrain state space - only step when v < 10
Next ==
    /\ v < 10
    /\ LET a == v + 1
           b == a * 2
       IN v' = b

Inv == v >= 0
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    // Trace: v=0 -> v=2 -> v=6 -> v=14 (stops because 14 >= 10)
    // States: 0, 2, 6, 14 = 4 states
    // The spec deadlocks when v=14 (no next action enabled), which is expected.
    let states = match &result {
        CheckResult::Success(stats) => stats.states_found,
        CheckResult::Deadlock { stats, .. } => stats.states_found,
        other => panic!(
            "Expected success or deadlock with nested LET, got: {:?}",
            other
        ),
    };
    assert_eq!(states, 4, "Expected 4 states (v=0,2,6,14), got {}", states);
}

// ============================================================================
// Bug #304: LET binding depth bug in compiled guards
// ============================================================================

/// Bug #304: LET bindings that capture quantifier-bound variables must evaluate correctly
/// under nested quantifiers when invariants are compiled.
///
/// Regression root cause: LET definitions were compiled at their definition-site scope depth,
/// but when inlined under additional binders the LocalVar depths were not adjusted, causing
/// captured variables to read the wrong binding (typically the most recently bound variable).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_304_let_binding_depth_in_compiled_guards() {
    let spec = r#"
---- MODULE TestLETDepthBug304 ----
\* Based on tests/specs/bug_repro/TestLETDepthBug.tla
EXTENDS Integers

VARIABLES x

Init == x = 0

\* Finite state space without deadlock (self-loop at x=3)
Next == (x < 3 /\ x' = x + 1) \/ (x = 3 /\ x' = x)

TestNoLET ==
    \A i \in {1, 2}:
        \A j \in {3, 4}:
            i < j

TestWithLET ==
    \A i \in {1, 2}:
        LET k == i
        IN \A j \in {3, 4}:
            k < j

TestWithLETExpr ==
    \A i \in {1, 2}:
        LET k == i + 10
        IN \A j \in {3, 4}:
            k > j

TestDoubleNest ==
    \A i \in {1, 2}:
        LET k == i
        IN \A j \in {3, 4}:
            \A m \in {5, 6}:
                k < j /\ j < m

TestWithRecord ==
    LET rec == [a |-> 1, b |-> 2]
    IN \A i \in {0, 1}:
        rec.a <= rec.b

TestNestedLET ==
    \A i \in {1, 2}:
        LET k == i
        IN \A j \in {3, 4}:
            LET m == j
            IN k < m

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![
            "TestNoLET".to_string(),
            "TestWithLET".to_string(),
            "TestWithLETExpr".to_string(),
            "TestDoubleNest".to_string(),
            "TestWithRecord".to_string(),
            "TestNestedLET".to_string(),
        ],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 4,
                "Expected 4 states, got {}",
                stats.states_found
            );
        }
        other => panic!("Expected success, got: {:?}", other),
    }
}
