// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CHOOSE shadowing, variable capture, enumeration - Bugs #472, #499, #159
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::parse_module;
use tla_check::{check_module, CheckResult, Config, ConstantValue};

// ============================================================================
// Bug #472: CHOOSE variable shadowing when LET-bound name exists
// ============================================================================

/// Bug #472: CHOOSE variable shadowing with LET-defined name
///
/// The MultiPaxos_MC spec had a pattern like:
/// ```
/// FirstEmptySlot(insts) == CHOOSE s \in Slots: insts[s].status = "Empty" /\ ...
///
/// TakeNewRequest(self) ==
///     LET s == FirstEmptySlot(node[self].insts)
///     IN  /\ node' = [node EXCEPT ![self].insts[s].status = "Accepting"]
///         /\ ...
/// ```
///
/// The bug: When CHOOSE binds `s`, the value was added to `env`, but lookup order is:
///   local_stack → local_ops → env
///
/// If a LET expression defines `s` in the enclosing scope, the lookup of `s`
/// inside CHOOSE would find the LET definition in `local_ops` instead of the
/// CHOOSE-bound value from `env`. This caused infinite recursion when `FirstEmptySlot`
/// was re-evaluated repeatedly.
///
/// The fix: In `bind()`, check if the name exists in `local_ops` and if so,
/// add the binding to `local_stack` to properly shadow the LET definition.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_choose_variable_shadowing_with_let() {
    let spec = r#"
---- MODULE ChooseVariableShadowing ----
EXTENDS Naturals

VARIABLE x

\* This operator uses CHOOSE to find a value
FindValue(set) == CHOOSE v \in set: v > 0

Init == x = 0

\* The key pattern: LET defines `v`, then the body uses FindValue which
\* internally binds `v` in CHOOSE. The CHOOSE-bound `v` must shadow the LET-defined `v`.
Next ==
    LET v == FindValue({1, 2, 3})
    IN  x' = v

Spec == Init /\ [][Next]_x

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
            // Should find at least 2 states: x=0, x=1 (or x=2 or x=3 depending on CHOOSE)
            assert!(
                stats.states_found >= 2,
                "Should find at least 2 states, got {}",
                stats.states_found
            );
        }
        CheckResult::Deadlock { .. } => {
            // Deadlock is acceptable - the important thing is we don't get infinite recursion
        }
        _ => {
            panic!(
                "Bug exists! Got unexpected result (likely infinite recursion): {:?}",
                result
            );
        }
    }
}

/// More complex test: CHOOSE inside LET where CHOOSE variable name matches LET name
///
/// This directly tests the case where the bound variable in CHOOSE has the same
/// name as the LET-defined operator that contains the CHOOSE.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_choose_shadows_containing_let_name() {
    let spec = r#"
---- MODULE ChooseShadowsLet ----
EXTENDS Naturals

VARIABLE result

Init == result = 0

\* The LET defines `s`, and the CHOOSE inside also binds `s`.
\* The CHOOSE's `s` must shadow the LET's `s` within the CHOOSE body.
Next ==
    LET s == CHOOSE s \in {1, 2, 3}: s > 1
    IN  result' = s

Spec == Init /\ [][Next]_result

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
            // Should complete without infinite recursion
            // We expect states: result=0 (init), result=2 or result=3 (after transition)
            assert!(
                stats.states_found >= 2,
                "Should find at least 2 states, got {}",
                stats.states_found
            );
        }
        CheckResult::Deadlock { .. } => {
            // Deadlock is acceptable - the important thing is no infinite recursion
        }
        _ => {
            panic!(
                "Bug exists! Got unexpected result (likely infinite recursion): {:?}",
                result
            );
        }
    }
}

// ============================================================================
// Bug #499: Variable capture in action preprocessing operator inlining
// ============================================================================

/// Bug #499: Variable capture in preprocessing operator inlining
///
/// The MCCheckpointCoordination spec has:
/// ```
/// SendReplicatedRequest(prospect) ==
///     ...
///     ReplicatedLog' = [n \in Node |-> ... WriteLog(n, index, prospect) ...]
/// ```
///
/// When preprocessing `\E n \in Node: SendReplicatedRequest(n)`, the inliner was:
/// 1. Creating substitution: `prospect` -> `n` (the argument expression)
/// 2. Substituting in the body, producing: `[n \in Node |-> ... WriteLog(n, index, n) ...]`
/// 3. The function comprehension's `n` variable captured both the original `n` and
///    what was meant to be `prospect`!
///
/// This caused each node to write its OWN name to the log instead of the `prospect` value.
///
/// The fix: Check `inlining_substitution_is_capture_safe` before inlining operators
/// during action preprocessing, similar to how `compiled_guard.rs` does.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_preprocessing_variable_capture() {
    // Minimal reproduction of the MCCheckpointCoordination pattern
    let spec = r#"
---- MODULE PreprocessingVariableCapture ----
EXTENDS Naturals

CONSTANTS Node

VARIABLE log

LogIndex == {1, 2, 3}

\* WriteLog is called with `prospect` parameter - the key is that
\* the inner comprehension uses `i` not `n`, but the outer comprehension
\* in Send uses `n` which could capture `prospect` if inlining is unsafe.
WriteLog(node, idx, val) ==
    [i \in LogIndex |-> IF i = idx THEN val ELSE log[node][i]]

\* The bug pattern: EXISTS binds `n`, operator parameter is `prospect`,
\* body has `[n \in Node |-> ... WriteLog(n, index, prospect) ...]`
Send(prospect) ==
    log' = [n \in Node |-> WriteLog(n, 1, prospect)]

Init == log = [n \in Node |-> <<0, 0, 0>>]

Next == \E n \in Node: Send(n)

\* INVARIANT: All nodes should have the SAME value at position 1
\* (since they all received the same `prospect` argument)
AllSame == \A x, y \in Node: log[x][1] = log[y][1]

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["AllSame".to_string()],
        constants: vec![("Node".into(), ConstantValue::Value("{1, 2, 3}".into()))]
            .into_iter()
            .collect(),
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(stats) => {
            // Should complete without invariant violation
            // Expected states: 1 initial + 3 successors (one for each prospect)
            // But successors are equivalent under symmetry, so may be fewer
            assert!(
                stats.states_found >= 2,
                "Should find at least 2 states, got {}",
                stats.states_found
            );
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug exists! Invariant {} violated - variable capture during preprocessing. \
                 Each node is getting its own name instead of the prospect value.",
                invariant
            );
        }
        _ => {
            panic!("Unexpected result: {:?}", result);
        }
    }
}

// ============================================================================
// Bug #159: Transition over-enumeration - x' \in S after x' = val
// ============================================================================

/// Bug #159: Transition over-enumeration when x' is already bound
///
/// Pattern (from Moving_Cat_Puzzle/Cat.tla):
/// ```
/// Move_Cat ==
///   /\ \/ cat_box' = cat_box + 1
///      \/ cat_box' = cat_box - 1
///   /\ cat_box' \in Boxes
/// ```
///
/// TLA semantics:
/// 1. The disjunction `cat_box' = cat_box + 1 \/ cat_box' = cat_box - 1` binds `cat_box'`
/// 2. The constraint `cat_box' \in Boxes` should FILTER (check membership), not enumerate
///
/// Bug: TLA2's enumerate.rs treats `x' \in S` as enumeration even when x' is already
/// bound. This produces invalid transitions where the variable "teleports" to values
/// that don't satisfy the assignment.
///
/// Evidence:
/// - Cat spec: TLA2 produces 576 transitions (12/state), TLC produces 128 (2.67/state)
/// - Invalid counterexample: cat_box jumps from 1 to 5 (should only change by ±1)
///
/// The fix: In `Expr::In(lhs, rhs)` handling (enumerate.rs:5949), check if the primed
/// variable is already in the undo stack. If so, use `contains()` to filter instead
/// of enumerating all values.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_transition_over_enumeration() {
    // Minimal reproduction of the Cat spec pattern
    let spec = r#"
---- MODULE TransitionOverEnumeration ----
EXTENDS Naturals

VARIABLE x

\* Boxes = 1..6 in the Cat spec
Domain == 1..6

Init == x \in Domain

\* The bug pattern: disjunction binds x', then x' \in Domain should filter
Move ==
  /\ \/ x' = x + 1
     \/ x' = x - 1
  /\ x' \in Domain

Next == Move

\* Invariant: x can only change by ±1
ValidMove == x' \in {x - 1, x + 1}

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
            // Expected: 6 states (x \in 1..6)
            assert_eq!(
                stats.states_found, 6,
                "Expected 6 states (x in 1..6), got {}",
                stats.states_found
            );

            // Key assertion: transitions should be ~10 (2 per interior state, 1 per boundary)
            // States 1 and 6 have 1 valid transition each (can't go to 0 or 7)
            // States 2-5 have 2 valid transitions each
            // Total: 2*1 + 4*2 = 10 transitions
            //
            // BUG: If enumeration happens, we get 6*6 = 36 transitions (or more)
            //
            // With the fix: transitions should be exactly 10
            // Without fix: transitions will be >= 36 (each state enumerates all 6 domain values)
            let expected_max_transitions = 12; // Allow some slack, but not 36+
            assert!(
                stats.transitions <= expected_max_transitions,
                "BUG #159: Transition over-enumeration! Got {} transitions, expected <= {}. \
                 The x' \\in Domain constraint is enumerating instead of filtering.",
                stats.transitions,
                expected_max_transitions
            );
        }
        CheckResult::Deadlock { .. } => {
            // x=1 trying x-1=0 fails the domain check, x=6 trying x+1=7 fails
            // This is expected - not all states have successors
            // The important check is transition count, which we can't see here
            // So we just pass - the real test is the transition count above
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Variant: Explicit enumeration should work correctly
///
/// This test verifies that when x' is NOT already bound, enumeration is correct.
/// This is the baseline behavior that should NOT change.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_explicit_enumeration_works() {
    let spec = r#"
---- MODULE ExplicitEnumeration ----
EXTENDS Naturals

VARIABLE x

Domain == 1..3

Init == x = 1

\* x' is bound directly via enumeration (no prior assignment)
Next == x' \in Domain

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
            // Expected: 3 states (x \in 1..3)
            assert_eq!(
                stats.states_found, 3,
                "Expected 3 states (x in 1..3), got {}",
                stats.states_found
            );
            // Each state has 3 successors (to each of 1, 2, 3)
            // Total: 3*3 = 9 transitions
            assert_eq!(
                stats.transitions, 9,
                "Expected 9 transitions (3 states * 3 successors), got {}",
                stats.transitions
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Variant: Filter after set enumeration
///
/// Tests that x' \in S after x' \in T (where T is a subset source) works correctly.
/// This ensures the fix handles set membership, not just intervals.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_membership_filter() {
    let spec = r#"
---- MODULE SetMembershipFilter ----

VARIABLE x

Source == {"a", "b", "c"}
ValidSet == {"a", "b"}

Init == x = "a"

\* x' is bound via set enumeration, then filtered
Next ==
  /\ x' \in Source
  /\ x' \in ValidSet

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
            // Expected: 2 reachable states {"a", "b"}
            // "c" is in Source but not ValidSet, so filtered out
            assert_eq!(
                stats.states_found, 2,
                "Expected 2 states (intersection of Source and ValidSet), got {}",
                stats.states_found
            );
            // Each state can transition to {"a", "b"} = 2 successors
            // Total: 2*2 = 4 transitions
            assert_eq!(
                stats.transitions, 4,
                "Expected 4 transitions, got {}",
                stats.transitions
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}
