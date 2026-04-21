// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test for #1282: UNCHANGED must work when variable references are
//! resolved to `Expr::StateVar` nodes (array-based BFS path).
//!
//! Before commit 51950ec5, `extract_unchanged_vars_symbolic_with_ctx` only
//! matched `Expr::Ident(name, NameId::INVALID)`, not `Expr::StateVar(name, _, _)`. This meant
//! that on the array-based BFS path (where the resolution pass converts
//! identifiers to StateVar nodes), UNCHANGED expressions silently failed to
//! produce the `Unchanged(var)` symbolic assignment. The result was missing
//! transitions in specs using UNCHANGED.

mod common;

use tla_check::{CheckResult, Config, ModelChecker};

/// Regression test: UNCHANGED on a single variable in a disjunctive Next.
///
/// Spec has two actions: IncX (increments x, UNCHANGED y) and IncY
/// (increments y, UNCHANGED x). The state space is a 4x4 grid (x,y in 0..3).
///
/// If UNCHANGED extraction fails for StateVar nodes, the actions lose their
/// "keep other variable" semantics, causing either missing transitions or
/// errors. The correct state count is 16 (4 * 4 grid fully reachable).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn unchanged_single_var_disjunctive_next_state_count() {
    let spec = r#"
---- MODULE UnchangedRegression ----
VARIABLES x, y

Init == x = 0 /\ y = 0

IncX == x < 3 /\ x' = x + 1 /\ UNCHANGED y
IncY == y < 3 /\ y' = y + 1 /\ UNCHANGED x

Next == IncX \/ IncY

TypeOK == x \in 0..3 /\ y \in 0..3
====
"#;

    let module = common::parse_module_strict(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // 4*4 grid = 16 states, 1 initial state
            assert_eq!(
                stats.states_found, 16,
                "Expected 16 distinct states (4x4 grid), got {}. \
                 UNCHANGED may not be working on StateVar nodes.",
                stats.states_found
            );
            assert_eq!(stats.initial_states, 1);
        }
        other => panic!(
            "Expected Success, got {:?}. UNCHANGED extraction may have failed.",
            other
        ),
    }
}

/// Regression test: UNCHANGED on a tuple of variables (<<x, y>>).
///
/// Uses `UNCHANGED <<x, y>>` which is syntactically a tuple containing
/// state variable references. Both the Ident and StateVar paths through
/// `extract_unchanged_vars_symbolic_with_ctx` must handle the Tuple case.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn unchanged_tuple_all_vars_state_count() {
    let spec = r#"
---- MODULE UnchangedTuple ----
VARIABLES x, y, z

Init == x = 0 /\ y = 0 /\ z = 0

Step == z < 2 /\ z' = z + 1 /\ UNCHANGED <<x, y>>

Next == Step

TypeOK == x \in 0..0 /\ y \in 0..0 /\ z \in 0..2
====
"#;

    let module = common::parse_module_strict(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // Only z changes: 0, 1, 2 → 3 states
            assert_eq!(
                stats.states_found, 3,
                "Expected 3 distinct states (z in 0..2), got {}. \
                 UNCHANGED <<x,y>> may not be extracting tuple elements.",
                stats.states_found
            );
            assert_eq!(stats.initial_states, 1);
        }
        other => panic!(
            "Expected Success, got {:?}. UNCHANGED tuple extraction may have failed.",
            other
        ),
    }
}

/// Regression test: UNCHANGED combined with explicit priming in same action.
///
/// Tests that when one variable uses UNCHANGED and another uses explicit
/// prime assignment, both paths work correctly through the array-based BFS.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn unchanged_mixed_with_prime_state_count() {
    let spec = r#"
---- MODULE UnchangedMixed ----
VARIABLES a, b, c

Init == a = 0 /\ b = 0 /\ c = 0

\* Only a changes, b and c stay via UNCHANGED
ActionA == a < 2 /\ a' = a + 1 /\ UNCHANGED <<b, c>>

\* Only b changes, a via UNCHANGED, c via explicit prime
ActionB == b < 2 /\ b' = b + 1 /\ UNCHANGED a /\ c' = c

\* Only c changes
ActionC == c < 2 /\ c' = c + 1 /\ UNCHANGED <<a, b>>

Next == ActionA \/ ActionB \/ ActionC

TypeOK == a \in 0..2 /\ b \in 0..2 /\ c \in 0..2
====
"#;

    let module = common::parse_module_strict(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // 3*3*3 = 27 states fully reachable
            assert_eq!(
                stats.states_found, 27,
                "Expected 27 distinct states (3x3x3 grid), got {}. \
                 UNCHANGED may not work correctly with mixed prime assignments.",
                stats.states_found
            );
            assert_eq!(stats.initial_states, 1);
        }
        other => panic!(
            "Expected Success, got {:?}. Mixed UNCHANGED/prime may have failed.",
            other
        ),
    }
}
