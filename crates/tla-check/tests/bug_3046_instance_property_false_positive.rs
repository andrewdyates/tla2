// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression test for #3046: INSTANCE...WITH PROPERTY false positive.
//!
//! When a PROPERTY references a named INSTANCE spec (e.g., `LSpec == L!Spec`),
//! the action-level Always terms (e.g., `[][Next]_vars` from the INSTANCE'd module)
//! must be evaluated correctly during BFS, not deferred to the liveness checker.
//!
//! The bug was that top-level ModuleRef action-level Always terms were routed to
//! the liveness checker via `has_non_safety_terms = true`, which caused the property
//! to be evaluated incorrectly, producing false positives (e.g., Peterson finding
//! 7 states instead of 42, EWD998ChanID finding 2 states instead of 14).
//!
//! The fix routes action-level Always terms containing ModuleRef nodes to the
//! eval-based BFS-inline path (eval_implied_actions), which correctly handles
//! INSTANCE WITH substitutions via eval_prime.

mod common;

use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::FileId;

/// Abstract spec module: a simple counter with two states ("idle", "active").
///
/// This module defines Spec = Init /\ [][Next]_vars which is the property
/// that the concrete module must satisfy via INSTANCE...WITH.
fn abstract_spec_module() -> tla_core::ast::Module {
    common::parse_module_strict_with_id(
        r#"
---- MODULE AbstractSpec ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 3

vars == << x >>

Spec == Init /\ [][Next]_vars
====
"#,
        FileId(1),
    )
}

/// Regression test for #3046: INSTANCE...WITH PROPERTY with ModuleRef spec.
///
/// Pattern: A concrete spec that refines AbstractSpec via identity mapping
/// (`A == INSTANCE AbstractSpec WITH x <- x`) and checks `ASpec == A!Spec`
/// as a PROPERTY.
///
/// Without the fix, the property evaluator incorrectly defers the action-level
/// Always term to the liveness checker, causing a false positive
/// ("Action property ASpec is violated").
///
/// With the fix, the eval-based BFS-inline path correctly evaluates the property,
/// finding all states without error.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_3046_instance_with_property_no_false_positive() {
    let abstract_mod = abstract_spec_module();

    // Concrete module: implements the same spec and verifies refinement via PROPERTY.
    // The identity mapping (x <- x) means the refinement trivially holds.
    let concrete = common::parse_module_strict_with_id(
        r#"
---- MODULE Concrete ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 3

vars == << x >>

Spec == Init /\ [][Next]_vars

\* Identity refinement mapping
A == INSTANCE AbstractSpec WITH x <- x

\* PROPERTY that triggers the bug: ModuleRef to INSTANCE'd Spec
ASpec == A!Spec
====
"#,
        FileId(0),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["ASpec".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&concrete, &[&abstract_mod], &config);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // The spec has exactly 3 states: x=0, x=1, x=2 (cyclic mod 3).
            assert_eq!(
                stats.states_found, 3,
                "Bug #3046: expected 3 states for cyclic counter, got {}",
                stats.states_found
            );
        }
        CheckResult::PropertyViolation { property, .. } => {
            panic!(
                "Bug #3046 regression: INSTANCE...WITH PROPERTY '{}' reported as \
                 violated (false positive). The action-level Always term from the \
                 ModuleRef property is being incorrectly evaluated. The fix routes \
                 ModuleRef-containing action-level terms to the eval-based BFS-inline path \
                 instead of the liveness checker.",
                property
            );
        }
        other => panic!("Bug #3046: unexpected result: {other:?}"),
    }
}

/// Regression test for #3046: verify state count matches with and without PROPERTY.
///
/// The original bug caused Peterson to find 7 states with PROPERTY but 42 without.
/// This test verifies that adding a (valid) PROPERTY doesn't alter the state count.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_3046_property_does_not_reduce_state_count() {
    let abstract_mod = abstract_spec_module();

    let concrete = common::parse_module_strict_with_id(
        r#"
---- MODULE Concrete2 ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 3

vars == << x >>

Spec == Init /\ [][Next]_vars

A == INSTANCE AbstractSpec WITH x <- x
ASpec == A!Spec
====
"#,
        FileId(0),
    );

    // First: run without PROPERTY to get baseline state count.
    let config_no_prop = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&concrete, &[&abstract_mod], &config_no_prop);
    let baseline_states = match checker.check() {
        CheckResult::Success(stats) => stats.states_found,
        other => panic!("baseline (no PROPERTY) failed: {other:?}"),
    };

    assert_eq!(
        baseline_states, 3,
        "baseline: expected 3 states for cyclic counter"
    );

    // Second: run with PROPERTY — state count must match.
    let config_with_prop = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["ASpec".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker =
        ModelChecker::new_with_extends(&concrete, &[&abstract_mod], &config_with_prop);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, baseline_states,
                "Bug #3046: PROPERTY should not reduce state count. \
                 Without PROPERTY: {} states, with PROPERTY: {} states.",
                baseline_states, stats.states_found
            );
        }
        CheckResult::PropertyViolation { property, .. } => {
            panic!(
                "Bug #3046 regression: PROPERTY '{}' falsely violated. \
                 Baseline (no PROPERTY) found {} states successfully.",
                property, baseline_states
            );
        }
        other => panic!("unexpected result with PROPERTY: {other:?}"),
    }
}

/// Regression test for #3046: non-trivial refinement mapping.
///
/// Tests the more realistic pattern where the concrete module has different
/// variables than the abstract module, connected via a refinement mapping.
/// This exercises the INSTANCE WITH substitution through the property evaluation
/// path, which was the root cause of the Peterson/EWD998ChanID false positives.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn bug_3046_nontrivial_refinement_property() {
    // Abstract module: simple toggle with variable `flag`
    let abstract_mod = common::parse_module_strict_with_id(
        r#"
---- MODULE Toggle ----

VARIABLE flag

Init == flag = FALSE

Next == flag' = ~flag

vars == << flag >>

Spec == Init /\ [][Next]_vars
====
"#,
        FileId(1),
    );

    // Concrete module: counter that refines Toggle via a mapping
    let concrete = common::parse_module_strict_with_id(
        r#"
---- MODULE ConcreteToggle ----
EXTENDS Integers

VARIABLE count

Init == count = 0

Next == count' = (count + 1) % 4

vars == << count >>

Spec == Init /\ [][Next]_vars

\* Refinement: map count to flag via parity
flag_mapping == (count % 2) = 1

T == INSTANCE Toggle WITH flag <- flag_mapping

\* PROPERTY: the refinement check
TSpec == T!Spec
====
"#,
        FileId(0),
    );

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        properties: vec!["TSpec".to_string()],
        check_deadlock: false,
        ..Default::default()
    };

    let mut checker = ModelChecker::new_with_extends(&concrete, &[&abstract_mod], &config);
    let result = checker.check();

    match result {
        CheckResult::Success(stats) => {
            // 4 states: count = 0, 1, 2, 3
            assert_eq!(
                stats.states_found, 4,
                "Bug #3046: expected 4 states for mod-4 counter, got {}",
                stats.states_found
            );
        }
        CheckResult::PropertyViolation { property, .. } => {
            panic!(
                "Bug #3046 regression: non-trivial refinement PROPERTY '{}' \
                 falsely violated. The INSTANCE WITH substitution is not being \
                 correctly evaluated through the BFS-inline property path.",
                property
            );
        }
        other => panic!("Bug #3046: unexpected result: {other:?}"),
    }
}
