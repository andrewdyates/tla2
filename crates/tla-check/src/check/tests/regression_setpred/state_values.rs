// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #1828 eval_membership.rs:187: SetPred element in SUBSET membership.
///
/// Tests that a set-filtered value passes SUBSET membership checks correctly.
/// The invariant checks that `evens \in SUBSET {1,2,3,4}` which should be TRUE
/// since evens = {2,4} which is indeed a subset of {1,2,3,4}.
/// But if the SetPred is not materialized before the SUBSET membership check,
/// iter_set() returns None -> false -> spurious invariant violation.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_element_in_subset_membership() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SetPredSubsetMembership ----
EXTENDS Integers
VARIABLE x

Evens == {n \in {1, 2, 3, 4} : n % 2 = 0}

Init == x = Evens
Next == UNCHANGED x

\* This invariant should PASS: {2,4} \in SUBSET {1,2,3,4} is TRUE
Inv == x \in SUBSET {1, 2, 3, 4}
====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Parse errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("module should lower");

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "Should find exactly 1 state (x = {{2,4}}). Found {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "Invariant Inv should PASS - {{2,4}} is in SUBSET {{1,2,3,4}}. \
                 If this fails, SetPred is not being materialized for SUBSET membership. \
                 Error: {error:?}"
            );
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Regression test for proof_coverage audit: UNCHANGED with SetPred state value.
///
/// When a state variable holds a SetPred value (e.g., from Init), and the Next
/// action uses UNCHANGED, the SetPred value must survive the state comparison.
/// If fingerprint computation on SetPred values is broken, UNCHANGED could generate
/// spurious new states or fail to detect identity.
///
/// This is related to the W6 fingerprint identity collapse fix (commit 08ea5beb).
///
/// FIX (#1910): The original test used `{n \in {1,2,3,4} : n % 2 = 0}` which
/// eagerly evaluates to a plain `Value::Set({2,4})` because `{1,2,3,4}` is finite.
/// It never stored a SetPred in state, so UNCHANGED trivially preserved identity.
/// Fixed to use `SUBSET {1,2}` as the filter domain, which triggers the lazy
/// SetPred path in eval_set_filter.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_unchanged_preserves_setpred_value_identity() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE UnchangedSetPred ----
EXTENDS Integers, FiniteSets
VARIABLE x

\* Init produces a SetPred value via SUBSET filter (lazy path).
\* SUBSET {1,2} = {{}, {1}, {2}, {1,2}}, filter Cardinality > 0 -> {{1}, {2}, {1,2}}.
\* x gets the set {{1}, {2}, {1,2}} which is a materialized SetPred.
Init == x = {s \in SUBSET {1, 2} : Cardinality(s) > 0}

\* UNCHANGED must recognize that the value is the same
Next == UNCHANGED x

====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Parse errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("module should lower");

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            // Only 1 state: x = {{1}, {2}, {1,2}}. UNCHANGED means no new states.
            assert_eq!(
                stats.states_found, 1,
                "UNCHANGED with SetPred value should find exactly 1 state. \
                 If more, fingerprint identity for SetPred/materialized values is broken \
                 (see W6 fix 08ea5beb). Found {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("UNCHANGED with SetPred value should not error. Error: {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Regression test for proof_coverage audit: invariant evaluation on SetPred-containing state.
///
/// When a state variable holds a value that was computed via set filtering (SetPred),
/// invariants that compare or operate on this value must see the materialized form,
/// not the lazy SetPred wrapper. This tests that the invariant evaluator correctly
/// handles SetPred values stored in state.
///
/// The invariant `Cardinality(x) = 2` requires iterating x's elements,
/// which fails if x is still a lazy SetPred without an eval context.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_invariant_over_setpred_state_value() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE InvariantSetPredState ----
EXTENDS Integers, FiniteSets
VARIABLE x

Init == x \in {{n \in {1, 2, 3} : n > 1}, {n \in {1, 2, 3} : n < 3}}

Next == UNCHANGED x

\* Both possible values ({2,3} and {1,2}) have cardinality 2
Inv == Cardinality(x) = 2

====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Parse errors: {:?}",
        lower_result.errors
    );
    let module = lower_result.module.expect("module should lower");

    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["Inv".to_string()],
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            // Two init states: x={2,3} and x={1,2}, both have Cardinality 2
            assert_eq!(
                stats.states_found, 2,
                "Invariant over SetPred state should find 2 states. \
                 If 0, the SetPred Init domain couldn't be enumerated. \
                 If invariant fails, Cardinality can't handle materialized SetPred. Found {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "Invariant over SetPred state should not error. \
                 If Cardinality fails, the SetPred value was not materialized before \
                 invariant evaluation. Error: {error:?}"
            );
        }
        other => panic!("unexpected result: {other:?}"),
    }
}
