// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Algorithm audit: nested SetPred materialization via SUBSET filter of SUBSET filter.
///
/// This tests the recursive materialization path in eval_iter_set / materialize_setpred_to_vec.
/// The inner `{y \in SUBSET {1,2} : Cardinality(y) = 1}` produces a lazy SetPred (SUBSET
/// triggers the lazy path in eval_set_filter). The outer `{x \in inner : 1 \in x}` must
/// materialize the inner SetPred to iterate it, then apply its own filter.
///
/// Expected result: `{{1}}` - the only size-1 subset of {1,2} containing 1.
/// If materialization fails, the outer filter would either error or produce empty set.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_nested_setpred_subset_filter_materializes_correctly() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE NestedSetPredSubset ----
EXTENDS Integers, FiniteSets
VARIABLE x

Inner == {y \in SUBSET {1, 2} : Cardinality(y) = 1}
Outer == {s \in Inner : 1 \in s}

Init == x = Outer
Next == UNCHANGED x
Inv == x = {{1}}
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
                "Nested SetPred filter should produce exactly 1 initial state. \
                 If 0, inner SetPred materialization failed. Found {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "Nested SetPred filter should not error. \
                 If eval_iter_set fails to recursively materialize, this panics. Error: {error:?}"
            );
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Algorithm audit: SetPred with always-false predicate on SUBSET domain.
///
/// `{x \in SUBSET {1, 2, 3} : FALSE}` must produce `{}` (empty set), not an error
/// and not a lazy SetPred that behaves as non-empty. SUBSET {1,2,3} has 8 elements;
/// the predicate rejects all of them. This tests the boundary where materialization
/// succeeds but produces zero elements.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_empty_result_from_always_false_predicate() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SetPredEmptyResult ----
EXTENDS Integers, FiniteSets
VARIABLE x

EmptyFilter == {s \in SUBSET {1, 2, 3} : FALSE}

Init == x = Cardinality(EmptyFilter)
Next == UNCHANGED x
Inv == x = 0
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
                "Empty SetPred should produce exactly 1 state (x=0). Found {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "Empty SetPred should not error. \
                 Cardinality of empty materialized set must be 0. Error: {error:?}"
            );
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Algorithm audit: SetPred cardinality varies with state - verifies materialization
/// uses the current state, not a stale captured snapshot.
///
/// The spec has x cycling through {0, 1, 2}. The invariant checks
/// `Cardinality({n \in {0, 1, 2, 3} : n > x})` against the expected value `3 - x`.
/// If SetPred captures stale state, the cardinality would be wrong for at least one state.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setpred_cardinality_depends_on_current_state() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SetPredStateDep ----
EXTENDS Integers, FiniteSets
VARIABLE x

Init == x = 0
Next == IF x < 2 THEN x' = x + 1 ELSE UNCHANGED x

\* {n \in {0,1,2,3} : n > x} has cardinality 3-x for x \in {0,1,2}
Inv == Cardinality({n \in {0, 1, 2, 3} : n > x}) = 3 - x
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
            // States: x=0, x=1, x=2. Cardinalities: 3, 2, 1.
            assert_eq!(
                stats.states_found, 3,
                "State-dependent SetPred should explore 3 states (x=0,1,2). Found {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "State-dependent SetPred invariant should pass. \
                 If Cardinality varies incorrectly, captured state is stale. Error: {error:?}"
            );
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Regression test for b3cf3ad (Part of #2834): SetPred tuple destructuring in lazy
/// materialization, exercised at the model checker level.
///
/// The key pattern is `{<<a, b>> \in S \X T : P(a, b)}` where the cross-product domain
/// creates a SetPred with BoundPattern::Tuple. Before the fix, the lazy materialization
/// path used `bind_local` with the synthetic name "<<a, b>>" instead of destructuring
/// the tuple into individual variable bindings for `a` and `b`.
///
/// This test uses a Next action that filters a cross-product via set comprehension
/// with tuple destructuring, which triggers the lazy `SetPredValue` path.
#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_setpred_tuple_destructuring_in_lazy_materialization() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SetPredTupleDestructure ----
EXTENDS Integers
VARIABLE state

\* Cross-product domain with tuple destructuring.
\* {1,2} \X {10,20} = {<<1,10>>, <<1,20>>, <<2,10>>, <<2,20>>}
\* Filter: a + b > 11 -> {<<1,20>>, <<2,10>>, <<2,20>>}
ValidPairs == {<<a, b>> \in {1, 2} \X {10, 20} : a + b > 11}

Init == state = 0

\* Pick from the filtered set and store the sum
Next == \E p \in ValidPairs : state' = p[1] + p[2]

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
            // Init: state=0
            // ValidPairs = {<<1,20>>, <<2,10>>, <<2,20>>}
            // Sums: 21, 12, 22
            // States: {0, 21, 12, 22} = 4 states
            assert_eq!(
                stats.states_found, 4,
                "b3cf3ad regression: SetPred with tuple destructuring should find 4 states \
                 (state=0, 12, 21, 22). Before the fix, this would fail with \
                 'Undefined variable: a'. Found {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "b3cf3ad regression: SetPred with <<a, b>> tuple destructuring should not error. \
                 Before the fix, lazy materialization bound the synthetic name '<<a, b>>' instead \
                 of destructuring, causing 'Undefined variable' errors. Error: {error:?}"
            );
        }
        other => panic!("unexpected result: {other:?}"),
    }
}
