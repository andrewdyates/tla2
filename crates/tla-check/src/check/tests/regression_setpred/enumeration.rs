// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #1500: Seq(SetPred) membership fallback.
/// When Seq(S) where S is a SetPred, set_contains returns None and
/// the context-aware fallback must handle SeqSet membership correctly.
///
/// NOTE: The domain `{1, 2, 3}` is finite, so eval_set_filter eagerly evaluates
/// to a plain `Value::Set({2, 3})`. This tests the AST-level set-filter-in-Seq
/// pattern but does NOT exercise the runtime lazy SetPred path. For lazy SetPred
/// coverage, see tests using `SUBSET` domains (e.g., test_exists_over_subset_filter_domain_in_next).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1500_seq_of_setpred_membership() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE SeqSetPredMembership ----
EXTENDS Sequences
VARIABLE x
S == {v \in {1, 2, 3} : v > 1}
Init == x = <<2, 3>>
Next == x' \in {<<s>> : s \in S}
====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Errors: {:?}",
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
            // S = {2, 3}, so {<<s>> : s \in S} = {<<2>>, <<3>>}
            // Init: <<2,3>>. From <<2,3>>: reach <<2>>, <<3>>.
            // From <<2>>: reach <<2>>, <<3>> (already seen).
            // From <<3>>: reach <<2>>, <<3>> (already seen).
            // Total distinct states: <<2,3>>, <<2>>, <<3>> = 3
            assert_eq!(
                stats.states_found, 3,
                "#1500 regression: Seq(SetPred) membership should find exactly 3 states \
                 (<<2,3>>, <<2>>, <<3>>). Found {}",
                stats.states_found,
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("Seq(SetPred) membership should not raise eval errors: {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Regression test for #1500: UNION membership with indeterminate inner sets.
/// When UNION S contains SetPred inner sets, set_contains returns None and
/// the context-aware fallback must handle BigUnion membership correctly.
///
/// NOTE: Domains `{1, 2}` and `{3, 4}` are finite, so eval_set_filter eagerly
/// evaluates A to `Value::Set({1, 2})` and B to `Value::Set({3, 4})`. This tests
/// the AST-level set-filter-in-UNION pattern but does NOT exercise the runtime
/// lazy SetPred path. For lazy SetPred coverage, see tests using `SUBSET` domains.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_1500_union_setpred_membership() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE UnionSetPredMembership ----
VARIABLE x
A == {v \in {1, 2} : v > 0}
B == {v \in {3, 4} : v > 0}
Init == x = 1
Next == x' \in UNION {A, B}
====
"#;

    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "Errors: {:?}",
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
            // A = {1,2}, B = {3,4}, UNION {A,B} = {1,2,3,4}
            // Init: x=1. From x=1: reach x=1,2,3,4.
            // From x=2: reach x=1,2,3,4 (all seen). Same for x=3, x=4.
            // Total distinct states: {1, 2, 3, 4} = 4
            assert_eq!(
                stats.states_found, 4,
                "#1500 regression: UNION(SetPred) membership should find exactly 4 states \
                 (x=1,2,3,4). Found {}",
                stats.states_found,
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("UNION(SetPred) membership should not raise eval errors: {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Regression test for #1828/#1719: EXISTS with SetPred (set filter) domain in model checker.
///
/// When the Next action uses `\E x \in {y \in S : P(y)} : ...`, the enumerator must
/// materialize the SetPred to enumerate successors. Without proper handling,
/// `iter_set()` returns `None` for SetPred and the enumerator silently returns `Ok(())`
/// (zero successors), causing missing states.
///
/// This test uses a small finite set so the eager filter path should work.
/// TLC correctly enumerates all successors through this pattern.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_over_set_filter_domain_in_next() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Spec: variable x starts at 0, Next picks an even number from {1..4} and sets x to it
    // The set filter {n \in 1..4 : n % 2 = 0} produces a SetPred.
    // Expected: init state x=0, then x can be 2 or 4 -> 3 distinct states total
    let src = r#"
---- MODULE ExistsOverSetFilter ----
EXTENDS Integers
VARIABLE x

Init == x = 0

\* EXISTS over a set filter (SetPred domain)
Next == \E n \in {k \in 1..4 : k % 2 = 0} : x' = n

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
            // x=0 (init), x=2, x=4 -> 3 states
            assert_eq!(
                stats.states_found, 3,
                "EXISTS over set filter should find 3 states (x=0,2,4). \
                 If fewer, the enumerator is silently dropping the SetPred domain. \
                 Found {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "EXISTS over set filter domain should not error. \
                 If this errors with type_error or InitCannotEnumerate, \
                 the SetPred is not being materialized. Error: {error:?}"
            );
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Regression test for #1828: Init with set filter domain (SUBSET filter).
///
/// `selected \in {S \in SUBSET Procs : Cardinality(S) = 2}` creates a SetPred
/// because the domain is `SUBSET Procs`. The init constraint extractor must
/// handle this either eagerly or via deferred materialization.
///
/// This is the same pattern as test_symmetry_with_pairs but without symmetry,
/// isolating the SetPred enumeration issue.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_init_with_subset_filter_domain() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    // Small SUBSET: SUBSET {1,2,3} has 8 elements, filter to size-2 subsets -> 3 elements
    let src = r#"
---- MODULE InitSubsetFilter ----
EXTENDS Integers, FiniteSets
VARIABLE selected

Init == selected \in {S \in SUBSET {1, 2, 3} : Cardinality(S) = 2}
Next == UNCHANGED selected
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
            // {1,2}, {1,3}, {2,3} -> 3 initial states, UNCHANGED -> no new states
            assert_eq!(
                stats.states_found, 3,
                "Init with SUBSET filter should find 3 states. \
                 If 0, the SetPred domain cannot be enumerated. Found {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "Init with SUBSET filter domain should not error. \
                 InitCannotEnumerate means SetPred materialization is missing. \
                 Error: {error:?}"
            );
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Regression test for #1719/#1828: EXISTS over SUBSET-filter domain in Next action.
///
/// Unlike test_exists_over_set_filter_domain_in_next which uses `1..4` (eagerly
/// filtered to a regular Set), this test uses `SUBSET {1,2}` as the filter source.
/// `SUBSET` creates a `Value::Subset(_)` which triggers the lazy SetPred path
/// in eval_set_filter (line 343: `matches!(dv, Value::Subset(_))`).
/// The enumerator must then materialize the SetPred to find successors.
///
/// Expected: Init x={}, Next picks a non-empty subset -> {1}, {2}, {1,2} -> 4 states total
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_over_subset_filter_domain_in_next() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE ExistsOverSubsetFilter ----
EXTENDS Integers, FiniteSets
VARIABLE x

Init == x = {}

\* EXISTS over a SUBSET filter - this creates a SetPred because SUBSET triggers lazy path
Next == \E s \in {t \in SUBSET {1, 2} : Cardinality(t) > 0} : x' = s

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
            // x={} (init), x={1}, x={2}, x={1,2} -> 4 states
            assert_eq!(
                stats.states_found, 4,
                "EXISTS over SUBSET filter should find 4 states. \
                 If fewer, the enumerator silently drops the SetPred domain. Found {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!(
                "EXISTS over SUBSET filter domain should not error. \
                 If this errors, the SetPred is not being materialized in the enumerator. \
                 Error: {error:?}"
            );
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Regression test for proof_coverage audit: multi-variable symbolic assignment
/// where both variables come from SetPred domains.
///
/// This exercises the case where symbolic_assignments.rs must expand *multiple*
/// InSet assignments from SetPred domains. Each variable's domain must be
/// independently materialized, and the cross product of assignments must be correct.
///
/// Expected: Init (x={}, y={}), Next produces all combos of non-empty subsets -> states
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_multi_variable_setpred_symbolic_assignment() {
    use tla_core::{lower, parse_to_syntax_tree, FileId};

    let src = r#"
---- MODULE MultiVarSetPredAssign ----
EXTENDS Integers, FiniteSets
VARIABLES x, y

Init == x = {} /\ y = {}

\* Two independent SetPred domains in one EXISTS
Next == \E a \in {s \in SUBSET {1, 2} : Cardinality(s) = 1},
           b \in {s \in SUBSET {1, 2} : Cardinality(s) = 1} :
        x' = a /\ y' = b

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
            // Init: (x={}, y={})
            // Next: a in {{1},{2}}, b in {{1},{2}} -> 4 combos:
            //   (x={1},y={1}), (x={1},y={2}), (x={2},y={1}), (x={2},y={2})
            // Total: 1 init + 4 next = 5 states
            assert_eq!(
                stats.states_found, 5,
                "Multi-variable SetPred assignment should find 5 states (1 init + 4 combos). \
                 If fewer, one or both SetPred domains were silently dropped. Found {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("Multi-variable SetPred assignment should not error. Error: {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}
