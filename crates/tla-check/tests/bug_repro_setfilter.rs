// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SetFilter desugaring - Issue #618
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::parse_module;
use std::collections::HashMap;
use tla_check::{check_module, CheckResult, Config, ConstantValue};

// ============================================================================
// SetFilter Desugaring Tests (#618)
// ============================================================================

/// Part of #618: Basic SetFilter desugaring test
///
/// Verifies that \A x \in {y \in S : P(y)} : Q(x) is correctly desugared to
/// \A x \in S : (P(x) => Q(x))
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setfilter_desugaring_basic() {
    let spec = r#"
---- MODULE SetFilterDesugarBasic ----
EXTENDS Integers

VARIABLE x

Init == x = 0
Next == x' = IF x < 3 THEN x + 1 ELSE x

\* SetFilter: elements > 2 from 1..5 = {3, 4, 5}
\* Invariant: all elements in the filtered set are >= 3
InvFilteredSet == \A n \in {m \in 1..5 : m > 2} : n >= 3
InvDesugared == \A n \in 1..5 : (n > 2 => n >= 3)

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InvFilteredSet".to_string(), "InvDesugared".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 4,
                "Expected 4 states (x=0,1,2,3), got {}",
                stats.states_found
            );
        }
        other => panic!("SetFilter desugaring basic test failed: {:?}", other),
    }
}

/// Part of #618: SetFilter with different bound variable names
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setfilter_desugaring_var_substitution() {
    let spec = r#"
---- MODULE SetFilterDesugarVarSubst ----
EXTENDS Integers

VARIABLE v

Init == v = 0
Next == v' = IF v < 2 THEN v + 1 ELSE v

\* Filter uses 'y', quantifier uses 'x' - requires substitution
InvWithSubstitution == \A x \in {y \in 1..4 : y > 1} : x <= 4
InvSameName == \A y \in {y \in 1..4 : y > 1} : y <= 4

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InvWithSubstitution".to_string(), "InvSameName".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "Expected 3 states (v=0,1,2), got {}",
                stats.states_found
            );
        }
        other => panic!("SetFilter variable substitution test failed: {:?}", other),
    }
}

/// Part of #618: SetFilter via operator reference (like btree's Leaves)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setfilter_desugaring_operator_reference() {
    let spec = r#"
---- MODULE SetFilterDesugarOpRef ----
EXTENDS Integers

CONSTANT MaxNode
VARIABLE isLeaf

Nodes == 1..MaxNode
Leaves == {n \in Nodes : isLeaf[n]}

Init == isLeaf = [n \in Nodes |-> n > (MaxNode \div 2)]
Next == UNCHANGED isLeaf

InvAllLeaves == \A n \in Leaves : n > 0
InvLeafCheck == \A n \in Leaves : isLeaf[n]

====
"#;

    let module = parse_module(spec);
    let mut constants = HashMap::new();
    constants.insert("MaxNode".to_string(), ConstantValue::Value("4".to_string()));
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InvAllLeaves".to_string(), "InvLeafCheck".to_string()],
        constants,
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "Expected 1 state, got {}",
                stats.states_found
            );
        }
        other => panic!("SetFilter operator reference test failed: {:?}", other),
    }
}

/// Part of #618: SetFilter with EXISTS (audit finding - was missing)
///
/// Verifies that \E x \in {y \in S : P(y)} : Q(x) is correctly desugared to
/// \E x \in S : (P(x) /\ Q(x))
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setfilter_desugaring_exists() {
    let spec = r#"
---- MODULE SetFilterDesugarExists ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == x' = IF x < 5 THEN x + 1 ELSE x

\* EXISTS over SetFilter
\* {n \in 1..10 : n > 5} = {6, 7, 8, 9, 10}
\* \E n \in {m \in 1..10 : m > 5} : n = 7 should be TRUE
InvExistsInFilter == \E n \in {m \in 1..10 : m > 5} : n = 7

\* Desugared form (for comparison)
\* \E n \in 1..10 : (n > 5 /\ n = 7)
InvExistsDesugared == \E n \in 1..10 : (n > 5 /\ n = 7)

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec![
            "InvExistsInFilter".to_string(),
            "InvExistsDesugared".to_string(),
        ],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 6,
                "Expected 6 states (x=0..5), got {}",
                stats.states_found
            );
        }
        other => panic!("SetFilter EXISTS desugaring test failed: {:?}", other),
    }
}

/// Part of #618: SetFilter with empty result (filter excludes all elements)
///
/// Tests edge case where the filter predicate excludes all elements.
/// \A x \in {} : P(x) should be vacuously TRUE.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_setfilter_desugaring_empty_result() {
    let spec = r#"
---- MODULE SetFilterDesugarEmpty ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == x' = IF x < 2 THEN x + 1 ELSE x

\* Filter that excludes all elements: {n \in 1..5 : n > 100} = {}
\* \A n \in {} : P(n) should be TRUE (vacuously)
InvEmptyForall == \A n \in {m \in 1..5 : m > 100} : n < 0

\* \E n \in {} : P(n) should be FALSE
InvEmptyExists == ~(\E n \in {m \in 1..5 : m > 100} : n > 0)

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InvEmptyForall".to_string(), "InvEmptyExists".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "Expected 3 states (x=0,1,2), got {}",
                stats.states_found
            );
        }
        other => panic!("SetFilter empty result test failed: {:?}", other),
    }
}
