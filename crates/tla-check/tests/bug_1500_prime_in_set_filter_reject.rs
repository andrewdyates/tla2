// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod common;

use tla_check::{CheckResult, Config, ModelChecker};

/// Regression coverage for #1500: bound PrimeInSet Seq(SetPred) accepts members.
///
/// Asserts transitions=1 so this fails if `x' \in Seq(...)` is mistakenly treated
/// as disabled while still returning Success with one distinct state.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1500_prime_in_set_seqset_filter_accepts_member() {
    let src = r#"
---- MODULE PrimeInSetSeqPredAccept ----
EXTENDS Integers, Sequences
VARIABLE x

Init == x = <<1, 2>>
Next == x' = <<1, 2>> /\ x' \in Seq({n \in {1, 2, 3} : n > 0})
====
"#;

    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "Expected one distinct self-loop state"
            );
            assert_eq!(
                stats.transitions, 1,
                "PrimeInSet SeqSet filter should accept <<1,2>> and emit one transition"
            );
        }
        other => panic!("PrimeInSet SeqSet filter should accept member without error: {other:?}"),
    }
}

/// Regression coverage for #1500: bound PrimeInSet UNION(SetPred,...) accepts members.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1500_prime_in_set_union_filter_accepts_member() {
    let src = r#"
---- MODULE PrimeInSetUnionPredAccept ----
EXTENDS Integers
VARIABLE x

Init == x = 2
Next == x' = 2 /\ x' \in UNION {{n \in {1, 2, 3} : n > 1}, {10}}
====
"#;

    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "Expected one distinct self-loop state"
            );
            assert_eq!(
                stats.transitions, 1,
                "PrimeInSet UNION filter should accept 2 and emit one transition"
            );
        }
        other => panic!("PrimeInSet UNION filter should accept member without error: {other:?}"),
    }
}

/// Regression coverage for #1500: PrimeInSet filter path must reject bound
/// values not in Seq(SetPred), without raising a TypeError.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1500_prime_in_set_seqset_filter_rejects_non_member() {
    let src = r#"
---- MODULE PrimeInSetSeqPredReject ----
EXTENDS Integers, Sequences
VARIABLE x

Init == x = <<1, 2>>
Next == x' = <<0, 1>> /\ x' \in Seq({n \in {1, 2, 3} : n > 0})
====
"#;

    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "PrimeInSet SeqSet filter should reject <<0,1>> and produce no successor state"
            );
            assert_eq!(
                stats.transitions, 0,
                "PrimeInSet SeqSet reject case should emit no transitions"
            );
        }
        other => {
            panic!("PrimeInSet SeqSet filter should reject non-member without error: {other:?}")
        }
    }
}

/// Regression coverage for #1500: PrimeInSet filter path must reject bound
/// values not in UNION(SetPred,...), without raising a TypeError.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1500_prime_in_set_union_filter_rejects_non_member() {
    let src = r#"
---- MODULE PrimeInSetUnionPredReject ----
EXTENDS Integers
VARIABLE x

Init == x = 2
Next == x' = 5 /\ x' \in UNION {{n \in {1, 2, 3} : n > 1}, {10}}
====
"#;

    let module = common::parse_module(src);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    };

    let mut checker = ModelChecker::new(&module, &config);
    checker.set_deadlock_check(false);

    match checker.check() {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "PrimeInSet UNION filter should reject 5 and produce no successor state"
            );
            assert_eq!(
                stats.transitions, 0,
                "PrimeInSet UNION reject case should emit no transitions"
            );
        }
        other => {
            panic!("PrimeInSet UNION filter should reject non-member without error: {other:?}")
        }
    }
}
