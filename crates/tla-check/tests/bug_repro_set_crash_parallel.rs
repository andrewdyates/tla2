// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Set membership, crash, parallel - Bugs #1483, #744, #773, #731
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::assert_eval_error_set_too_large;
use common::parse_module;
use tla_check::{check_module, check_module_parallel, CheckResult, Config};

// ============================================================================
// Bug #1483: SetCup/SetDiff treat SetPred membership as false
// ============================================================================

/// Bug #1483: `{1} \cup {n \in Nat : n > 1}` contains 2, but SetCupValue
/// collapses the SetPred's indeterminate membership to `false`.
///
/// TLC baseline: `InvCup` and `InvDiffExpected` both pass (no invariant violation).
/// TLA2 before fix: false invariant violation because `2 \in ({1} \cup SetPred)` returned false.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1483_setcup_with_setpred_membership() {
    let spec = r#"
---- MODULE SetCupPred ----
EXTENDS Naturals
VARIABLE x

Init == x = 0
Next == x' = x

InvCup == (x = 0) => (2 \in ({1} \cup {n \in Nat : n > 1}))
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InvCup".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "expected 1 state, got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("InvCup should pass (2 is in {{1}} \\cup {{n in Nat : n > 1}}), but got error: {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

/// Bug #1483: `{1, 2, 3} \ {n \in Nat : n > 1}` should equal `{1}`,
/// so `2 \notin ({1, 2, 3} \ {n \in Nat : n > 1})` should be true.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_1483_setdiff_with_setpred_membership() {
    let spec = r#"
---- MODULE SetDiffPred ----
EXTENDS Naturals
VARIABLE x

Init == x = 0
Next == x' = x

InvDiff == (x = 0) => ~(2 \in ({1, 2, 3} \ {n \in Nat : n > 1}))
====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["InvDiff".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);
    match result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 1,
                "expected 1 state, got {}",
                stats.states_found
            );
        }
        CheckResult::Error { error, .. } => {
            panic!("InvDiff should pass (2 is NOT in {{1,2,3}} \\ {{n in Nat : n > 1}}), but got error: {error:?}");
        }
        other => panic!("unexpected result: {other:?}"),
    }
}

// ============================================================================
// Crash #744: Seq(Nat) = Seq(Nat) panics in Value total ordering
// ============================================================================

/// Crash #744: `Seq(Nat) = Seq(Nat)` must not panic.
///
/// Repro from #744:
/// - Invariant `Inv == Seq(Nat) = Seq(Nat)`
/// - Model checking used to panic with: `unreachable!("type_order ensures same types")`
///
/// TLC baseline:
/// - Completes successfully
/// - `1 distinct states found`
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_crash_seq_nat_equality_does_not_panic() {
    let spec = r#"
---- MODULE SeqNatEquality ----
EXTENDS Naturals, Sequences
VARIABLE x
Init == x = 0
Next == x' = x
Inv == Seq(Nat) = Seq(Nat)
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
                stats.states_found, 1,
                "SeqNatEquality: expected 1 distinct state (TLC baseline), got {}",
                stats.states_found
            );
            assert_eq!(
                stats.initial_states, 1,
                "SeqNatEquality: expected 1 initial state, got {}",
                stats.initial_states
            );
        }
        other => {
            panic!("Unexpected result: {:?}", other);
        }
    }
}

// ============================================================================
// Bug #773: Parallel checker must propagate invariant evaluation errors
// ============================================================================

/// Bug #773: Invariant evaluation errors must not be coerced into violations.
///
/// TLC semantics: if invariant evaluation triggers an evaluation error (e.g., forcing enumeration
/// or cardinality computation for an infinite/non-enumerable set), model checking reports an error.
/// The parallel checker must match sequential behavior.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_parallel_invariant_eval_errors_propagate() {
    let cases = [
        (
            "SubsetNatEmptyEquality",
            r#"
---- MODULE SubsetNatEmptyEquality ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
Inv == SUBSET Nat = {}
====
"#,
        ),
        (
            "FuncSetEmptyEquality",
            r#"
---- MODULE FuncSetEmptyEquality ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x
Inv == [Nat -> Nat] = {}
====
"#,
        ),
    ];

    for (name, spec) in cases {
        let module = parse_module(spec);
        let config = Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            invariants: vec!["Inv".to_string()],
            ..Default::default()
        };

        let seq = check_module(&module, &config);
        assert_eval_error_set_too_large(name, "sequential", seq);

        let par = check_module_parallel(&module, &config, 2);
        assert_eval_error_set_too_large(name, "parallel", par);
    }
}

/// Seq({}) is the singleton set containing the empty sequence.
///
/// TLC baseline:
/// - `Seq({}) = {<<>>}` evaluates to TRUE
/// - Model checking completes with `1 distinct states found`
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_seq_empty_set_equals_singleton_empty_sequence() {
    let spec = r#"
---- MODULE SeqEmptyEquality ----
EXTENDS Sequences
VARIABLE x
Init == x = 0
Next == x' = x
Inv == Seq({}) = {<<>>}
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
                stats.states_found, 1,
                "SeqEmptyEquality: expected 1 distinct state (TLC baseline), got {}",
                stats.states_found
            );
        }
        other => {
            panic!("Unexpected result: {:?}", other);
        }
    }
}

// ============================================================================
// Bug #731: kafka2_core false positive TypeInvariant violation (Seq(record) membership)
// ============================================================================

/// Bug #731: kafka2_core-style TypeInvariant must not produce false positives.
///
/// Repro pattern from #731 (simplified):
/// - record type with a `key` field: `Seq(Nat) \cup {<<>>}`
/// - a sequence of those records: `msgs \in Seq(MessageType)`
/// - invariants should hold for all reachable states
///
/// TLC baseline:
/// - completes with no error.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_kafka2_typeinvariant_seq_record_membership() {
    let spec = r#"
---- MODULE Kafka2TypeInvariantRepro ----
EXTENDS Naturals, Sequences

MessageType == [key: Seq(Nat) \cup {<<>>}]

Keys == {<<>>, <<0>>, <<0, 1>>}

VARIABLE msgs

Init == msgs = << [key |-> <<>>] >>

Next ==
    \E k \in Keys:
        msgs' = << [key |-> k] >>

TypeInvariant == msgs \in Seq(MessageType)

====
"#;

    // Part of #758: stack overflow coverage for this pattern is in
    // `crates/tla-check/tests/seq_record_membership_stack.rs` (subprocess-based to avoid
    // hard-aborting the full suite on regression).
    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeInvariant".to_string()],
        ..Default::default()
    };
    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(stats) => {
            assert_eq!(
                stats.states_found, 3,
                "Kafka2TypeInvariantRepro: expected 3 distinct states (one per key), got {}",
                stats.states_found
            );
            assert_eq!(
                stats.transitions, 9,
                "Kafka2TypeInvariantRepro: expected 9 transitions (3 states * 3 successors), got {}",
                stats.transitions
            );
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #731 regression: invariant {} violated (should hold for all reachable states)",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Variant: Prime guard directly in Next (baseline - should always work)
///
/// This test verifies that inline prime guards work correctly.
/// The bug only affected prime guards inside operator bodies.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inline_prime_guard_works() {
    let spec = r#"
---- MODULE InlinePrimeGuard ----
VARIABLE x

NoSelfLoop == \A pair \in x : pair[1] # pair[2]

Init == x = {}

\* Prime guard is inline in Next, not inside an operator
Next ==
    /\ x' \in SUBSET({<<1, 1>>, <<1, 2>>, <<2, 1>>})
    /\ NoSelfLoop'

NoSelfLoopInvariant == \A pair \in x : pair[1] # pair[2]

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["NoSelfLoopInvariant".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success { .. } => {
            // Expected: inline prime guards should work
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Inline prime guard failed! Invariant {} violated",
                invariant
            );
        }
        _ => {
            panic!("Unexpected result: {:?}", result);
        }
    }
}
