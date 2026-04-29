// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Set/interval operations - Bug #179 MCQuicksort
//!
//! Split from bug_reproductions.rs — Part of #2850

mod common;

use common::parse_module;
use tla_check::{check_module, CheckResult, Config, ConstantValue};

// ============================================================================
// Bug #179: MCQuicksort - Seq(S) \ {<<>>} SetDiff membership bug
// ============================================================================

/// Bug #179: SetDiff membership fails for SeqSet \ Set
///
/// The MCQuicksort spec uses `seq \in Seq(Values) \ {<<>>}` in TypeOK.
/// This should check that seq is:
/// 1. A valid sequence over Values, AND
/// 2. Not the empty sequence
///
/// The bug: When LHS is SeqSet (non-enumerable) and RHS is a Set,
/// SetDiff::contains returns false even when the element should be in.
///
/// Investigation status:
/// - `seq \in Seq(Values)` works correctly
/// - `seq \in Seq(Values) \ {<<>>}` fails incorrectly
/// - The SetDiff logic appears correct, but something in the membership
///   check chain is failing
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_179_seqset_setdiff_membership() {
    let spec = r#"
---- MODULE SeqSetDiffBug179 ----
EXTENDS Integers, Sequences

CONSTANT Values

VARIABLE seq

\* TypeOK0: seq is in Seq(Values) - works
TypeOK0 == seq \in Seq(Values)

\* TypeOK1: seq is in Seq(Values) \ {<<>>} - fails incorrectly
TypeOK1 == seq \in Seq(Values) \ {<<>>}

Init == seq = <<1, 1, 1, 1>>

Next == UNCHANGED seq

====
"#;

    let module = parse_module(spec);
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK1".to_string()],
        ..Default::default()
    };
    config.constants.insert(
        "Values".to_string(),
        ConstantValue::Value("{1}".to_string()),
    );

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(_) => {
            // Expected: TypeOK1 should pass - <<1,1,1,1>> is in Seq({1}) \ {<<>>}
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #179 exists! Invariant {} violated - SetDiff membership for SeqSet is broken",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

// ============================================================================
// Bug #179 Part 2: Interval vs Set equality in SUBSET membership
// ============================================================================

/// Bug #179: Interval (1..1) should equal Set ({1}) in SUBSET membership
///
/// In TLA+, 1..1 = {1} (an interval IS the set of integers it contains).
/// When checking U \in SUBSET(SUBSET(S)), where U contains intervals,
/// TLA2 must recognize that:
/// - 1..1 semantically equals {1}
/// - {1} \in SUBSET(S) should pass when 1 \in S
///
/// This test verifies interval/set semantic equality in nested SUBSET checks.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_179_interval_vs_set_equality() {
    let spec = r#"
---- MODULE IntervalSetEquality179 ----
EXTENDS Integers

VARIABLE U

\* TypeOK: U is a set of non-empty subsets of 1..4
\* Using nested SUBSET pattern from MCQuicksort
TypeOK == U \in SUBSET ( (SUBSET (1..4)) \ {{}} )

\* Init: U contains the singleton interval 1..1 (which equals {1})
Init == U = {1..1}

Next == UNCHANGED U

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(_) => {
            // Expected: TypeOK should pass
            // {1..1} = {{1}} which is a valid element of SUBSET((SUBSET(1..4)) \ {{}})
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #179 exists! Invariant {} violated - Interval 1..1 not recognized as equal to {{1}}",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Bug #179: More precise test - interval in SetDiff of powerset
///
/// This tests exactly the MCQuicksort scenario:
/// - U transitions from {1..4} to {1..1, 2..4}
/// - Each element of U must be in (SUBSET(1..4)) \ {{}}
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_179_interval_in_setdiff_powerset() {
    let spec = r#"
---- MODULE IntervalSetDiffBug179 ----
EXTENDS Integers

VARIABLE U

\* The exact MCQuicksort pattern: U is a set of non-empty subsets
TypeOK == U \in SUBSET ( (SUBSET (1..4)) \ {{}} )

\* Init with two intervals - the failing state from MCQuicksort
Init == U = {1..1, 2..4}

Next == UNCHANGED U

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(_) => {
            // Expected: TypeOK should pass
            // U = {{1}, {2,3,4}} (intervals as sets) is a valid subset
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #179: {} violated - Intervals {{1..1, 2..4}} not recognized as subsets in SUBSET((SUBSET(1..4)) \\ {{{{}}}})",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Bug #179: Explicit set of FuncSets (not set comprehension)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_179_tuple_in_explicit_set_of_funcsets() {
    let spec = r#"
---- MODULE TupleInExplicitSetFuncSets179 ----
EXTENDS Integers

CONSTANT Values

VARIABLE seq

\* Explicit set of FuncSets (no comprehension)
TypeOK == seq \in UNION {[1..1 -> Values], [1..2 -> Values], [1..3 -> Values], [1..4 -> Values]}

Init == seq = <<1, 1, 1, 1>>

Next == UNCHANGED seq

====
"#;

    let module = parse_module(spec);
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };
    config.constants.insert(
        "Values".to_string(),
        ConstantValue::Value("{1, 2, 3}".to_string()),
    );

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(_) => {
            // Good - explicit set of FuncSets works
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #179 (explicit set): {} violated - Tuple not in UNION of explicit FuncSets",
                invariant
            );
        }
        other => panic!("Unexpected result (explicit set): {:?}", other),
    }
}

/// Bug #179: Simplest case - Tuple in single FuncSet
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_179_tuple_in_single_funcset() {
    let spec = r#"
---- MODULE TupleInSingleFuncSet179 ----
EXTENDS Integers

CONSTANT Values

VARIABLE seq

\* Direct FuncSet membership
TypeOK == seq \in [1..4 -> Values]

Init == seq = <<1, 1, 1, 1>>

Next == UNCHANGED seq

====
"#;

    let module = parse_module(spec);
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };
    config.constants.insert(
        "Values".to_string(),
        ConstantValue::Value("{1, 2, 3}".to_string()),
    );

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(_) => {
            // Good - direct FuncSet membership works
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #179 (single FuncSet): {} violated - Tuple <<1,1,1,1>> not in [1..4 -> {{1,2,3}}]",
                invariant
            );
        }
        other => panic!("Unexpected result (single FuncSet): {:?}", other),
    }
}

/// Bug #179: Tuple vs Function equality in LimitedSeq membership
///
/// MCQuicksort redefines Seq <- LimitedSeq where:
///   LimitedSeq(S) == UNION {[1 .. n -> S] : n \in 1 .. MaxSeqLen}
///
/// This produces FUNCTIONS like [1 |-> 1, 2 |-> 1, ...], not tuples.
/// But during evaluation, sequences may be represented as tuples <<1, 1, ...>>.
///
/// TLA+ semantics: <<1, 1, 1, 1>> = [1 |-> 1, 2 |-> 1, 3 |-> 1, 4 |-> 1]
/// So tuple should be IN LimitedSeq even though LimitedSeq contains functions.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_179_tuple_in_function_set() {
    // First test: Without SetDiff (UNION only)
    let spec_union_only = r#"
---- MODULE TupleInUnionBug179 ----
EXTENDS Integers

CONSTANT Values

\* LimitedSeq from MCQuicksort - produces FUNCTIONS
LimitedSeq(S) == UNION {[1 .. n -> S] : n \in 1 .. 4}

VARIABLE seq

\* Test without the SetDiff - just UNION membership
TypeOK == seq \in LimitedSeq(Values)

\* Init with a TUPLE (not a function)
Init == seq = <<1, 1, 1, 1>>

Next == UNCHANGED seq

====
"#;

    let module = parse_module(spec_union_only);
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };
    config.constants.insert(
        "Values".to_string(),
        ConstantValue::Value("{1, 2, 3}".to_string()),
    );

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(_) => {
            // Good - UNION membership works
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #179 (UNION only): {} violated - Tuple not recognized in UNION of function sets",
                invariant
            );
        }
        other => panic!("Unexpected result (UNION only): {:?}", other),
    }

    // Second test: With SetDiff
    let spec = r#"
---- MODULE TupleInFuncSetBug179 ----
EXTENDS Integers

CONSTANT Values

\* LimitedSeq from MCQuicksort - produces FUNCTIONS
LimitedSeq(S) == UNION {[1 .. n -> S] : n \in 1 .. 4}

VARIABLE seq

\* Tuple should be semantically equal to corresponding function
TypeOK == seq \in LimitedSeq(Values) \ {<<>>}

\* Init with a TUPLE (not a function)
Init == seq = <<1, 1, 1, 1>>

Next == UNCHANGED seq

====
"#;

    let module = parse_module(spec);
    let mut config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };
    config.constants.insert(
        "Values".to_string(),
        ConstantValue::Value("{1, 2, 3}".to_string()),
    );

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(_) => {
            // Expected: TypeOK should pass
            // <<1, 1, 1, 1>> should be recognized as equal to [1 |-> 1, ...]
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #179: {} violated - Tuple not recognized as equal to function in LimitedSeq \\ {{<<>>}}",
                invariant
            );
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}

/// Bug #179: Dynamic interval creation via LET expressions
///
/// This mimics the MCQuicksort action where intervals are created via:
///   LET I1 == Min(I)..p IN LET I2 == (p+1)..Max(I) IN ...
///
/// Result: This test PASSES (TypeOK holds through all states).
/// The bug in MCQuicksort must have a different root cause.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bug_179_dynamic_interval_creation() {
    let spec = r#"
---- MODULE DynamicIntervalBug179 ----
EXTENDS Integers, FiniteSets

VARIABLE U, seq0

Min(S) == CHOOSE x \in S : \A y \in S : x =< y
Max(S) == CHOOSE x \in S : \A y \in S : y =< x

TypeOK == /\ U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )

Init == /\ U = {1..4}
        /\ seq0 = <<1, 1, 1, 1>>

\* Mimics the MCQuicksort action exactly
Action == /\ U # {}
          /\ \E I \in U:
               IF Cardinality(I) = 1
               THEN U' = U \ {I}
               ELSE \E p \in Min(I) .. (Max(I)-1):
                      LET I1 == Min(I)..p IN
                      LET I2 == (p+1)..Max(I) IN
                      U' = ((U \ {I}) \cup {I1, I2})
          /\ seq0' = seq0

\* Allow stuttering when done (prevents deadlock)
Done == U = {} /\ UNCHANGED <<U, seq0>>

Next == Action \/ Done

====
"#;

    let module = parse_module(spec);
    let config = Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        invariants: vec!["TypeOK".to_string()],
        ..Default::default()
    };

    let result = check_module(&module, &config);

    match &result {
        CheckResult::Success(_) => {
            // Expected: TypeOK should pass in all states
            // Each transition creates valid intervals that are subsets of 1..4
        }
        CheckResult::InvariantViolation { invariant, .. } => {
            panic!(
                "Bug #179: {} violated - Dynamic interval creation via LET not recognized correctly",
                invariant
            );
        }
        CheckResult::Deadlock { .. } => {
            // Should not happen with Done action
            panic!("Unexpected deadlock");
        }
        other => panic!("Unexpected result: {:?}", other),
    }
}
