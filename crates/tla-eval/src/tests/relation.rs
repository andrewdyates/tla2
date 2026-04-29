// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

fn assert_relation_cases(cases: &[(&str, bool)]) {
    for (expr, expected) in cases {
        assert_eq!(eval_str(expr).unwrap(), Value::Bool(*expected), "{expr}");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_relation_is_reflexive_under_equality() {
    assert_eq!(
        eval_str(r#"IsReflexiveUnder(=, {1, 2, 3})"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_relation_is_strictly_totally_ordered_under_lt() {
    assert_eq!(
        eval_str(r#"IsStrictlyTotallyOrderedUnder(<, {1, 2, 3})"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_relation_is_partially_ordered_under_user_defined_operator() {
    assert_eq!(
        eval_with_ops(
            "Leq(a, b) == a \\leq b",
            r#"IsPartiallyOrderedUnder(Leq, {1, 2, 3})"#,
        )
        .unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_relation_transitive_closure_returns_boolean_relation() {
    assert_eq!(
        eval_str(
            r#"LET S == {1, 2, 3}
               R == [x,y \in S |-> (x = 1 /\ y = 2) \/ (x = 2 /\ y = 3)]
               IN TransitiveClosure(R, S)
                    = [x,y \in S |-> (x = 1 /\ (y = 2 \/ y = 3)) \/ (x = 2 /\ y = 3)]"#,
        )
        .unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_relation_reflexive_transitive_closure_adds_identity_pairs() {
    assert_eq!(
        eval_str(
            r#"LET S == {1, 2, 3}
               R == [x,y \in S |-> (x = 1 /\ y = 2) \/ (x = 2 /\ y = 3)]
               IN ReflexiveTransitiveClosure(R, S)
                    = [x,y \in S |->
                         x = y
                         \/ (x = 1 /\ (y = 2 \/ y = 3))
                         \/ (x = 2 /\ y = 3)]"#,
        )
        .unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_relation_is_connected_uses_reflexive_transitive_reachability() {
    assert_eq!(
        eval_str(
            r#"LET S == {1, 2, 3}
               R == [x,y \in S |->
                        <<x, y>> \in {<<1, 2>>, <<2, 1>>, <<2, 3>>, <<3, 2>>}]
               IN IsConnected(R, S)"#,
        )
        .unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_relation_direct_relation_requires_boolean_entries() {
    let err = eval_str(r#"LET S == {1} IN IsReflexive([x,y \in S |-> 1], S)"#).unwrap_err();
    assert!(matches!(
        err,
        EvalError::TypeError {
            expected: "BOOLEAN",
            ..
        }
    ));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_relation_direct_predicates_cover_true_and_false_cases() {
    assert_relation_cases(&[
        (
            r#"LET S == {1, 2, 3} IN IsReflexive([x,y \in S |-> x = y], S)"#,
            true,
        ),
        (
            r#"LET S == {1, 2, 3} IN IsIrreflexive([x,y \in S |-> x < y], S)"#,
            true,
        ),
        (
            r#"LET S == {1, 2, 3}
               IN IsSymmetric(
                    [x,y \in S |-> <<x, y>> \in {<<1, 2>>, <<2, 1>>, <<3, 3>>}],
                    S
                  )"#,
            true,
        ),
        (
            r#"LET S == {1, 2, 3} IN IsAntiSymmetric([x,y \in S |-> x \leq y], S)"#,
            true,
        ),
        (
            r#"LET S == {1, 2, 3} IN IsAsymmetric([x,y \in S |-> x < y], S)"#,
            true,
        ),
        (
            r#"LET S == {1, 2, 3} IN IsTransitive([x,y \in S |-> x \leq y], S)"#,
            true,
        ),
        (
            r#"LET S == {1, 2, 3}
               IN IsStrictlyPartiallyOrdered([x,y \in S |-> x < y], S)"#,
            true,
        ),
        (
            r#"LET S == {1, 2, 3} IN IsPartiallyOrdered([x,y \in S |-> x \leq y], S)"#,
            true,
        ),
        (
            r#"LET S == {1, 2, 3}
               IN IsStrictlyTotallyOrdered([x,y \in S |-> x < y], S)"#,
            true,
        ),
        (
            r#"LET S == {1, 2, 3} IN IsTotallyOrdered([x,y \in S |-> x \leq y], S)"#,
            true,
        ),
        (
            r#"LET S == {1, 2, 3} IN IsIrreflexive([x,y \in S |-> x = y], S)"#,
            false,
        ),
        (
            r#"LET S == {1, 2, 3}
               IN IsSymmetric([x,y \in S |-> <<x, y>> = <<1, 2>>], S)"#,
            false,
        ),
        (
            r#"LET S == {1, 2, 3}
               IN IsAntiSymmetric(
                    [x,y \in S |-> <<x, y>> \in {<<1, 2>>, <<2, 1>>}],
                    S
                  )"#,
            false,
        ),
        (
            r#"LET S == {1, 2, 3} IN IsAsymmetric([x,y \in S |-> x = y], S)"#,
            false,
        ),
        (
            r#"LET S == {1, 2, 3}
               IN IsTransitive(
                    [x,y \in S |-> <<x, y>> \in {<<1, 2>>, <<2, 3>>}],
                    S
                  )"#,
            false,
        ),
        (
            r#"LET S == {1, 2, 3}
               IN IsStrictlyPartiallyOrdered([x,y \in S |-> x \leq y], S)"#,
            false,
        ),
        (
            r#"LET S == {1, 2, 3} IN IsPartiallyOrdered([x,y \in S |-> x < y], S)"#,
            false,
        ),
        (
            r#"LET S == {1, 2, 3}
               IN IsStrictlyTotallyOrdered(
                    [x,y \in S |-> <<x, y>> = <<1, 2>>],
                    S
                  )"#,
            false,
        ),
        (
            r#"LET S == {1, 2, 3} IN IsTotallyOrdered([x,y \in S |-> x = y], S)"#,
            false,
        ),
    ]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_relation_under_predicates_cover_remaining_operators() {
    assert_relation_cases(&[
        (r#"IsIrreflexiveUnder(<, {1, 2, 3})"#, true),
        (r#"IsSymmetricUnder(=, {1, 2, 3})"#, true),
        (r#"IsAntiSymmetricUnder(\leq, {1, 2, 3})"#, true),
        (r#"IsAsymmetricUnder(<, {1, 2, 3})"#, true),
        (r#"IsTransitiveUnder(<, {1, 2, 3})"#, true),
        (r#"IsStrictlyPartiallyOrderedUnder(<, {1, 2, 3})"#, true),
        (r#"IsTotallyOrderedUnder(\leq, {1, 2, 3})"#, true),
        (r#"IsSymmetricUnder(<, {1, 2, 3})"#, false),
        (r#"IsTransitiveUnder(#, {1, 2, 3})"#, false),
        (r#"IsTransitiveUnder(/=, {1, 2, 3})"#, false),
        (r#"IsTotallyOrderedUnder(=, {1, 2, 3})"#, false),
    ]);
}
