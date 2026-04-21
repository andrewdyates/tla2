// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Edge case tests for `eval_membership` and set operations.

use super::eval_str;
use crate::error::EvalError;
use crate::Value;

// --- Basic membership ---

#[test]
fn test_membership_in_empty_set() {
    let v = eval_str("1 \\in {}").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_membership_in_singleton() {
    let v = eval_str("1 \\in {1}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_not_in_operator() {
    let v = eval_str("4 \\notin {1, 2, 3}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

// --- Membership with mixed types ---

#[test]
fn test_membership_string_in_set() {
    let v = eval_str("\"a\" \\in {\"a\", \"b\", \"c\"}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_membership_boolean_in_set() {
    let v = eval_str("TRUE \\in {TRUE, FALSE}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_membership_tuple_in_set() {
    let v = eval_str("<<1, 2>> \\in {<<1, 2>>, <<3, 4>>}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_membership_tuple_not_in_set() {
    let v = eval_str("<<1, 3>> \\in {<<1, 2>>, <<3, 4>>}").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// --- Subset operations ---

#[test]
fn test_subseteq_empty_set() {
    // Empty set is subset of everything
    let v = eval_str("{} \\subseteq {1, 2, 3}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_subseteq_same_set() {
    let v = eval_str("{1, 2} \\subseteq {1, 2}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_subseteq_proper_subset() {
    let v = eval_str("{1} \\subseteq {1, 2}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_subseteq_not_subset() {
    let v = eval_str("{1, 3} \\subseteq {1, 2}").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// --- Set operations edge cases ---

#[test]
fn test_union_with_empty() {
    let v = eval_str("{1, 2} \\union {} = {1, 2}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_intersect_with_empty() {
    let v = eval_str("{1, 2} \\intersect {} = {}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_set_minus_empty() {
    let v = eval_str("{1, 2, 3} \\ {} = {1, 2, 3}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_set_minus_self() {
    let v = eval_str("{1, 2, 3} \\ {1, 2, 3} = {}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

// --- Membership in intervals ---

#[test]
fn test_membership_in_interval() {
    let v = eval_str("3 \\in 1..5").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_membership_not_in_interval() {
    let v = eval_str("6 \\in 1..5").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_membership_in_empty_interval() {
    // 5..1 is an empty interval
    let v = eval_str("3 \\in 5..1").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// --- Membership in set filter ---

#[test]
fn test_membership_in_set_filter() {
    let v = eval_str("4 \\in {x \\in 1..10 : x % 2 = 0}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_membership_not_in_set_filter() {
    let v = eval_str("3 \\in {x \\in 1..10 : x % 2 = 0}").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// --- Membership in DOMAIN ---

#[test]
fn test_domain_of_function() {
    let v = eval_str("\"a\" \\in DOMAIN [a |-> 1, b |-> 2]").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_domain_of_sequence() {
    // DOMAIN of a sequence <<a,b,c>> is 1..3
    let v = eval_str("2 \\in DOMAIN <<\"a\", \"b\", \"c\">>").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_domain_out_of_bounds() {
    let v = eval_str("4 \\in DOMAIN <<\"a\", \"b\", \"c\">>").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// --- Nested set membership ---

#[test]
fn test_nested_set_membership() {
    let v = eval_str("{1, 2} \\in {{1, 2}, {3, 4}}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_deeply_nested_set() {
    let v = eval_str("{{1}} \\in {{{1}}, {{2}}}").unwrap();
    assert_eq!(v, Value::Bool(true));
}

// --- DOMAIN coverage: IntFunc, empty collections, records ---

#[test]
fn test_domain_of_intfunc_non_unit_start() {
    // [i \in 2..5 |-> i * 10] creates an IntFunc with domain 2..5
    let v = eval_str("DOMAIN [i \\in 2..5 |-> i * 10]").unwrap();
    let expected = eval_str("2..5").unwrap();
    assert_eq!(
        v, expected,
        "DOMAIN of IntFunc 2..5 should equal the interval 2..5"
    );
}

#[test]
fn test_domain_of_intfunc_membership() {
    let v = eval_str("3 \\in DOMAIN [i \\in 2..5 |-> i * 10]").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_domain_of_intfunc_non_member() {
    let v = eval_str("1 \\in DOMAIN [i \\in 2..5 |-> i * 10]").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_domain_of_empty_sequence() {
    // SubSeq(<<1>>, 2, 1) produces an empty sequence
    let v = eval_str("DOMAIN SubSeq(<<1>>, 2, 1)").unwrap();
    assert_eq!(
        v,
        Value::empty_set(),
        "DOMAIN of empty sequence should be empty set"
    );
}

#[test]
fn test_domain_of_empty_tuple_literal() {
    // <<>> is an empty sequence/tuple
    let v = eval_str("DOMAIN <<>>").unwrap();
    assert_eq!(v, Value::empty_set(), "DOMAIN of <<>> should be empty set");
}

#[test]
fn test_domain_of_record() {
    let v = eval_str("DOMAIN [a |-> 1, b |-> 2, c |-> 3]").unwrap();
    let expected = eval_str("{\"a\", \"b\", \"c\"}").unwrap();
    assert_eq!(v, expected, "DOMAIN of record should be set of field names");
}

#[test]
fn test_domain_of_record_membership() {
    let v = eval_str("\"b\" \\in DOMAIN [a |-> 1, b |-> 2]").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_domain_of_record_non_member() {
    let v = eval_str("\"z\" \\in DOMAIN [a |-> 1, b |-> 2]").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_domain_cardinality_intfunc() {
    // Cardinality(DOMAIN [i \in 3..7 |-> i]) = 5
    let v = eval_str("Cardinality(DOMAIN [i \\in 3..7 |-> i])").unwrap();
    assert_eq!(v, Value::int(5));
}

#[test]
fn test_domain_type_error_on_integer() {
    let err = eval_str("DOMAIN 42").unwrap_err();
    assert!(
        matches!(err, EvalError::TypeError { .. }),
        "DOMAIN of integer should be TypeError, got: {:?}",
        err
    );
}

#[test]
fn test_domain_type_error_on_boolean() {
    let err = eval_str("DOMAIN TRUE").unwrap_err();
    assert!(
        matches!(err, EvalError::TypeError { .. }),
        "DOMAIN of boolean should be TypeError, got: {:?}",
        err
    );
}

#[test]
fn test_domain_type_error_on_string() {
    let err = eval_str("DOMAIN \"hello\"").unwrap_err();
    assert!(
        matches!(err, EvalError::TypeError { .. }),
        "DOMAIN of string should be TypeError, got: {:?}",
        err
    );
}

// === #1805 regression tests: NotInDomain/IndexOutOfBounds must propagate ===
// Previously these errors were silently converted to false in set-comprehension
// paths. TLC propagates them as Assert.fail (fatal).

/// Regression test for #1805: membership in set-filter must propagate eval
/// errors when the predicate applies a function outside its domain.
/// TLC calls Assert.fail on such errors; TLA2 must not swallow them.
#[test]
fn test_membership_set_filter_propagates_eval_error() {
    // f = [y \in {1,2} |-> TRUE] creates a tuple <<TRUE, TRUE>>.
    // Checking 3 \in {x \in {1,2,3} : f[x]} — when x=3, f[3] is out of bounds.
    let src = r#"LET f == [y \in {1,2} |-> TRUE]
                 IN 3 \in {x \in {1,2,3} : f[x]}"#;
    let err = eval_str(src).unwrap_err();
    assert!(
        matches!(
            err,
            EvalError::NotInDomain { .. } | EvalError::IndexOutOfBounds { .. }
        ),
        "#1805: eval error in set-filter predicate must propagate, got: {:?}",
        err
    );
}

/// Regression test for #1805: IndexOutOfBounds in set-filter predicate
/// must propagate, not be silently treated as false.
#[test]
fn test_membership_set_filter_propagates_index_out_of_bounds() {
    // <<1,2>>[x] where x=3 gives IndexOutOfBounds
    let src = r#"LET t == <<1,2>>
                 IN 3 \in {x \in {1,2,3} : t[x] = 1}"#;
    let err = eval_str(src).unwrap_err();
    assert!(
        matches!(
            err,
            EvalError::IndexOutOfBounds { .. } | EvalError::NotInDomain { .. }
        ),
        "#1805: IndexOutOfBounds in set-filter predicate must propagate, got: {:?}",
        err
    );
}
