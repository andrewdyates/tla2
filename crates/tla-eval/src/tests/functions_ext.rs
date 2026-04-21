// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `builtin_functions_ext` module — RestrictDomain, RestrictValues,
//! IsRestriction, Pointwise, AntiFunction.

use super::{eval_str, eval_with_ops};
use crate::Value;

// --- RestrictDomain ---

#[test]
fn test_restrict_domain_keeps_matching() {
    // RestrictDomain([a |-> 1, b |-> 2, c |-> 3], LAMBDA x: x = "a" \/ x = "c")
    // Should keep only "a" and "c"
    let v = eval_str(
        "DOMAIN RestrictDomain(\"a\" :> 1 @@ \"b\" :> 2 @@ \"c\" :> 3, LAMBDA x: x = \"a\" \\/ x = \"c\") = {\"a\", \"c\"}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_restrict_domain_empty_result() {
    let v = eval_str("RestrictDomain(\"a\" :> 1, LAMBDA x: FALSE) = EmptyBag").unwrap();
    // Both are empty functions, should be equal
    assert_eq!(v, Value::Bool(true));
}

// --- RestrictValues ---

#[test]
fn test_restrict_values_keeps_matching() {
    // Keep only entries where value > 1
    let v = eval_str(
        "DOMAIN RestrictValues(\"a\" :> 1 @@ \"b\" :> 2 @@ \"c\" :> 3, LAMBDA v: v > 1) = {\"b\", \"c\"}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true));
}

// --- IsRestriction ---

#[test]
fn test_is_restriction_true() {
    // {a->1} is a restriction of {a->1, b->2}
    let v = eval_str("IsRestriction(\"a\" :> 1, \"a\" :> 1 @@ \"b\" :> 2)").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_is_restriction_false_extra_key() {
    // {a->1, c->3} is NOT a restriction of {a->1, b->2} (c not in domain)
    let v = eval_str("IsRestriction(\"a\" :> 1 @@ \"c\" :> 3, \"a\" :> 1 @@ \"b\" :> 2)").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_is_restriction_false_different_value() {
    // {a->2} is NOT a restriction of {a->1, b->2} (different value for a)
    let v = eval_str("IsRestriction(\"a\" :> 2, \"a\" :> 1 @@ \"b\" :> 2)").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_is_restriction_empty_is_restriction_of_anything() {
    let v = eval_str("IsRestriction(EmptyBag, \"a\" :> 1)").unwrap();
    assert_eq!(v, Value::Bool(true));
}

// Regression test for #2894: IsRestriction must use values_equal for
// set-valued function comparisons. Without values_equal, sets that are
// extensionally equal but structurally different (e.g., {1,2} vs {2,1})
// could compare as not-equal, causing IsRestriction to return FALSE
// when it should return TRUE.
#[test]
fn test_is_restriction_set_valued_functions() {
    // Both f and g map "a" to the same set {1,2}, but internal ordering
    // may differ. values_equal is required for correct comparison.
    let v = eval_str("IsRestriction(\"a\" :> {1, 2}, \"a\" :> {1, 2} @@ \"b\" :> {3})").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_is_restriction_set_valued_not_equal() {
    // f maps "a" to {1,2}, g maps "a" to {1,3} — should be FALSE
    let v = eval_str("IsRestriction(\"a\" :> {1, 2}, \"a\" :> {1, 3} @@ \"b\" :> {4})").unwrap();
    assert_eq!(v, Value::Bool(false));
}

// Regression test for #2894: IsRestriction with SetPred-valued functions.
// This test WOULD FAIL under the old PartialEq-based code because
// SetPred({x \in {1,2,3} : x < 3}) is structurally different from Set({1,2}),
// making PartialEq return false even though they are extensionally equal.
// values_equal materializes the SetPred and compares element-by-element.
#[test]
fn test_is_restriction_setpred_vs_explicit_set() {
    let v = eval_str(
        "IsRestriction(\"a\" :> {x \\in {1,2,3} : x < 3}, \"a\" :> {1, 2} @@ \"b\" :> {4})",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true));
}

// Regression test for #2894: IsRestriction where BOTH sides use SetPred
// with different predicates but same extension.
#[test]
fn test_is_restriction_setpred_both_sides() {
    let v = eval_str(
        "IsRestriction(\"a\" :> {x \\in {1,2,3} : x < 3}, \"a\" :> {x \\in {0,1,2,3} : x > 0 /\\ x < 3} @@ \"b\" :> {4})",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true));
}

// --- Pointwise ---

#[test]
fn test_pointwise_addition() {
    // Pointwise(Add, f, g) applies Add to corresponding values
    let v = eval_with_ops(
        "Add(a, b) == a + b",
        "(Pointwise(Add, \"x\" :> 10 @@ \"y\" :> 20, \"x\" :> 1 @@ \"y\" :> 2))[\"x\"]",
    )
    .unwrap();
    assert_eq!(v, Value::SmallInt(11));
}

#[test]
fn test_pointwise_domain_intersection() {
    // Pointwise only operates on intersection of domains
    let v = eval_with_ops(
        "Add(a, b) == a + b",
        "DOMAIN Pointwise(Add, \"x\" :> 1 @@ \"y\" :> 2, \"y\" :> 3 @@ \"z\" :> 4) = {\"y\"}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true));
}

// --- AntiFunction ---

#[test]
fn test_anti_function_reverses_mapping() {
    // AntiFunction({"a" :> 1, "b" :> 2}) = {1 :> "a", 2 :> "b"}
    let v = eval_str("(AntiFunction(\"a\" :> 1 @@ \"b\" :> 2))[1] = \"a\"").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_anti_function_non_injective_errors() {
    // Non-injective function (two keys map to same value) should error with Internal
    let err = eval_str("AntiFunction(\"a\" :> 1 @@ \"b\" :> 1)").unwrap_err();
    assert!(
        matches!(err, crate::error::EvalError::Internal { .. }),
        "Expected Internal error for non-injective AntiFunction, got: {:?}",
        err
    );
    let msg = format!("{}", err);
    assert!(
        msg.contains("injective"),
        "Expected 'injective' in error message, got: {}",
        msg
    );
}

#[test]
fn test_anti_function_empty() {
    // AntiFunction of empty function is empty function
    let v = eval_str("AntiFunction(EmptyBag) = EmptyBag").unwrap();
    assert_eq!(v, Value::Bool(true));
}
