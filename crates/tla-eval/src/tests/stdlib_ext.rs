// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for `builtin_stdlib_ext` (Min, Max, STRING) and
//! `builtin_misc` (DyadicRationals, TLAPS) operators.

use super::{eval_str, eval_with_extended_modules};
use crate::Value;

// --- Min / Max ---

#[test]
fn test_min_set() {
    let v = eval_str("Min({3, 1, 4, 1, 5})").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_max_set() {
    let v = eval_str("Max({3, 1, 4, 1, 5})").unwrap();
    assert_eq!(v, Value::SmallInt(5));
}

#[test]
fn test_min_singleton() {
    let v = eval_str("Min({42})").unwrap();
    assert_eq!(v, Value::SmallInt(42));
}

#[test]
fn test_max_singleton() {
    let v = eval_str("Max({42})").unwrap();
    assert_eq!(v, Value::SmallInt(42));
}

#[test]
fn test_min_negative() {
    let v = eval_str("Min({-10, -5, 0, 5, 10})").unwrap();
    assert_eq!(v, Value::SmallInt(-10));
}

#[test]
fn test_max_negative() {
    let v = eval_str("Max({-10, -5})").unwrap();
    assert_eq!(v, Value::SmallInt(-5));
}

#[test]
fn test_min_empty_set_errors() {
    let err = eval_str("Min({})").unwrap_err();
    assert!(
        matches!(err, crate::error::EvalError::Internal { .. }),
        "Expected Internal error for Min({{}}), got: {:?}",
        err
    );
    let msg = format!("{}", err);
    assert!(
        msg.contains("non-empty"),
        "Expected 'non-empty' in error message, got: {}",
        msg
    );
}

#[test]
fn test_max_empty_set_errors() {
    let err = eval_str("Max({})").unwrap_err();
    assert!(
        matches!(err, crate::error::EvalError::Internal { .. }),
        "Expected Internal error for Max({{}}), got: {:?}",
        err
    );
    let msg = format!("{}", err);
    assert!(
        msg.contains("non-empty"),
        "Expected 'non-empty' in error message, got: {}",
        msg
    );
}

// --- STRING ---

#[test]
fn test_string_membership() {
    // "hello" should be a member of STRING (the set of all strings)
    let v = eval_str("\"hello\" \\in STRING").unwrap();
    assert_eq!(v, Value::Bool(true));
}

// --- DyadicRationals ---

#[test]
fn test_dyadic_zero() {
    // Zero is [num |-> 0, den |-> 1]
    let v = eval_str("Zero.num").unwrap();
    assert_eq!(v, Value::SmallInt(0));
}

#[test]
fn test_dyadic_one() {
    let v = eval_str("One.num").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_is_dyadic_rational_true() {
    let v = eval_str("IsDyadicRational([num |-> 3, den |-> 4])").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_is_dyadic_rational_false() {
    // den=3 is not a power of 2
    let v = eval_str("IsDyadicRational([num |-> 1, den |-> 3])").unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[test]
fn test_dyadic_add() {
    // Add(One, One) = [num |-> 2, den |-> 1]
    let v = eval_str("Add(One, One).num").unwrap();
    assert_eq!(v, Value::SmallInt(2));
}

#[test]
fn test_user_defined_add_shadows_dyadic_builtin_direct_apply() {
    let v = eval_with_extended_modules(
        "EXTENDS DyadicRationals\nAdd(a, b) == a + b",
        "Add(3, 4)",
        &["DyadicRationals"],
    )
    .unwrap();
    assert_eq!(
        v,
        Value::SmallInt(7),
        "main-module Add must shadow DyadicRationals.Add"
    );
}

#[test]
fn test_dyadic_half() {
    // Half(One) = [num |-> 1, den |-> 2]
    let v = eval_str("Half(One).den").unwrap();
    assert_eq!(v, Value::SmallInt(2));
}

#[test]
fn test_dyadic_pretty_print_zero() {
    let v = eval_str("PrettyPrint(Zero)").unwrap();
    assert_eq!(v.as_string().unwrap(), "0");
}

#[test]
fn test_dyadic_pretty_print_integer() {
    let v = eval_str("PrettyPrint(One)").unwrap();
    assert_eq!(v.as_string().unwrap(), "1");
}

#[test]
fn test_dyadic_pretty_print_fraction() {
    let v = eval_str("PrettyPrint(Half(One))").unwrap();
    assert_eq!(v.as_string().unwrap(), "1/2");
}

// --- TLAPS operators ---

#[test]
fn test_tlaps_smt_returns_true() {
    // All zero-arity TLAPS operators return TRUE (proof backend pragmas)
    let v = eval_str("SMT").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_tlaps_zenon_returns_true() {
    let v = eval_str("Zenon").unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[test]
fn test_tlaps_auto_returns_true() {
    let v = eval_str("Auto").unwrap();
    assert_eq!(v, Value::Bool(true));
}
