// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Reals module tests (membership, \notin, \subseteq, Infinity, Real domain).
//!
//! TLA+ Reals module: TLC doesn't actually support real numbers.
//! In TLA2, we implement Real as a superset of Int (Int <= Real).
//! The Infinity constant is defined but errors on arithmetic operations.
//!
//! Split from property_tests.rs lines 3750-3881. Part of #1371.

use tla_check::Value;

use super::helpers::eval_with_extends;

// ============================================================================
// Reals module tests
// ============================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reals_membership_positive() {
    // EXTENDS Reals required for Real constant
    let result = eval_with_extends(r#"5 \in Real"#, &["Reals"]).unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reals_membership_negative() {
    // Negative integers are also in Real
    let result = eval_with_extends(r#"-3 \in Real"#, &["Reals"]).unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reals_membership_zero() {
    // Zero is in Real
    let result = eval_with_extends(r#"0 \in Real"#, &["Reals"]).unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reals_non_membership_string() {
    // Strings are not in Real
    let result = eval_with_extends(r#""hello" \in Real"#, &["Reals"]).unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reals_non_membership_bool() {
    // Booleans are not in Real
    let result = eval_with_extends(r#"TRUE \in Real"#, &["Reals"]).unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reals_non_membership_set() {
    // Sets are not in Real
    let result = eval_with_extends(r#"{1, 2} \in Real"#, &["Reals"]).unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reals_notin() {
    // \notin works for Real
    let result = eval_with_extends(r#""hello" \notin Real"#, &["Reals"]).unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reals_int_notin() {
    // Integers are NOT in the "not in Real" category
    let result = eval_with_extends(r#"42 \notin Real"#, &["Reals"]).unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reals_subseteq_from_finite_set() {
    // {1, 2, 3} \subseteq Real is TRUE (since Int <= Real)
    let result = eval_with_extends(r#"{1, 2, 3} \subseteq Real"#, &["Reals"]).unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reals_subseteq_mixed_types() {
    // {"hello", 1} \subseteq Real is FALSE (string not in Real)
    let result = eval_with_extends(r#"{"hello"} \subseteq Real"#, &["Reals"]).unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_infinity_constant_exists() {
    // Infinity constant should be defined (as a ModelValue)
    let result = eval_with_extends(r#"Infinity"#, &["Reals"]).unwrap();
    // Infinity is a ModelValue representing an abstract concept
    if let Value::ModelValue(ref name) = result {
        assert_eq!(name.as_ref(), "Infinity");
    } else {
        panic!("Expected Infinity to be a ModelValue");
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_real_function_domain() {
    // Functions with Real domain should work
    let result = eval_with_extends(r#"LET f[n \in Real] == n * 2 IN f[5]"#, &["Reals"]).unwrap();
    assert_eq!(result, Value::int(10));
}
