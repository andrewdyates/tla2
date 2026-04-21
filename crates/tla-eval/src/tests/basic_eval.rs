// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_literals() {
    assert_eq!(eval_str("TRUE").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("FALSE").unwrap(), Value::Bool(false));
    assert_eq!(eval_str("42").unwrap(), Value::int(42));
    assert_eq!(eval_str("-5").unwrap(), Value::int(-5));
    assert_eq!(eval_str("\"hello\"").unwrap(), Value::string("hello"));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_logic() {
    assert_eq!(eval_str(r#"TRUE /\ FALSE"#).unwrap(), Value::Bool(false));
    assert_eq!(eval_str(r#"TRUE \/ FALSE"#).unwrap(), Value::Bool(true));
    assert_eq!(eval_str("~TRUE").unwrap(), Value::Bool(false));
    assert_eq!(eval_str("FALSE => TRUE").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("TRUE <=> TRUE").unwrap(), Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_arithmetic() {
    assert_eq!(eval_str("2 + 3").unwrap(), Value::int(5));
    assert_eq!(eval_str("10 - 4").unwrap(), Value::int(6));
    assert_eq!(eval_str("3 * 7").unwrap(), Value::int(21));
    assert_eq!(eval_str(r#"10 \div 3"#).unwrap(), Value::int(3));
    assert_eq!(eval_str("10 % 3").unwrap(), Value::int(1));
    // TLA+ uses Euclidean modulo: -1 % 5 = 4 (not -1 like Rust)
    assert_eq!(eval_str("(-1) % 5").unwrap(), Value::int(4));
    assert_eq!(eval_str("(-6) % 5").unwrap(), Value::int(4));
    assert_eq!(eval_str("(-5) % 5").unwrap(), Value::int(0));
    assert_eq!(eval_str("2^10").unwrap(), Value::int(1024));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_abs() {
    assert_eq!(eval_str("Abs(5)").unwrap(), Value::int(5));
    assert_eq!(eval_str("Abs(-5)").unwrap(), Value::int(5));
    assert_eq!(eval_str("Abs(0)").unwrap(), Value::int(0));
    assert_eq!(eval_str("Abs(-100)").unwrap(), Value::int(100));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_sign() {
    assert_eq!(eval_str("Sign(42)").unwrap(), Value::int(1));
    assert_eq!(eval_str("Sign(-42)").unwrap(), Value::int(-1));
    assert_eq!(eval_str("Sign(0)").unwrap(), Value::int(0));
    assert_eq!(eval_str("Sign(1)").unwrap(), Value::int(1));
    assert_eq!(eval_str("Sign(-1)").unwrap(), Value::int(-1));
}
