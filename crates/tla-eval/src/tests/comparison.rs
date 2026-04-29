// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_comparison() {
    assert_eq!(eval_str("1 < 2").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("2 <= 2").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("3 > 2").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("2 >= 3").unwrap(), Value::Bool(false));
    assert_eq!(eval_str("1 = 1").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("1 /= 2").unwrap(), Value::Bool(true));
}

/// Comprehensive comparison tests covering gaps identified in #1210:
/// negative numbers, equal values for strict comparisons, BigInt boundary,
/// and mixed SmallInt/BigInt paths.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_comparison_negative_numbers() {
    assert_eq!(eval_str("-3 < -1").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("-1 < -3").unwrap(), Value::Bool(false));
    assert_eq!(eval_str("-1 >= 0").unwrap(), Value::Bool(false));
    assert_eq!(eval_str("0 >= -1").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("-5 <= -5").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("-1 > -2").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("-2 > -1").unwrap(), Value::Bool(false));
    assert_eq!(eval_str("-1 = -1").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("-1 /= -2").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("-1 /= -1").unwrap(), Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_comparison_equal_strict() {
    assert_eq!(eval_str("2 < 2").unwrap(), Value::Bool(false));
    assert_eq!(eval_str("2 > 2").unwrap(), Value::Bool(false));
    assert_eq!(eval_str("0 < 0").unwrap(), Value::Bool(false));
    assert_eq!(eval_str("0 > 0").unwrap(), Value::Bool(false));
    assert_eq!(eval_str("-1 < -1").unwrap(), Value::Bool(false));
    assert_eq!(eval_str("-1 > -1").unwrap(), Value::Bool(false));
    assert_eq!(eval_str("2 <= 2").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("2 >= 2").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("0 <= 0").unwrap(), Value::Bool(true));
    assert_eq!(eval_str("0 >= 0").unwrap(), Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_comparison_bigint_boundary() {
    assert_eq!(
        eval_str("9223372036854775807 < 9223372036854775807 + 1").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str("9223372036854775807 + 1 > 9223372036854775807").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str("9223372036854775807 + 1 = 9223372036854775807 + 1").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str("9223372036854775807 + 1 /= 9223372036854775807").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str("-(9223372036854775807 + 1) < 0").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str("-(9223372036854775807 + 1) <= -(9223372036854775807 + 1)").unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_eval_comparison_mixed_smallint_bigint() {
    assert_eq!(
        eval_str("5 < 9223372036854775807 + 1").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str("9223372036854775807 + 1 > 5").unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str("5 >= 9223372036854775807 + 1").unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        eval_str("5 = 9223372036854775807 + 1").unwrap(),
        Value::Bool(false)
    );
}
