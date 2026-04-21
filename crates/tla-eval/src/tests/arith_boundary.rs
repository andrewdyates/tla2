// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boundary tests for `eval_arith` — overflow, underflow, large exponents.

use super::eval_str;
use crate::Value;

#[test]
fn test_arith_smallint_max_boundary() {
    // SmallInt holds i64. Operations near the boundary should promote to BigInt.
    // i64::MAX = 9223372036854775807
    let v = eval_str("9223372036854775807 + 0").unwrap();
    assert_eq!(v, Value::SmallInt(i64::MAX));
}

#[test]
fn test_arith_smallint_overflow_promotes() {
    // i64::MAX + 1 should overflow to BigInt
    let v = eval_str("9223372036854775807 + 1").unwrap();
    // Result should be a valid integer, just bigger than SmallInt can hold
    let n = v.to_bigint().unwrap();
    assert_eq!(n.to_string(), "9223372036854775808");
}

#[test]
fn test_arith_smallint_min_boundary() {
    // i64::MIN = -9223372036854775808
    let v = eval_str("-9223372036854775808 + 0").unwrap();
    // Note: parser may handle this differently, but the arithmetic should work
    let n = v.to_bigint().unwrap();
    assert_eq!(n.to_string(), "-9223372036854775808");
}

#[test]
fn test_arith_large_multiplication() {
    // Large multiplication that overflows i64
    let v = eval_str("9223372036854775807 * 2").unwrap();
    let n = v.to_bigint().unwrap();
    assert_eq!(n.to_string(), "18446744073709551614");
}

#[test]
fn test_arith_exponentiation_zero_exponent() {
    let v = eval_str("5 ^ 0").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_arith_exponentiation_one_exponent() {
    let v = eval_str("5 ^ 1").unwrap();
    assert_eq!(v, Value::SmallInt(5));
}

#[test]
fn test_arith_exponentiation_large() {
    // 2^63 overflows i64 but should work with BigInt
    let v = eval_str("2 ^ 63").unwrap();
    let n = v.to_bigint().unwrap();
    assert_eq!(n.to_string(), "9223372036854775808");
}

#[test]
fn test_arith_negative_base_even_exponent() {
    let v = eval_str("(-3) ^ 2").unwrap();
    assert_eq!(v, Value::SmallInt(9));
}

#[test]
fn test_arith_negative_base_odd_exponent() {
    let v = eval_str("(-3) ^ 3").unwrap();
    assert_eq!(v, Value::SmallInt(-27));
}

#[test]
fn test_arith_zero_base_zero_exponent() {
    // 0^0 = 1 (standard mathematical convention)
    let v = eval_str("0 ^ 0").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_arith_div_truncates_toward_zero() {
    // TLA+ integer division truncates toward negative infinity (Euclidean)
    let v = eval_str("7 \\div 2").unwrap();
    assert_eq!(v, Value::SmallInt(3));
}

#[test]
fn test_arith_div_negative_dividend() {
    // -7 \div 2 = -4 (floor division in TLA+)
    let v = eval_str("(-7) \\div 2").unwrap();
    assert_eq!(v, Value::SmallInt(-4));
}

#[test]
fn test_arith_mod_positive() {
    let v = eval_str("7 % 3").unwrap();
    assert_eq!(v, Value::SmallInt(1));
}

#[test]
fn test_arith_mod_result_always_non_negative() {
    // In TLA+, a % b is always non-negative when b > 0
    let v = eval_str("(-7) % 3").unwrap();
    assert_eq!(v, Value::SmallInt(2));
}

#[test]
fn test_arith_subtraction_underflow() {
    // Result goes below i64::MIN
    let v = eval_str("-9223372036854775808 - 1").unwrap();
    let n = v.to_bigint().unwrap();
    assert_eq!(n.to_string(), "-9223372036854775809");
}

#[test]
fn test_arith_negation_of_min() {
    // Negating i64::MIN would overflow in fixed-width, should promote to BigInt
    let v = eval_str("-(-9223372036854775808)").unwrap();
    let n = v.to_bigint().unwrap();
    assert_eq!(n.to_string(), "9223372036854775808");
}
