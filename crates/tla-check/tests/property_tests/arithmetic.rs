// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;
use proptest::prelude::*;
use tla_check::Value;

use super::helpers::eval_str;

/// Strategy for small integers (avoid overflow in parsing)
fn small_int() -> impl Strategy<Value = i32> {
    -1000i32..1000
}

/// Strategy for positive integers (for division)
fn positive_int() -> impl Strategy<Value = i32> {
    1i32..100
}

proptest! {
    // --- Addition properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_add_commutativity(a in small_int(), b in small_int()) {
        // a + b = b + a
        let lhs = eval_str(&format!("{} + {}", a, b)).unwrap();
        let rhs = eval_str(&format!("{} + {}", b, a)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_add_associativity(a in small_int(), b in small_int(), c in small_int()) {
        // (a + b) + c = a + (b + c)
        let lhs = eval_str(&format!("({} + {}) + {}", a, b, c)).unwrap();
        let rhs = eval_str(&format!("{} + ({} + {})", a, b, c)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_add_identity(a in small_int()) {
        // a + 0 = a
        let result = eval_str(&format!("{} + 0", a)).unwrap();
        prop_assert_eq!(result, Value::int(a.into()));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_add_inverse(a in small_int()) {
        // a + (-a) = 0
        let result = eval_str(&format!("{} + ({})", a, -a)).unwrap();
        prop_assert_eq!(result, Value::int(0));
    }

    // --- Multiplication properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_mult_commutativity(a in small_int(), b in small_int()) {
        // a * b = b * a
        let lhs = eval_str(&format!("{} * {}", a, b)).unwrap();
        let rhs = eval_str(&format!("{} * {}", b, a)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_mult_associativity(a in -100i32..100, b in -100i32..100, c in -100i32..100) {
        // (a * b) * c = a * (b * c)
        let lhs = eval_str(&format!("({} * {}) * {}", a, b, c)).unwrap();
        let rhs = eval_str(&format!("{} * ({} * {})", a, b, c)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_mult_identity(a in small_int()) {
        // a * 1 = a
        let result = eval_str(&format!("{} * 1", a)).unwrap();
        prop_assert_eq!(result, Value::int(a.into()));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_mult_zero(a in small_int()) {
        // a * 0 = 0
        let result = eval_str(&format!("{} * 0", a)).unwrap();
        prop_assert_eq!(result, Value::int(0));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_distributive(a in -50i32..50, b in -50i32..50, c in -50i32..50) {
        // a * (b + c) = a * b + a * c
        let lhs = eval_str(&format!("{} * ({} + {})", a, b, c)).unwrap();
        let rhs = eval_str(&format!("{} * {} + {} * {}", a, b, a, c)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    // --- Subtraction properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_sub_definition(a in small_int(), b in small_int()) {
        // a - b = a + (-b)
        let lhs = eval_str(&format!("{} - {}", a, b)).unwrap();
        let rhs = eval_str(&format!("{} + ({})", a, -b)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_sub_self(a in small_int()) {
        // a - a = 0
        let result = eval_str(&format!("{} - {}", a, a)).unwrap();
        prop_assert_eq!(result, Value::int(0));
    }

    // --- Negation properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_negation_involution(a in small_int()) {
        // -(-a) = a
        let result = eval_str(&format!("-({})", -a)).unwrap();
        prop_assert_eq!(result, Value::int(a.into()));
    }

    // --- Comparison properties ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_less_than_irreflexive(a in small_int()) {
        // ~(a < a)
        let result = eval_str(&format!("{} < {}", a, a)).unwrap();
        prop_assert_eq!(result, Value::Bool(false));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_less_equal_reflexive(a in small_int()) {
        // a <= a
        let result = eval_str(&format!("{} <= {}", a, a)).unwrap();
        prop_assert_eq!(result, Value::Bool(true));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_equality_reflexive(a in small_int()) {
        // a = a
        let result = eval_str(&format!("{} = {}", a, a)).unwrap();
        prop_assert_eq!(result, Value::Bool(true));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_inequality_irreflexive(a in small_int()) {
        // ~(a /= a)
        let result = eval_str(&format!("{} /= {}", a, a)).unwrap();
        prop_assert_eq!(result, Value::Bool(false));
    }

    // --- Division/modulo properties (TLA+ uses Euclidean) ---

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_div_mod_identity(a in small_int(), b in positive_int()) {
        // a = (a \div b) * b + (a % b)
        let div_result = eval_str(&format!(r#"({}) \div {}"#, a, b)).unwrap();
        let mod_result = eval_str(&format!("({}) % {}", a, b)).unwrap();

        // Use to_bigint() to handle both SmallInt and Int variants
        let div_val = div_result.to_bigint().expect("Expected integer for div");
        let mod_val = mod_result.to_bigint().expect("Expected integer for mod");

        let reconstructed: BigInt = &div_val * BigInt::from(b) + &mod_val;
        prop_assert_eq!(reconstructed, BigInt::from(a));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_mod_range(a in small_int(), b in positive_int()) {
        // 0 <= (a % b) < b  (Euclidean modulo is always non-negative)
        let mod_result = eval_str(&format!("({}) % {}", a, b)).unwrap();

        // Use to_bigint() to handle both SmallInt and Int variants
        let m = mod_result.to_bigint().expect("Expected integer");
        prop_assert!(m >= BigInt::from(0));
        prop_assert!(m < BigInt::from(b));
    }
}
