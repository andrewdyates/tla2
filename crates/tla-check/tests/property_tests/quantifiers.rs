// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::helpers::{eval_str, small_int_set};
use proptest::prelude::*;
use tla_check::Value;

// ============================================================================
// Quantifier property tests
// ============================================================================

// Non-parameterized quantifier tests (outside proptest! block)
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_forall_empty() {
    // \A x \in {} : FALSE = TRUE (vacuously true)
    // Note: Using parentheses around the body to avoid parser issues
    let result = eval_str(r#"\A x \in {} : (FALSE)"#).unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_empty() {
    // \E x \in {} : TRUE = FALSE (no witnesses)
    let result = eval_str(r#"\E x \in {} : (TRUE)"#).unwrap();
    assert_eq!(result, Value::Bool(false));
}

proptest! {

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_forall_singleton(v in -10i32..10) {
        // \A x \in {v} : x = v
        let result = eval_str(&format!(r#"\A x \in {{{}}} : x = {}"#, v, v)).unwrap();
        prop_assert_eq!(result, Value::Bool(true));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_exists_singleton(v in -10i32..10) {
        // \E x \in {v} : x = v
        let result = eval_str(&format!(r#"\E x \in {{{}}} : x = {}"#, v, v)).unwrap();
        prop_assert_eq!(result, Value::Bool(true));
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_forall_exists_duality(s in small_int_set()) {
        // ~(\A x \in S : x > 0) = \E x \in S : ~(x > 0)
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let lhs = eval_str(&format!(r#"~(\A x \in {} : x > 0)"#, s_str)).unwrap();
        let rhs = eval_str(&format!(r#"\E x \in {} : ~(x > 0)"#, s_str)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_exists_forall_duality(s in small_int_set()) {
        // ~(\E x \in S : x > 0) = \A x \in S : ~(x > 0)
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let lhs = eval_str(&format!(r#"~(\E x \in {} : x > 0)"#, s_str)).unwrap();
        let rhs = eval_str(&format!(r#"\A x \in {} : ~(x > 0)"#, s_str)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_forall_and_split(s in small_int_set()) {
        // \A x \in S : (P(x) /\ Q(x)) = (\A x \in S : P(x)) /\ (\A x \in S : Q(x))
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let lhs = eval_str(&format!(r#"\A x \in {} : (x >= 0 /\ x <= 10)"#, s_str)).unwrap();
        let rhs = eval_str(&format!(r#"(\A x \in {} : x >= 0) /\ (\A x \in {} : x <= 10)"#, s_str, s_str)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn prop_exists_or_split(s in small_int_set()) {
        // \E x \in S : (P(x) \/ Q(x)) = (\E x \in S : P(x)) \/ (\E x \in S : Q(x))
        let s_str = format!("{{{}}}", s.iter().map(std::string::ToString::to_string).collect::<Vec<_>>().join(", "));
        let lhs = eval_str(&format!(r#"\E x \in {} : (x < 0 \/ x > 5)"#, s_str)).unwrap();
        let rhs = eval_str(&format!(r#"(\E x \in {} : x < 0) \/ (\E x \in {} : x > 5)"#, s_str, s_str)).unwrap();
        prop_assert_eq!(lhs, rhs);
    }
}
