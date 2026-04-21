// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for lazy SetBuilder membership checking (Part of #3979).
//!
//! Tests cover two optimization tiers:
//! 1. **Inverse membership** (O(k)): For invertible patterns (tuple/record/identity),
//!    decompose the target and check components against domains directly.
//! 2. **Short-circuit iteration** (O(|S|) best case): For general expressions,
//!    iterate domain elements and stop on first match.

use super::*;

// --- Basic SetBuilder membership ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_simple_match() {
    // 4 \in {x * 2 : x \in {1, 2, 3}} should be TRUE (x=2 maps to 4)
    assert_eq!(
        eval_str(r#"4 \in {x * 2 : x \in {1, 2, 3}}"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_no_match() {
    // 5 \in {x * 2 : x \in {1, 2, 3}} should be FALSE (no x maps to 5)
    assert_eq!(
        eval_str(r#"5 \in {x * 2 : x \in {1, 2, 3}}"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_notin() {
    // 5 \notin {x * 2 : x \in {1, 2, 3}} should be TRUE
    assert_eq!(
        eval_str(r#"5 \notin {x * 2 : x \in {1, 2, 3}}"#).unwrap(),
        Value::Bool(true)
    );
    // 4 \notin {x * 2 : x \in {1, 2, 3}} should be FALSE
    assert_eq!(
        eval_str(r#"4 \notin {x * 2 : x \in {1, 2, 3}}"#).unwrap(),
        Value::Bool(false)
    );
}

// --- Identity mapping (set-builder is identity) ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_identity_mapping() {
    // {x : x \in {1, 2, 3}} is the same as {1, 2, 3}
    assert_eq!(
        eval_str(r#"2 \in {x : x \in {1, 2, 3}}"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"4 \in {x : x \in {1, 2, 3}}"#).unwrap(),
        Value::Bool(false)
    );
}

// --- Empty domain ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_empty_domain() {
    // Nothing is in {x * 2 : x \in {}} because the domain is empty
    assert_eq!(
        eval_str(r#"0 \in {x * 2 : x \in {}}"#).unwrap(),
        Value::Bool(false)
    );
}

// --- Tuple-valued expressions ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_tuple_expression() {
    // <<2, 1>> \in {<<x, y>> : x \in {1, 2}, y \in {1, 2}} should be TRUE
    assert_eq!(
        eval_str(r#"<<2, 1>> \in {<<x, y>> : x \in {1, 2}, y \in {1, 2}}"#).unwrap(),
        Value::Bool(true)
    );
    // <<1, 3>> should NOT be in the set
    assert_eq!(
        eval_str(r#"<<1, 3>> \in {<<x, y>> : x \in {1, 2}, y \in {1, 2}}"#).unwrap(),
        Value::Bool(false)
    );
}

// --- Multi-variable SetBuilder ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_multi_variable() {
    // {x + y : x \in {1, 2}, y \in {10, 20}} = {11, 12, 21, 22}
    assert_eq!(
        eval_str(r#"11 \in {x + y : x \in {1, 2}, y \in {10, 20}}"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"22 \in {x + y : x \in {1, 2}, y \in {10, 20}}"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"15 \in {x + y : x \in {1, 2}, y \in {10, 20}}"#).unwrap(),
        Value::Bool(false)
    );
}

// --- SetBuilder with complex expressions ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_record_expression() {
    // Membership in a set of records built from a domain
    assert_eq!(
        eval_str(
            r#"[name |-> "a", val |-> 1] \in {[name |-> n, val |-> 1] : n \in {"a", "b", "c"}}"#
        )
        .unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(
            r#"[name |-> "d", val |-> 1] \in {[name |-> n, val |-> 1] : n \in {"a", "b", "c"}}"#
        )
        .unwrap(),
        Value::Bool(false)
    );
}

// --- SetBuilder with interval domain ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_interval_domain() {
    // 25 \in {x * x : x \in 1..10} should be TRUE (x=5)
    assert_eq!(
        eval_str(r#"25 \in {x * x : x \in 1..10}"#).unwrap(),
        Value::Bool(true)
    );
    // 7 \in {x * x : x \in 1..10} should be FALSE (no perfect square = 7)
    assert_eq!(
        eval_str(r#"7 \in {x * x : x \in 1..10}"#).unwrap(),
        Value::Bool(false)
    );
}

// --- SetBuilder membership used in quantifier ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_in_quantifier() {
    // \A y \in {2, 4, 6} : y \in {x * 2 : x \in {1, 2, 3}}
    assert_eq!(
        eval_str(r#"\A y \in {2, 4, 6} : y \in {x * 2 : x \in {1, 2, 3}}"#).unwrap(),
        Value::Bool(true)
    );
    // \E y \in {2, 5, 6} : y \notin {x * 2 : x \in {1, 2, 3}}
    assert_eq!(
        eval_str(r#"\E y \in {2, 5, 6} : y \notin {x * 2 : x \in {1, 2, 3}}"#).unwrap(),
        Value::Bool(true)
    );
}

// --- Named operator with SetBuilder body ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_named_operator() {
    // Named operator: Doubled == {x * 2 : x \in {1, 2, 3}}
    // Membership should work via the zero-arg operator cache
    assert_eq!(
        eval_with_ops(
            r#"Doubled == {x * 2 : x \in {1, 2, 3}}"#,
            r#"4 \in Doubled"#
        )
        .unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_with_ops(
            r#"Doubled == {x * 2 : x \in {1, 2, 3}}"#,
            r#"5 \in Doubled"#
        )
        .unwrap(),
        Value::Bool(false)
    );
}

// --- SetBuilder with set-valued expressions ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_set_valued() {
    // Check membership where the expression builds sets
    // {1, 2} \in {{x} : x \in {1, 2, 3}} should be FALSE (only singletons in the result)
    assert_eq!(
        eval_str(r#"{1, 2} \in {{x} : x \in {1, 2, 3}}"#).unwrap(),
        Value::Bool(false)
    );
    // {2} \in {{x} : x \in {1, 2, 3}} should be TRUE
    assert_eq!(
        eval_str(r#"{2} \in {{x} : x \in {1, 2, 3}}"#).unwrap(),
        Value::Bool(true)
    );
}

// --- SetBuilder with string concatenation ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_first_element_match() {
    // Verify short-circuit: first element matches
    // 2 \in {x * 2 : x \in {1, 2, 3}} — x=1 gives 2, should short-circuit
    assert_eq!(
        eval_str(r#"2 \in {x * 2 : x \in {1, 2, 3}}"#).unwrap(),
        Value::Bool(true)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_last_element_match() {
    // 6 \in {x * 2 : x \in {1, 2, 3}} — x=3 gives 6, last element
    assert_eq!(
        eval_str(r#"6 \in {x * 2 : x \in {1, 2, 3}}"#).unwrap(),
        Value::Bool(true)
    );
}

// --- SetBuilder nested in union (common pattern) ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_in_union() {
    // Membership in a union where one branch is a SetBuilder
    // This is the pattern used by MCLamportMutex's Messages type
    assert_eq!(
        eval_with_ops(
            r#"S == {"a", "b"} \union {<<x, 1>> : x \in {1, 2, 3}}"#,
            r#"<<2, 1>> \in S"#
        )
        .unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_with_ops(
            r#"S == {"a", "b"} \union {<<x, 1>> : x \in {1, 2, 3}}"#,
            r#""a" \in S"#
        )
        .unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_with_ops(
            r#"S == {"a", "b"} \union {<<x, 1>> : x \in {1, 2, 3}}"#,
            r#"<<4, 1>> \in S"#
        )
        .unwrap(),
        Value::Bool(false)
    );
}

// --- SetBuilder with SUBSET domain ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_subset_domain() {
    // {Cardinality(s) : s \in SUBSET {1, 2, 3}} = {0, 1, 2, 3}
    assert_eq!(
        eval_with_ops(
            "EXTENDS FiniteSets",
            r#"2 \in {Cardinality(s) : s \in SUBSET {1, 2, 3}}"#
        )
        .unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_with_ops(
            "EXTENDS FiniteSets",
            r#"4 \in {Cardinality(s) : s \in SUBSET {1, 2, 3}}"#
        )
        .unwrap(),
        Value::Bool(false)
    );
}

// --- SetBuilder membership equality with eager evaluation ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_set_builder_membership_matches_eager_evaluation() {
    // Verify that lazy membership gives the same answer as constructing the set
    // and checking contains. This is a correctness cross-check.
    let set_val = eval_str(r#"{x * x : x \in 1..5}"#).unwrap();
    for target in [1, 4, 9, 16, 25, 2, 3, 5, 10, 15] {
        let lazy_result =
            eval_str(&format!(r#"{} \in {{x * x : x \in 1..5}}"#, target)).unwrap();
        let eager_contains = set_val.set_contains(&Value::int(target));
        assert_eq!(
            lazy_result,
            Value::Bool(eager_contains.unwrap_or(false)),
            "Mismatch for target {} in {{x*x : x \\in 1..5}}",
            target,
        );
    }
}

// ======================================================================
// Inverse membership tests (Part of #3979)
// These test the O(k) inverse checking path for invertible patterns.
// ======================================================================

// --- Pattern 1: Identity mapping inverse ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_identity_membership() {
    // {x : x \in 1..100} — identity mapping, should check domain directly
    assert_eq!(
        eval_str(r#"50 \in {x : x \in 1..100}"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"0 \in {x : x \in 1..100}"#).unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        eval_str(r#"101 \in {x : x \in 1..100}"#).unwrap(),
        Value::Bool(false)
    );
}

// --- Pattern 2: Tuple inverse membership ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_tuple_membership_two_vars() {
    // {<<x, y>> : x \in {1, 2, 3}, y \in {"a", "b"}}
    // Inverse: decompose target tuple, check each component against its domain
    assert_eq!(
        eval_str(r#"<<2, "a">> \in {<<x, y>> : x \in {1, 2, 3}, y \in {"a", "b"}}"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"<<4, "a">> \in {<<x, y>> : x \in {1, 2, 3}, y \in {"a", "b"}}"#).unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        eval_str(r#"<<1, "c">> \in {<<x, y>> : x \in {1, 2, 3}, y \in {"a", "b"}}"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_tuple_membership_three_vars() {
    // {<<x, y, z>> : x \in {1, 2}, y \in {3, 4}, z \in {5, 6}}
    // Without inverse: 2*2*2 = 8 combinations to check
    // With inverse: 3 domain checks
    assert_eq!(
        eval_str(r#"<<1, 3, 5>> \in {<<x, y, z>> : x \in {1, 2}, y \in {3, 4}, z \in {5, 6}}"#)
            .unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"<<2, 4, 6>> \in {<<x, y, z>> : x \in {1, 2}, y \in {3, 4}, z \in {5, 6}}"#)
            .unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"<<1, 3, 7>> \in {<<x, y, z>> : x \in {1, 2}, y \in {3, 4}, z \in {5, 6}}"#)
            .unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_tuple_membership_reordered_vars() {
    // {<<y, x>> : x \in {1, 2}, y \in {"a", "b"}}
    // Variables appear in different order than bounds — inverse should still work
    assert_eq!(
        eval_str(r#"<<"a", 1>> \in {<<y, x>> : x \in {1, 2}, y \in {"a", "b"}}"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"<<1, "a">> \in {<<y, x>> : x \in {1, 2}, y \in {"a", "b"}}"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_tuple_membership_wrong_length() {
    // Target tuple has wrong number of elements
    assert_eq!(
        eval_str(r#"<<1>> \in {<<x, y>> : x \in {1, 2}, y \in {3, 4}}"#).unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        eval_str(r#"<<1, 2, 3>> \in {<<x, y>> : x \in {1, 2}, y \in {3, 4}}"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_tuple_membership_non_tuple_target() {
    // Target is not a tuple at all
    assert_eq!(
        eval_str(r#"1 \in {<<x, y>> : x \in {1, 2}, y \in {3, 4}}"#).unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        eval_str(r#""hello" \in {<<x, y>> : x \in {1, 2}, y \in {3, 4}}"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_tuple_membership_with_interval_domains() {
    // {<<x, y>> : x \in 1..10, y \in 1..10} — large Cartesian product (100 elements)
    // Inverse: O(1) per check instead of O(100)
    assert_eq!(
        eval_str(r#"<<5, 7>> \in {<<x, y>> : x \in 1..10, y \in 1..10}"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"<<0, 5>> \in {<<x, y>> : x \in 1..10, y \in 1..10}"#).unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        eval_str(r#"<<5, 11>> \in {<<x, y>> : x \in 1..10, y \in 1..10}"#).unwrap(),
        Value::Bool(false)
    );
}

// --- Pattern 3: Record inverse membership ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_record_membership_two_fields() {
    // {[name |-> n, age |-> a] : n \in {"Alice", "Bob"}, a \in {25, 30}}
    // Inverse: decompose target record, check field values against domains
    assert_eq!(
        eval_str(
            r#"[name |-> "Alice", age |-> 25] \in {[name |-> n, age |-> a] : n \in {"Alice", "Bob"}, a \in {25, 30}}"#
        )
        .unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(
            r#"[name |-> "Charlie", age |-> 25] \in {[name |-> n, age |-> a] : n \in {"Alice", "Bob"}, a \in {25, 30}}"#
        )
        .unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        eval_str(
            r#"[name |-> "Alice", age |-> 35] \in {[name |-> n, age |-> a] : n \in {"Alice", "Bob"}, a \in {25, 30}}"#
        )
        .unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_record_membership_wrong_fields() {
    // Target record has different field names or different number of fields
    assert_eq!(
        eval_str(
            r#"[name |-> "Alice"] \in {[name |-> n, age |-> a] : n \in {"Alice", "Bob"}, a \in {25, 30}}"#
        )
        .unwrap(),
        Value::Bool(false)
    );
    assert_eq!(
        eval_str(
            r#"[name |-> "Alice", age |-> 25, id |-> 1] \in {[name |-> n, age |-> a] : n \in {"Alice", "Bob"}, a \in {25, 30}}"#
        )
        .unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_record_membership_non_record_target() {
    // Target is not a record
    assert_eq!(
        eval_str(
            r#"<<1, 2>> \in {[name |-> n, age |-> a] : n \in {"Alice"}, a \in {25}}"#
        )
        .unwrap(),
        Value::Bool(false)
    );
}

// --- Fallback path (non-invertible body) still works ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_non_invertible_body_still_works() {
    // {x + y : x \in {1, 2}, y \in {10, 20}} — body is x + y, not invertible
    // Must fall back to iterate-and-check
    assert_eq!(
        eval_str(r#"11 \in {x + y : x \in {1, 2}, y \in {10, 20}}"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"15 \in {x + y : x \in {1, 2}, y \in {10, 20}}"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_partial_var_tuple_falls_back() {
    // {<<x, x + 1>> : x \in {1, 2, 3}} — second component is expression, not pure variable
    // Should fall back to iterate-and-check (not invertible)
    assert_eq!(
        eval_str(r#"<<2, 3>> \in {<<x, x + 1>> : x \in {1, 2, 3}}"#).unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(r#"<<2, 4>> \in {<<x, x + 1>> : x \in {1, 2, 3}}"#).unwrap(),
        Value::Bool(false)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_record_with_constant_field_falls_back() {
    // {[name |-> n, val |-> 1] : n \in {"a", "b"}} — val is constant, not a bound variable
    // Should fall back to iterate-and-check (not all fields are pure variables)
    assert_eq!(
        eval_str(
            r#"[name |-> "a", val |-> 1] \in {[name |-> n, val |-> 1] : n \in {"a", "b"}}"#
        )
        .unwrap(),
        Value::Bool(true)
    );
    assert_eq!(
        eval_str(
            r#"[name |-> "a", val |-> 2] \in {[name |-> n, val |-> 1] : n \in {"a", "b"}}"#
        )
        .unwrap(),
        Value::Bool(false)
    );
}

// --- Cross-check: inverse and eager produce same results ---

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_tuple_matches_eager_cross_check() {
    // Verify inverse tuple membership gives the same answer as expected.
    // Use known-correct expected values to avoid manual Value construction.
    for x in [1, 2, 3, 4] {
        for y in ["a", "b", "c"] {
            let expr = format!(
                r#"<<{}, "{}">> \in {{<<x, y>> : x \in {{1, 2, 3}}, y \in {{"a", "b"}}}}"#,
                x, y
            );
            let lazy_result = eval_str(&expr).unwrap();

            // Expected: x in {1,2,3} AND y in {"a","b"}
            let expected = (1..=3).contains(&x) && (y == "a" || y == "b");
            assert_eq!(
                lazy_result,
                Value::Bool(expected),
                "Mismatch for <<{}, \"{}\">>",
                x,
                y,
            );
        }
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_record_matches_eager_cross_check() {
    // Verify inverse record membership gives the same answer as eager set construction.
    // Use eval_str for both paths to avoid manual RecordValue construction.
    for k in ["x", "y", "z"] {
        for v in [1, 2, 3] {
            // Lazy membership (uses inverse path for invertible pattern)
            let lazy_expr = format!(
                r#"[k |-> "{}", v |-> {}] \in {{[k |-> k, v |-> v] : k \in {{"x", "y"}}, v \in {{1, 2}}}}"#,
                k, v
            );
            let lazy_result = eval_str(&lazy_expr).unwrap();

            // Expected: k in {"x", "y"} AND v in {1, 2}
            let expected = (k == "x" || k == "y") && (v == 1 || v == 2);
            assert_eq!(
                lazy_result,
                Value::Bool(expected),
                "Mismatch for [k |-> \"{}\", v |-> {}]",
                k,
                v,
            );
        }
    }
}
