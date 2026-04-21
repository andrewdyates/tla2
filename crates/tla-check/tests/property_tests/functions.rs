// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Functions module tests — Restrict, IsInjective, IsSurjective, IsBijection,
//! Inverse, Range, RestrictDomain, RestrictValues, IsRestriction, Pointwise,
//! AntiFunction, Injection, Surjection, Bijection, Exists* variants.
//!
//! Consolidated from property_tests.rs lines 2615-2900 and 3192-3291.
//! Part of #1371.

use tla_check::Value;
use tla_core::{lower, parse_to_syntax_tree, FileId};
use tla_value::SortedSet;

use super::helpers::int_set;
use std::sync::Arc;

/// Helper to evaluate with Functions module
fn eval_functions_str(src: &str) -> Result<Value, String> {
    let module_src = format!(
        "---- MODULE Test ----\nEXTENDS Functions\n\nOp == {}\n\n====",
        src
    );
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = match lower_result.module {
        Some(m) => m,
        None => return Err(format!("Parse error: {:?}", lower_result.errors)),
    };

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    ctx.eval_op("Op").map_err(|e| format!("{:?}", e))
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_restrict_function() {
    // Restrict([x \in {1, 2, 3} |-> x * 2], {1, 2}) should give [x \in {1, 2} |-> x * 2]
    let result = eval_functions_str("Restrict([x \\in {1, 2, 3} |-> x * 2], {1, 2})").unwrap();
    if let Value::Func(ref f) = result {
        assert_eq!(f.domain_len(), 2);
        assert!(f.domain_contains(&Value::int(1)));
        assert!(f.domain_contains(&Value::int(2)));
        assert!(!f.domain_contains(&Value::int(3)));
        assert_eq!(f.mapping_get(&Value::int(1)), Some(&Value::int(2)));
        assert_eq!(f.mapping_get(&Value::int(2)), Some(&Value::int(4)));
    } else {
        panic!("Expected Func value, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_restrict_empty() {
    // Restrict(f, {}) = <<>> (empty function)
    let result = eval_functions_str("Restrict([x \\in {1, 2} |-> x], {})").unwrap();
    if let Value::Func(ref f) = result {
        assert_eq!(f.domain_len(), 0);
    } else {
        panic!("Expected Func value, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_injective_true() {
    // [1 |-> "a", 2 |-> "b"] is injective (different inputs map to different outputs)
    let result =
        eval_functions_str(r#"IsInjective([x \in {1, 2} |-> IF x = 1 THEN "a" ELSE "b"])"#)
            .unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_injective_false() {
    // [1 |-> "a", 2 |-> "a"] is NOT injective (different inputs map to same output)
    let result = eval_functions_str(r#"IsInjective([x \in {1, 2} |-> "a"])"#).unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_injective_sequence_true() {
    let result = eval_functions_str(r#"IsInjective(<<"a", "b", "c">>)"#).unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_injective_sequence_false() {
    let result = eval_functions_str(r#"IsInjective(<<"a", "b", "a">>)"#).unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_surjective_true() {
    // f = [x \in {1, 2} |-> x] is surjective from {1, 2} to {1, 2}
    let result = eval_functions_str("IsSurjective([x \\in {1, 2} |-> x], {1, 2}, {1, 2})").unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_surjective_false() {
    // f = [x \in {1, 2} |-> 1] is NOT surjective from {1, 2} to {1, 2} (2 never hit)
    let result = eval_functions_str("IsSurjective([x \\in {1, 2} |-> 1], {1, 2}, {1, 2})").unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_bijection_true() {
    // Identity function is a bijection
    let result = eval_functions_str("IsBijection([x \\in {1, 2} |-> x], {1, 2}, {1, 2})").unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_bijection_false_not_injective() {
    // Constant function is not a bijection (not injective)
    let result = eval_functions_str("IsBijection([x \\in {1, 2} |-> 1], {1, 2}, {1, 2})").unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_identity() {
    // Inverse of identity function is identity
    let result = eval_functions_str("Inverse([x \\in {1, 2} |-> x], {1, 2}, {1, 2})").unwrap();
    if let Value::Func(ref f) = result {
        assert_eq!(f.domain_len(), 2);
        assert_eq!(f.mapping_get(&Value::int(1)), Some(&Value::int(1)));
        assert_eq!(f.mapping_get(&Value::int(2)), Some(&Value::int(2)));
    } else {
        panic!("Expected Func value, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_swap() {
    // Inverse of [1 |-> 2, 2 |-> 1] should be [2 |-> 1, 1 |-> 2]
    let result =
        eval_functions_str("Inverse([x \\in {1, 2} |-> IF x = 1 THEN 2 ELSE 1], {1, 2}, {1, 2})")
            .unwrap();
    if let Value::Func(ref f) = result {
        assert_eq!(f.mapping_get(&Value::int(1)), Some(&Value::int(2)));
        assert_eq!(f.mapping_get(&Value::int(2)), Some(&Value::int(1)));
    } else {
        panic!("Expected Func value, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_function() {
    // Range([x \in {1, 2} |-> x + 10]) = {11, 12}
    let result = eval_functions_str("Range([x \\in {1, 2} |-> x + 10])").unwrap();
    assert_eq!(result, int_set(&[11, 12]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_range_sequence() {
    let result = eval_functions_str("Range(<<1, 2, 2>>)").unwrap();
    assert_eq!(result, int_set(&[1, 2]));
}

// New Functions module operators: RestrictDomain, RestrictValues, IsRestriction, Pointwise, AntiFunction

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_restrict_domain() {
    // RestrictDomain(f, P) restricts function to domain elements satisfying P
    let module_src = r#"---- MODULE Test ----
EXTENDS Functions

f == [x \in {1, 2, 3, 4} |-> x * 2]
IsEven(x) == x % 2 = 0
Op == RestrictDomain(f, LAMBDA x: IsEven(x))

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();
    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    if let Value::Func(ref f) = result {
        assert_eq!(f.domain_len(), 2);
        assert!(f.domain_contains(&Value::int(2)));
        assert!(f.domain_contains(&Value::int(4)));
        assert!(!f.domain_contains(&Value::int(1)));
        assert!(!f.domain_contains(&Value::int(3)));
    } else {
        panic!("Expected Func, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_restrict_values() {
    // RestrictValues(f, P) restricts function to keys whose values satisfy P
    let module_src = r#"---- MODULE Test ----
EXTENDS Functions

f == [x \in {1, 2, 3, 4} |-> x * 2]
IsGt5(y) == y > 5
Op == RestrictValues(f, LAMBDA y: IsGt5(y))

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();
    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    if let Value::Func(ref f) = result {
        // f[3] = 6, f[4] = 8 are > 5
        assert_eq!(f.domain_len(), 2);
        assert!(f.domain_contains(&Value::int(3)));
        assert!(f.domain_contains(&Value::int(4)));
    } else {
        panic!("Expected Func, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_restriction_true() {
    // IsRestriction([x \in {1} |-> x], [x \in {1, 2} |-> x]) = TRUE
    let result =
        eval_functions_str("IsRestriction([x \\in {1} |-> x], [x \\in {1, 2} |-> x])").unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_restriction_false_domain() {
    // IsRestriction fails if domain not a subset
    let result =
        eval_functions_str("IsRestriction([x \\in {1, 3} |-> x], [x \\in {1, 2} |-> x])").unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_is_restriction_false_values() {
    // IsRestriction fails if values differ
    let result =
        eval_functions_str("IsRestriction([x \\in {1} |-> x + 1], [x \\in {1, 2} |-> x])").unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_pointwise() {
    // Pointwise(Op, f, g) combines functions pointwise
    let module_src = r#"---- MODULE Test ----
EXTENDS Functions

Add(a, b) == a + b
f == [x \in {1, 2} |-> x]
g == [x \in {1, 2} |-> x * 10]
Op == Pointwise(Add, f, g)

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();
    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    if let Value::Func(ref f) = result {
        // f[1] = 1 + 10 = 11, f[2] = 2 + 20 = 22
        assert_eq!(f.mapping_get(&Value::int(1)), Some(&Value::int(11)));
        assert_eq!(f.mapping_get(&Value::int(2)), Some(&Value::int(22)));
    } else {
        panic!("Expected Func, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_anti_function() {
    // AntiFunction reverses key-value pairs
    let result = eval_functions_str("AntiFunction([x \\in {1, 2} |-> x * 10])").unwrap();
    if let Value::Func(ref f) = result {
        // {10 -> 1, 20 -> 2}
        assert_eq!(f.mapping_get(&Value::int(10)), Some(&Value::int(1)));
        assert_eq!(f.mapping_get(&Value::int(20)), Some(&Value::int(2)));
    } else {
        panic!("Expected Func, got {:?}", result);
    }
}

// ============================================================================
// Functions - Injection, Surjection, Bijection, Exists*
// ============================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_injection_set() {
    // Injection({1, 2}, {a, b, c}) should have 6 elements (3 * 2 = 6 injective functions)
    let result = eval_functions_str(r#"Cardinality(Injection({1, 2}, {"a", "b", "c"}))"#).unwrap();
    assert_eq!(result, Value::int(6));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_injection_too_large_source() {
    // Injection({1, 2, 3}, {a, b}) should be empty (no injection possible)
    let result = eval_functions_str(r#"Injection({1, 2, 3}, {"a", "b"})"#).unwrap();
    assert_eq!(result, Value::Set(Arc::new(SortedSet::new())));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bijection_set() {
    // Bijection({1, 2}, {a, b}) should have 2 elements (2! = 2)
    let result = eval_functions_str(r#"Cardinality(Bijection({1, 2}, {"a", "b"}))"#).unwrap();
    assert_eq!(result, Value::int(2));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bijection_different_cardinality() {
    // Bijection({1, 2}, {a, b, c}) should be empty (cardinalities differ)
    let result = eval_functions_str(r#"Bijection({1, 2}, {"a", "b", "c"})"#).unwrap();
    assert_eq!(result, Value::Set(Arc::new(SortedSet::new())));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_surjection_set() {
    // Surjection({1, 2}, {a}) should have 1 element (both map to "a")
    let result = eval_functions_str(r#"Cardinality(Surjection({1, 2}, {"a"}))"#).unwrap();
    assert_eq!(result, Value::int(1));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_surjection_too_small_source() {
    // Surjection({1}, {a, b}) should be empty (no surjection possible)
    let result = eval_functions_str(r#"Surjection({1}, {"a", "b"})"#).unwrap();
    assert_eq!(result, Value::Set(Arc::new(SortedSet::new())));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_injection_true() {
    // ExistsInjection({1, 2}, {a, b, c}) = TRUE
    let result = eval_functions_str(r#"ExistsInjection({1, 2}, {"a", "b", "c"})"#).unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_injection_false() {
    // ExistsInjection({1, 2, 3}, {a, b}) = FALSE
    let result = eval_functions_str(r#"ExistsInjection({1, 2, 3}, {"a", "b"})"#).unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_surjection_true() {
    // ExistsSurjection({1, 2, 3}, {a, b}) = TRUE
    let result = eval_functions_str(r#"ExistsSurjection({1, 2, 3}, {"a", "b"})"#).unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_surjection_false() {
    // ExistsSurjection({1}, {a, b}) = FALSE
    let result = eval_functions_str(r#"ExistsSurjection({1}, {"a", "b"})"#).unwrap();
    assert_eq!(result, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_bijection_true() {
    // ExistsBijection({1, 2}, {a, b}) = TRUE
    let result = eval_functions_str(r#"ExistsBijection({1, 2}, {"a", "b"})"#).unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_exists_bijection_false() {
    // ExistsBijection({1, 2, 3}, {a, b}) = FALSE
    let result = eval_functions_str(r#"ExistsBijection({1, 2, 3}, {"a", "b"})"#).unwrap();
    assert_eq!(result, Value::Bool(false));
}

// ── Performance proof tests (Part of #2370) ──────────────────────────

/// Performance proof: Inverse with larger domain exercises O(|T|*|entries|) scan.
///
/// The current implementation at builtin_functions.rs:172-177 uses `.find()`
/// inside a `for t in target` loop, giving O(|T| * |entries| * log|S|).
/// A pre-built reverse HashMap would be O(|entries| + |T|).
///
/// This test verifies correctness with a 6-element bijection. Any future
/// optimization must preserve these results.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_inverse_larger_domain() {
    // Build a 6-element permutation [1->6, 2->5, 3->4, 4->3, 5->2, 6->1]
    // Its inverse should be the same mapping.
    let result = eval_functions_str("Inverse([x \\in 1..6 |-> 7 - x], 1..6, 1..6)").unwrap();
    if let Value::Func(ref f) = result {
        assert_eq!(f.domain_len(), 6, "Inverse should have 6 domain elements");
        for i in 1..=6 {
            let expected = 7 - i;
            assert_eq!(
                f.mapping_get(&Value::int(i)),
                Some(&Value::int(expected)),
                "Inverse[{}] should be {}, but got {:?}",
                i,
                expected,
                f.mapping_get(&Value::int(i))
            );
        }
    } else {
        panic!("Expected Func value, got {:?}", result);
    }
}

/// Performance proof: Injection set generation with non-trivial domain.
///
/// Injection({1,2,3}, {1,2,3,4}) should produce P(4,3) = 4!/1! = 24 injections.
/// This exercises the `generate_injections` recursive function which clones
/// OrdMap+OrdSet at every leaf (24 leaves here).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_injection_set_nontrivial_size() {
    let result = eval_functions_str("Cardinality(Injection(1..3, 1..4))").unwrap();
    // P(4,3) = 4! / (4-3)! = 24
    assert_eq!(
        result,
        Value::int(24),
        "Injection(1..3, 1..4) should have 24 elements (P(4,3))"
    );
}

/// Performance proof: Surjection set generation with non-trivial domain.
///
/// Surjection({1,2,3}, {1,2}) should produce surjections from 3->2.
/// Total functions: 2^3 = 8. Non-surjections: 2 (all-to-1, all-to-2).
/// Surjections: 6.
///
/// The current implementation at builtin_functions.rs:290-320 generates
/// ALL |T|^|S| functions and filters. At each leaf of the recursion tree,
/// it clones current_mapping and rebuilds a range OrdSet to check coverage.
/// With |S|=3, |T|=2 this is 8 leaves — manageable but exponential.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_surjection_set_nontrivial_size() {
    let result = eval_functions_str("Cardinality(Surjection(1..3, 1..2))").unwrap();
    // |T|^|S| - non-surjections = 2^3 - 2 = 6
    assert_eq!(
        result,
        Value::int(6),
        "Surjection(1..3, 1..2) should have 6 elements"
    );
}
