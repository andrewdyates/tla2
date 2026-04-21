// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TLC module operator tests (:> and @@, JavaTime, TLCGet/Set, etc.)
//!
//! Split from property_tests.rs lines 1301-1543. Part of #1371.

use num_bigint::BigInt;
use tla_check::Value;
use tla_core::{lower, parse_to_syntax_tree, FileId};

use super::helpers::int_set;

// ============================================================================
// TLC function operators (:> and @@) tests
// ============================================================================

/// Helper to evaluate with TLC module
fn eval_tlc_str(src: &str) -> Result<Value, String> {
    let module_src = format!(
        "---- MODULE Test ----\nEXTENDS TLC\n\nOp == {}\n\n====",
        src
    );
    let tree = parse_to_syntax_tree(&module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = match lower_result.module {
        Some(m) => m,
        None => return Err(format!("Parse error: {:?}", lower_result.errors)),
    };

    for unit in &module.units {
        if let tla_core::ast::Unit::Operator(def) = &unit.node {
            if def.name.node == "Op" {
                let ctx = tla_check::EvalCtx::new();
                return tla_check::eval(&ctx, &def.body).map_err(|e| format!("{:?}", e));
            }
        }
    }
    Err("Op not found".to_string())
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_make_fcn_single_element() {
    // d :> e creates [d |-> e]
    let result = eval_tlc_str("1 :> \"a\"").unwrap();
    if let Value::Func(ref f) = result {
        assert_eq!(f.domain_len(), 1);
        assert!(f.domain_contains(&Value::int(1)));
        assert_eq!(
            f.mapping_get(&Value::int(1)),
            Some(&Value::String("a".into()))
        );
    } else {
        panic!("Expected Func value, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_make_fcn_domain_application() {
    // (d :> e)[d] = e
    let result = eval_tlc_str("(1 :> \"a\")[1]").unwrap();
    assert_eq!(result, Value::String("a".into()));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_make_fcn_domain() {
    // DOMAIN (d :> e) = {d}
    let result = eval_tlc_str("DOMAIN (1 :> \"a\")").unwrap();
    assert_eq!(result, int_set(&[1]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_combine_fcn_disjoint() {
    // f @@ g with disjoint domains
    let result = eval_tlc_str("(1 :> \"a\") @@ (2 :> \"b\")").unwrap();
    if let Value::Func(ref f) = result {
        assert_eq!(f.domain_len(), 2);
        assert_eq!(
            f.mapping_get(&Value::int(1)),
            Some(&Value::String("a".into()))
        );
        assert_eq!(
            f.mapping_get(&Value::int(2)),
            Some(&Value::String("b".into()))
        );
    } else {
        panic!("Expected Func value, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_combine_fcn_priority() {
    // f @@ g with overlapping domains: f takes priority
    let result = eval_tlc_str("(1 :> \"first\") @@ (1 :> \"second\")").unwrap();
    if let Value::Func(ref f) = result {
        assert_eq!(f.domain_len(), 1);
        assert_eq!(
            f.mapping_get(&Value::int(1)),
            Some(&Value::String("first".into()))
        );
    } else {
        panic!("Expected Func value, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_combine_fcn_chain() {
    // (f @@ g) @@ h
    let result = eval_tlc_str("((1 :> \"a\") @@ (2 :> \"b\")) @@ (3 :> \"c\")").unwrap();
    if let Value::Func(ref f) = result {
        assert_eq!(f.domain_len(), 3);
        assert_eq!(
            f.mapping_get(&Value::int(1)),
            Some(&Value::String("a".into()))
        );
        assert_eq!(
            f.mapping_get(&Value::int(2)),
            Some(&Value::String("b".into()))
        );
        assert_eq!(
            f.mapping_get(&Value::int(3)),
            Some(&Value::String("c".into()))
        );
    } else {
        panic!("Expected Func value, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_combine_fcn_application() {
    // (f @@ g)[x]
    let result = eval_tlc_str("((1 :> \"a\") @@ (2 :> \"b\"))[2]").unwrap();
    assert_eq!(result, Value::String("b".into()));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_java_time() {
    // JavaTime returns a positive integer (seconds since epoch)
    let result = eval_tlc_str("JavaTime").unwrap();
    // Use to_bigint() to handle both SmallInt and Int variants
    let n = result.to_bigint().expect("Expected integer value");
    assert!(n > BigInt::from(0), "JavaTime should return positive value");
    // Should be less than 2^31 (due to MSB zeroing)
    assert!(
        n < BigInt::from(1i64 << 31),
        "JavaTime should have MSB zeroed"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_get_unset_errors() {
    // Part of #814: TLCGet now errors for unset registers (matches TLC behavior)
    let result = eval_tlc_str("TLCGet(1)");
    assert!(result.is_err(), "TLCGet on unset register should error");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_set_get_roundtrip() {
    // Part of #814: TLCSet stores value, TLCGet retrieves it
    // Uses IF to ensure TLCSet (condition) runs before TLCGet (then branch)
    // TLCSet returns TRUE, so THEN branch with TLCGet is always taken
    // Uses register 999 to avoid conflicts with other tests using register 1
    let result = eval_tlc_str("IF TLCSet(999, 42) THEN TLCGet(999) ELSE 0").unwrap();
    assert_eq!(result, Value::int(42));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_set_returns_true() {
    // TLCSet always returns TRUE
    let result = eval_tlc_str("TLCSet(1, 42)").unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_set_exit_true_requests_exit() {
    let err = eval_tlc_str("TLCSet(\"exit\", TRUE)").unwrap_err();
    assert!(
        err.contains("ExitRequested"),
        "expected ExitRequested, got {err}"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_set_exit_non_boolean_is_ignored() {
    // TLC parity: exit is triggered only by exactly TRUE.
    let result = eval_tlc_str("TLCSet(\"exit\", 42)").unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_random_element() {
    // RandomElement returns an element from the set
    let result = eval_tlc_str("RandomElement({1, 2, 3}) \\in {1, 2, 3}").unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_tlc_eval_identity() {
    // TLCEval returns its argument unchanged
    let result = eval_tlc_str("TLCEval(42)").unwrap();
    assert_eq!(result, Value::int(42));

    let result = eval_tlc_str("TLCEval({1, 2, 3})").unwrap();
    assert_eq!(result, int_set(&[1, 2, 3]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_any_returns_any_set() {
    let result = eval_tlc_str("Any").unwrap();
    assert!(matches!(result, Value::AnySet));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_any_membership() {
    let result = eval_tlc_str("42 \\in Any").unwrap();
    assert_eq!(result, Value::Bool(true));

    let result = eval_tlc_str("\"hello\" \\in Any").unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_subseteq_with_infinite_sets() {
    // Enumerable left side, non-enumerable right side.
    let result = eval_tlc_str("{1, 2} \\subseteq Any").unwrap();
    assert_eq!(result, Value::Bool(true));

    let result = eval_tlc_str("{0, 1, 2} \\subseteq Nat").unwrap();
    assert_eq!(result, Value::Bool(true));

    let result = eval_tlc_str("{-1} \\subseteq Nat").unwrap();
    assert_eq!(result, Value::Bool(false));

    // Non-enumerable left side should be an error.
    assert!(eval_tlc_str("Any \\subseteq Any").is_err());
    assert!(eval_tlc_str("Nat \\subseteq Nat").is_err());
}
