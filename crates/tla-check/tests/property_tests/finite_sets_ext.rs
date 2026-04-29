// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! FiniteSetsExt operator tests - consolidated from scattered sections of property_tests.rs

use tla_check::Value;
use tla_core::{lower, parse_to_syntax_tree, FileId};

use super::helpers::int_set;

// ============================================================================
// Helper: eval with EXTENDS FiniteSets, FiniteSetsExt
// ============================================================================

fn eval_fsext_str(src: &str) -> Result<Value, String> {
    let module_src = format!(
        "---- MODULE Test ----\nEXTENDS FiniteSets, FiniteSetsExt\n\nOp == {}\n\n====",
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

// ============================================================================
// Helper: eval with EXTENDS FiniteSetsExt (only)
// ============================================================================

/// Helper to evaluate with FiniteSetsExt module
fn eval_finitesetsext_str(src: &str) -> Result<Value, String> {
    let module_src = format!(
        "---- MODULE Test ----\nEXTENDS FiniteSetsExt\n\nOp == {}\n\n====",
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

// ============================================================================
// Core FiniteSetsExt operators (Quantify, Ksubsets, SymDiff, Flatten,
// Choose, Sum, Product)
// ============================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_quantify() {
    // Quantify counts elements satisfying predicate
    let module_src = r#"---- MODULE Test ----
EXTENDS FiniteSets, FiniteSetsExt

IsEven(x) == x % 2 = 0
Op == Quantify({1, 2, 3, 4, 5, 6}, IsEven)

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    assert_eq!(result, Value::int(3)); // 2, 4, 6 are even
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubsets() {
    // Ksubsets returns a lazy KSubsetValue (or Set for empty cases)
    let result = eval_fsext_str("Ksubsets({1, 2, 3}, 2)").unwrap();
    // Convert lazy value to set for comparison
    let s = result
        .to_sorted_set()
        .expect("Should be convertible to set");
    assert_eq!(s.len(), 3); // C(3,2) = 3
                            // Check that each element is a 2-element set
    for elem in &s {
        if let Value::Set(ref inner) = elem {
            assert_eq!(inner.len(), 2);
        } else {
            panic!("Expected Set value in Ksubsets result, got {:?}", elem);
        }
    }

    // k > n returns KSubset with empty enumeration
    let result = eval_fsext_str("Ksubsets({1, 2}, 5)").unwrap();
    let s = result
        .to_sorted_set()
        .expect("Should be convertible to set");
    assert!(s.is_empty());

    // k = 0 returns KSubset containing just empty set
    let result = eval_fsext_str("Ksubsets({1, 2, 3}, 0)").unwrap();
    let s = result
        .to_sorted_set()
        .expect("Should be convertible to set");
    assert_eq!(s.len(), 1);
    // The single element should be the empty set
    let elem = s.iter().next().unwrap();
    assert_eq!(elem, &Value::set(vec![]));
}

/// Part of #2224: kSubset negative k must error (TLC throws IllegalArgumentException).
/// Previously, `-1_i64 as usize` wrapped to usize::MAX, producing wrong results or OOM.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubsets_negative_k_errors() {
    // Negative k should produce an ArgumentError, matching TLC's IllegalArgumentException
    let result = eval_fsext_str("Ksubsets({1, 2, 3}, -1)");
    assert!(
        result.is_err(),
        "Ksubsets with negative k should error, got: {:?}",
        result
    );
    let err = result.unwrap_err();
    assert!(
        err.contains("non-negative"),
        "Error should mention non-negative, got: {err}"
    );

    // Large negative k should also error
    let result = eval_fsext_str("Ksubsets({1, 2}, -100)");
    assert!(result.is_err(), "Large negative k should error");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sym_diff() {
    // SymDiff is symmetric difference
    let result = eval_fsext_str("SymDiff({1, 2, 3}, {2, 3, 4})").unwrap();
    assert_eq!(result, int_set(&[1, 4])); // {1} ∪ {4}

    // SymDiff of identical sets is empty
    let result = eval_fsext_str("SymDiff({1, 2, 3}, {1, 2, 3})").unwrap();
    assert_eq!(result, int_set(&[]));

    // SymDiff of disjoint sets is their union
    let result = eval_fsext_str("SymDiff({1, 2}, {3, 4})").unwrap();
    assert_eq!(result, int_set(&[1, 2, 3, 4]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_flatten() {
    // Flatten is union of set of sets
    let result = eval_fsext_str("Flatten({{1, 2}, {2, 3}, {4}})").unwrap();
    assert_eq!(result, int_set(&[1, 2, 3, 4]));

    // Flatten of empty set is empty
    let result = eval_fsext_str("Flatten({})").unwrap();
    assert_eq!(result, int_set(&[]));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose() {
    // Choose returns an element from the set
    let result = eval_fsext_str("Choose({1, 2, 3}) \\in {1, 2, 3}").unwrap();
    assert_eq!(result, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_sum() {
    // Sum adds all elements
    let result = eval_fsext_str("Sum({1, 2, 3, 4})").unwrap();
    assert_eq!(result, Value::int(10));

    // Sum of empty set is 0
    let result = eval_fsext_str("Sum({})").unwrap();
    assert_eq!(result, Value::int(0));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_product() {
    // Product multiplies all elements
    let result = eval_fsext_str("Product({1, 2, 3, 4})").unwrap();
    assert_eq!(result, Value::int(24));

    // Product of empty set is 1
    let result = eval_fsext_str("Product({})").unwrap();
    assert_eq!(result, Value::int(1));
}

// ============================================================================
// ReduceSet tests
// ============================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reduceset() {
    // ReduceSet(op, S, base) - like FoldSet but different arg order
    let module_src = r#"---- MODULE Test ----
EXTENDS FiniteSets, FiniteSetsExt

Add(a, b) == a + b
Op == ReduceSet(Add, {1, 2, 3}, 0)

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    assert_eq!(result, Value::int(6));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_reduceset_empty() {
    // ReduceSet on empty set returns base
    let module_src = r#"---- MODULE Test ----
EXTENDS FiniteSets, FiniteSetsExt

Add(a, b) == a + b
Op == ReduceSet(Add, {}, 100)

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();

    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    assert_eq!(result, Value::int(100));
}

// ============================================================================
// Mean test
// ============================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_mean() {
    // Mean of a set of integers
    let result = eval_fsext_str("Mean({1, 2, 3, 4, 5})").unwrap();
    assert_eq!(result, Value::int(3)); // (1+2+3+4+5)/5 = 15/5 = 3

    // Mean with integer division (floor)
    let result = eval_fsext_str("Mean({1, 2})").unwrap();
    assert_eq!(result, Value::int(1)); // (1+2)/2 = 3/2 = 1 (floor)
}

// ============================================================================
// MapThenSumSet, Choices, ChooseUnique (use eval_finitesetsext_str)
// ============================================================================

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_map_then_sum_set() {
    // MapThenSumSet(Op, S) maps unary operator over S and sums results
    let module_src = r#"---- MODULE Test ----
EXTENDS FiniteSetsExt

Double(x) == x * 2
Op == MapThenSumSet(Double, {1, 2, 3})

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();
    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    // Double(1) + Double(2) + Double(3) = 2 + 4 + 6 = 12
    assert_eq!(result, Value::int(12));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_map_then_sum_set_empty() {
    // MapThenSumSet on empty set = 0
    let module_src = r#"---- MODULE Test ----
EXTENDS FiniteSetsExt

Id(x) == x
Op == MapThenSumSet(Id, {})

===="#;
    let tree = parse_to_syntax_tree(module_src);
    let lower_result = lower(FileId(0), &tree);
    let module = lower_result.module.unwrap();
    let mut ctx = tla_check::EvalCtx::new();
    ctx.load_module(&module);
    let result = ctx.eval_op("Op").unwrap();
    assert_eq!(result, Value::int(0));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choices_basic() {
    // Choices({{1}, {2}}) has 1 choice function: [S1 -> 1, S2 -> 2]
    let result = eval_finitesetsext_str("Choices({{1}, {2}})").unwrap();
    if let Value::Set(ref s) = result {
        assert_eq!(s.len(), 1);
    } else {
        panic!("Expected Set, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choices_multiple() {
    // Choices({{1, 2}, {3}}) has 2 choice functions
    let result = eval_finitesetsext_str("Choices({{1, 2}, {3}})").unwrap();
    if let Value::Set(ref s) = result {
        assert_eq!(s.len(), 2);
    } else {
        panic!("Expected Set, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choices_empty_set() {
    // Choices({}) = one empty function
    let result = eval_finitesetsext_str("Choices({})").unwrap();
    if let Value::Set(ref s) = result {
        assert_eq!(s.len(), 1);
    } else {
        panic!("Expected Set, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choices_contains_empty() {
    // Choices({{}, {1}}) = {} because one set is empty
    let result = eval_finitesetsext_str("Choices({{}, {1}})").unwrap();
    if let Value::Set(ref s) = result {
        assert_eq!(s.len(), 0);
    } else {
        panic!("Expected Set, got {:?}", result);
    }
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_choose_unique() {
    // ChooseUnique({1, 2, 3}, LAMBDA x: x = 2) = 2
    let result = eval_finitesetsext_str("ChooseUnique({1, 2, 3}, LAMBDA x: x = 2)").unwrap();
    assert_eq!(result, Value::int(2));
}
