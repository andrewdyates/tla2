// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for #3907: K-subset direct generation optimization.
//!
//! The pattern `{x \in SUBSET(S) : Cardinality(x) = k}` is detected during
//! TIR lowering and compiled to `TirExpr::KSubset` which constructs a
//! `KSubsetValue` directly, generating only C(n,k) subsets instead of
//! filtering all 2^n powerset elements.

use super::*;
use crate::tir::eval_tir;
use tla_core::ast::{Expr, Module, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId, Spanned};
use tla_tir::{lower_expr, TirExpr};

fn parse_module(src: &str) -> Module {
    let tree = parse_to_syntax_tree(src);
    let lower_result = lower(FileId(0), &tree);
    assert!(
        lower_result.errors.is_empty(),
        "lower errors for module:\n{src}\n{:?}",
        lower_result.errors
    );
    lower_result.module.expect("module should lower")
}

fn find_operator_body<'a>(module: &'a Module, name: &str) -> &'a Spanned<Expr> {
    module
        .units
        .iter()
        .find_map(|unit| match &unit.node {
            Unit::Operator(def) if def.name.node == name => Some(&def.body),
            _ => None,
        })
        .unwrap_or_else(|| panic!("operator '{name}' should exist"))
}

fn ast_value_for_named_op(module: &Module, name: &str) -> Value {
    clear_for_test_reset();
    let mut ctx = EvalCtx::new();
    ctx.load_module(module);
    ctx.eval_op(name)
        .unwrap_or_else(|err| panic!("AST eval of '{name}' should succeed: {err:?}"))
}

fn tir_value_for_expr(module: &Module, expr: &Spanned<Expr>) -> Value {
    clear_for_test_reset();
    let lowered = lower_expr(module, expr).expect("expression should lower to TIR");
    let mut ctx = EvalCtx::new();
    ctx.load_module(module);
    eval_tir(&ctx, &lowered).expect("TIR expression should evaluate")
}

/// Returns true if the lowered TIR for the given operator contains a
/// `TirExpr::KSubset` node (proving the pattern was detected).
fn tir_contains_ksubset(module: &Module, name: &str) -> bool {
    let body = find_operator_body(module, name);
    match lower_expr(module, body) {
        Ok(lowered) => contains_ksubset_node(&lowered.node),
        Err(_) => false,
    }
}

fn contains_ksubset_node(expr: &TirExpr) -> bool {
    match expr {
        TirExpr::KSubset { .. } => true,
        TirExpr::Cmp { left, right, .. } => {
            contains_ksubset_node(&left.node) || contains_ksubset_node(&right.node)
        }
        TirExpr::SetFilter { body, .. } => contains_ksubset_node(&body.node),
        TirExpr::Let { body, defs } => {
            contains_ksubset_node(&body.node)
                || defs.iter().any(|d| contains_ksubset_node(&d.body.node))
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Pattern detection: TIR lowerer should emit KSubset
// ---------------------------------------------------------------------------

const KSUBSET_BASIC_MODULE: &str = r#"
---- MODULE KSubsetBasic ----
EXTENDS FiniteSets

\* Standard pattern: Cardinality(x) = k
K2of3 == {x \in SUBSET {1, 2, 3} : Cardinality(x) = 2}

\* Reversed: k = Cardinality(x)
K2of3Rev == {x \in SUBSET {1, 2, 3} : 2 = Cardinality(x)}

\* k = 0: should produce {{}}
K0of3 == {x \in SUBSET {1, 2, 3} : Cardinality(x) = 0}

\* k = |S|: should produce {{1,2,3}}
K3of3 == {x \in SUBSET {1, 2, 3} : Cardinality(x) = 3}

\* k > |S|: should produce {}
K4of3 == {x \in SUBSET {1, 2, 3} : Cardinality(x) = 4}

\* k = 1: singletons
K1of3 == {x \in SUBSET {1, 2, 3} : Cardinality(x) = 1}

====
"#;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_tir_lowering_detects_pattern() {
    let module = parse_module(KSUBSET_BASIC_MODULE);
    assert!(
        tir_contains_ksubset(&module, "K2of3"),
        "TIR lowerer should detect Cardinality(x) = k pattern and emit KSubset"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_tir_lowering_detects_reversed_pattern() {
    let module = parse_module(KSUBSET_BASIC_MODULE);
    assert!(
        tir_contains_ksubset(&module, "K2of3Rev"),
        "TIR lowerer should detect k = Cardinality(x) reversed pattern"
    );
}

// ---------------------------------------------------------------------------
// Correctness: TIR KSubset produces the same values as AST tree-walking
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_k2_of_3_correct() {
    let module = parse_module(KSUBSET_BASIC_MODULE);
    let ast_val = ast_value_for_named_op(&module, "K2of3");
    let tir_val = tir_value_for_expr(&module, find_operator_body(&module, "K2of3"));
    // Both should equal {{1,2}, {1,3}, {2,3}}
    assert_eq!(
        tir_val, ast_val,
        "TIR KSubset and AST tree-walking should produce identical results for C(3,2)"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_reversed_eq_correct() {
    let module = parse_module(KSUBSET_BASIC_MODULE);
    let ast_val = ast_value_for_named_op(&module, "K2of3Rev");
    let tir_val = tir_value_for_expr(&module, find_operator_body(&module, "K2of3Rev"));
    assert_eq!(
        tir_val, ast_val,
        "reversed equality (k = Cardinality(x)) should produce same result"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_k0_produces_empty_set_singleton() {
    let module = parse_module(KSUBSET_BASIC_MODULE);
    let ast_val = ast_value_for_named_op(&module, "K0of3");
    let tir_val = tir_value_for_expr(&module, find_operator_body(&module, "K0of3"));
    // C(3,0) = 1 subset (the empty set)
    assert_eq!(tir_val, ast_val, "k=0 should produce the set containing empty set");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_k_equals_n_produces_full_set() {
    let module = parse_module(KSUBSET_BASIC_MODULE);
    let ast_val = ast_value_for_named_op(&module, "K3of3");
    let tir_val = tir_value_for_expr(&module, find_operator_body(&module, "K3of3"));
    // C(3,3) = 1 subset ({1,2,3})
    assert_eq!(
        tir_val, ast_val,
        "k=|S| should produce set containing the full set"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_k_greater_than_n_produces_empty() {
    let module = parse_module(KSUBSET_BASIC_MODULE);
    let ast_val = ast_value_for_named_op(&module, "K4of3");
    let tir_val = tir_value_for_expr(&module, find_operator_body(&module, "K4of3"));
    // C(3,4) = 0 subsets
    assert_eq!(
        tir_val, ast_val,
        "k>|S| should produce empty set of subsets"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_k1_singletons_correct() {
    let module = parse_module(KSUBSET_BASIC_MODULE);
    let ast_val = ast_value_for_named_op(&module, "K1of3");
    let tir_val = tir_value_for_expr(&module, find_operator_body(&module, "K1of3"));
    // C(3,1) = 3 subsets: {{1}, {2}, {3}}
    assert_eq!(
        tir_val, ast_val,
        "k=1 should produce singleton subsets"
    );
}

// ---------------------------------------------------------------------------
// End-to-end through eval_with_ops (AST path with existing optimization)
// ---------------------------------------------------------------------------

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_cardinality_count() {
    // Verify the count matches C(4,2) = 6
    let v = eval_with_ops(
        "EXTENDS FiniteSets",
        "Cardinality({x \\in SUBSET {1, 2, 3, 4} : Cardinality(x) = 2})",
    )
    .unwrap();
    assert_eq!(v, Value::SmallInt(6), "C(4,2) = 6");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_membership() {
    // Verify specific membership
    let v = eval_with_ops(
        "EXTENDS FiniteSets",
        "{1, 3} \\in {x \\in SUBSET {1, 2, 3} : Cardinality(x) = 2}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_non_membership() {
    // {1,2,3} has cardinality 3, not 2
    let v = eval_with_ops(
        "EXTENDS FiniteSets",
        "{1, 2, 3} \\in {x \\in SUBSET {1, 2, 3} : Cardinality(x) = 2}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_equality_with_explicit_set() {
    // Exact equality check
    let v = eval_with_ops(
        "EXTENDS FiniteSets",
        "{x \\in SUBSET {1, 2, 3} : Cardinality(x) = 2} = {{1, 2}, {1, 3}, {2, 3}}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_empty_base_set() {
    // SUBSET {} = {{}}, C(0,0) = 1
    let v = eval_with_ops(
        "EXTENDS FiniteSets",
        "{x \\in SUBSET {} : Cardinality(x) = 0} = {{}}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true), "C(0,0)=1: only the empty set");
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_ksubset_empty_base_k1() {
    // SUBSET {} = {{}}, and no element has cardinality 1
    let v = eval_with_ops(
        "EXTENDS FiniteSets",
        "{x \\in SUBSET {} : Cardinality(x) = 1} = {}",
    )
    .unwrap();
    assert_eq!(v, Value::Bool(true), "C(0,1)=0: no 1-subsets of empty set");
}
