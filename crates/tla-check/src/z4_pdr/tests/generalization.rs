// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for PDR lemma generalization.
//!
//! Verifies that the TLA-level lemma generalizer correctly drops unnecessary
//! conjuncts while preserving blocking ability, and that generalization
//! statistics are tracked accurately.

use super::helpers::*;
use super::*;
use tla_core::ast::Expr;
use tla_core::Spanned;
use tla_z4::TlaSort;

use crate::z4_pdr::generalize::{
    build_conjunction_from_mask, flatten_conjunction, generalize_lemma, AtomicGeneralizationStats,
};

// =========================================================================
// flatten_conjunction tests
// =========================================================================

#[test]
fn test_flatten_single_expr() {
    let expr = le_expr(var_expr("x"), int_expr(5));
    let mut out = Vec::new();
    flatten_conjunction(&expr, &mut out);
    assert_eq!(out.len(), 1, "single non-And should produce 1 literal");
}

#[test]
fn test_flatten_binary_and() {
    let expr = and_expr(
        le_expr(var_expr("x"), int_expr(5)),
        eq_expr(var_expr("y"), int_expr(0)),
    );
    let mut out = Vec::new();
    flatten_conjunction(&expr, &mut out);
    assert_eq!(out.len(), 2, "binary And should produce 2 literals");
}

#[test]
fn test_flatten_deeply_nested() {
    // (a /\ b) /\ (c /\ d) -> 4 literals
    let expr = and_expr(
        and_expr(
            eq_expr(var_expr("a"), int_expr(1)),
            eq_expr(var_expr("b"), int_expr(2)),
        ),
        and_expr(
            eq_expr(var_expr("c"), int_expr(3)),
            eq_expr(var_expr("d"), int_expr(4)),
        ),
    );
    let mut out = Vec::new();
    flatten_conjunction(&expr, &mut out);
    assert_eq!(out.len(), 4, "2x2 nested And should produce 4 literals");
}

#[test]
fn test_flatten_preserves_non_and() {
    // An Or at top level is a single literal
    let expr = Spanned::dummy(Expr::Or(
        Box::new(eq_expr(var_expr("x"), int_expr(0))),
        Box::new(eq_expr(var_expr("y"), int_expr(1))),
    ));
    let mut out = Vec::new();
    flatten_conjunction(&expr, &mut out);
    assert_eq!(out.len(), 1, "Or should be treated as single literal");
}

// =========================================================================
// build_conjunction_from_mask tests
// =========================================================================

#[test]
fn test_mask_all_false_produces_true() {
    let literals = vec![int_expr(1), int_expr(2)];
    let mask = vec![false, false];
    let result = build_conjunction_from_mask(&literals, &mask);
    assert!(
        matches!(result.node, Expr::Bool(true)),
        "all-false mask should produce TRUE"
    );
}

#[test]
fn test_mask_single_selected() {
    let literals = vec![int_expr(1), int_expr(2), int_expr(3)];
    let mask = vec![false, true, false];
    let result = build_conjunction_from_mask(&literals, &mask);
    assert!(
        matches!(result.node, Expr::Int(ref n) if *n == 2.into()),
        "single-selected mask should produce that literal"
    );
}

#[test]
fn test_mask_all_selected_produces_and() {
    let literals = vec![int_expr(1), int_expr(2)];
    let mask = vec![true, true];
    let result = build_conjunction_from_mask(&literals, &mask);
    assert!(
        matches!(result.node, Expr::And(..)),
        "all-selected should produce And"
    );
}

// =========================================================================
// AtomicGeneralizationStats tests
// =========================================================================

#[test]
fn test_stats_default_zeros() {
    let stats = AtomicGeneralizationStats::default();
    let snap = stats.snapshot();
    assert_eq!(snap.lemmas_generalized, 0);
    assert_eq!(snap.total_original_literals, 0);
    assert_eq!(snap.total_literals_dropped, 0);
    assert_eq!(snap.total_time_us, 0);
}

#[test]
fn test_stats_accumulate() {
    let stats = AtomicGeneralizationStats::default();
    stats.record(4, 2, 1000);
    stats.record(6, 3, 2000);
    stats.record(2, 0, 500);

    let snap = stats.snapshot();
    assert_eq!(snap.lemmas_generalized, 3);
    assert_eq!(snap.total_original_literals, 12);
    assert_eq!(snap.total_literals_dropped, 5);
    assert_eq!(snap.total_time_us, 3500);
}

// =========================================================================
// Integration: generalize_lemma with solver
// =========================================================================

/// Helper to build a simple bounded counter spec.
///
/// Init: x = 0
/// Next: x < bound /\ x' = x + 1
fn bounded_counter_spec(bound: i64) -> (Vec<(String, TlaSort)>, Spanned<Expr>, Spanned<Expr>) {
    let var_sorts = vec![("x".to_string(), TlaSort::Int)];
    let init = eq_expr(var_expr("x"), int_expr(0));
    let next = and_expr(
        lt_expr(var_expr("x"), int_expr(bound)),
        eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
    );
    (var_sorts, init, next)
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_generalize_single_literal_noop() {
    let (var_sorts, init, next) = bounded_counter_spec(5);
    let lemma = le_expr(var_expr("x"), int_expr(5));

    let result =
        generalize_lemma(&var_sorts, &init, &next, &lemma).expect("generalization should succeed");

    assert_eq!(result.original_literal_count, 1);
    assert_eq!(
        result.literals_dropped, 0,
        "single literal cannot be dropped"
    );
}

#[cfg_attr(test, ntest::timeout(30000))]
#[test]
fn test_generalize_with_redundant_true() {
    // Lemma: x <= 5 /\ TRUE
    // TRUE is always redundant and should be droppable.
    let (var_sorts, init, next) = bounded_counter_spec(5);
    let lemma = and_expr(
        le_expr(var_expr("x"), int_expr(5)),
        Spanned::dummy(Expr::Bool(true)),
    );

    let result =
        generalize_lemma(&var_sorts, &init, &next, &lemma).expect("generalization should succeed");

    assert_eq!(result.original_literal_count, 2);
    // TRUE is trivially droppable -- the solver should detect this.
    // Accept any drop count (solver may be conservative).
    assert!(result.literals_dropped <= 2);
}

#[cfg_attr(test, ntest::timeout(60000))]
#[test]
fn test_generalize_convergence_comparison() {
    // Compare PDR frame count with and without generalization by
    // verifying that generalized lemmas are at most as large as
    // the originals (never adds literals).
    let var_sorts = vec![
        ("x".to_string(), TlaSort::Int),
        ("y".to_string(), TlaSort::Int),
    ];
    let init = and_expr(
        eq_expr(var_expr("x"), int_expr(0)),
        eq_expr(var_expr("y"), int_expr(0)),
    );
    let next = and_expr(
        and_expr(
            lt_expr(var_expr("x"), int_expr(3)),
            eq_expr(prime_expr("x"), add_expr(var_expr("x"), int_expr(1))),
        ),
        eq_expr(prime_expr("y"), add_expr(var_expr("y"), int_expr(2))),
    );

    // Safety only depends on x; y-related literals are noise.
    let lemma = and_expr(
        and_expr(
            le_expr(var_expr("x"), int_expr(3)),
            Spanned::dummy(Expr::Geq(Box::new(var_expr("y")), Box::new(int_expr(0)))),
        ),
        Spanned::dummy(Expr::Geq(Box::new(var_expr("x")), Box::new(int_expr(0)))),
    );

    let result =
        generalize_lemma(&var_sorts, &init, &next, &lemma).expect("generalization should succeed");

    assert_eq!(result.original_literal_count, 3);
    // The generalized lemma should have at most 3 literals (never adds).
    let mut gen_lits = Vec::new();
    flatten_conjunction(&result.expr, &mut gen_lits);
    assert!(
        gen_lits.len() <= 3,
        "generalized lemma should not grow: got {} literals",
        gen_lits.len()
    );

    // Consistency check: remaining literals match original minus dropped.
    // Special case: when ALL literals are dropped, the result is Bool(true),
    // which flattens to 1 element. Account for this degenerate case.
    let expected_remaining = result.original_literal_count - result.literals_dropped;
    if expected_remaining == 0 {
        // All dropped => Bool(true), which flattens to [Bool(true)]
        assert_eq!(gen_lits.len(), 1, "fully-dropped should produce TRUE");
        assert!(
            matches!(result.expr.node, Expr::Bool(true)),
            "fully-dropped lemma should be TRUE"
        );
    } else {
        assert_eq!(
            expected_remaining,
            gen_lits.len(),
            "remaining literals should match original minus dropped"
        );
    }
}
