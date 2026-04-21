// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

// ── filter_non_canonical_conjuncts ──────────────────────────────────

#[test]
fn filter_non_canonical_removes_witness_conjunct() {
    let a0 = int_var("a0");
    let witness = int_var("_parity_w_a0_2");

    // a0 >= 0 AND a0 = 2 * _parity_w_a0_2 + 1
    let canonical_conj = ChcExpr::ge(ChcExpr::var(a0.clone()), ChcExpr::int(0));
    let witness_conj = ChcExpr::eq(
        ChcExpr::var(a0.clone()),
        ChcExpr::add(
            ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(witness)),
            ChcExpr::Int(1),
        ),
    );
    let formula = ChcExpr::and(canonical_conj.clone(), witness_conj);

    let result = PdrSolver::filter_non_canonical_conjuncts(&formula, &[a0]);

    // Should keep only the canonical conjunct
    let conjuncts = result.collect_conjuncts();
    assert_eq!(conjuncts.len(), 1);
    assert_eq!(conjuncts[0], canonical_conj);
}

#[test]
fn filter_non_canonical_keeps_all_canonical() {
    let a0 = int_var("a0");
    let a1 = int_var("a1");

    let c1 = ChcExpr::ge(ChcExpr::var(a0.clone()), ChcExpr::int(0));
    let c2 = ChcExpr::le(ChcExpr::var(a1.clone()), ChcExpr::int(10));
    let formula = ChcExpr::and(c1, c2);

    let result = PdrSolver::filter_non_canonical_conjuncts(&formula, &[a0, a1]);
    let conjuncts = result.collect_conjuncts();
    assert_eq!(conjuncts.len(), 2);
}

#[test]
fn filter_non_canonical_all_non_canonical_returns_true() {
    let w1 = int_var("_parity_w_a0_2");
    let w2 = int_var("_parity_w_a1_3");
    let a0 = int_var("a0");

    let c1 = ChcExpr::ge(ChcExpr::var(w1), ChcExpr::int(0));
    let c2 = ChcExpr::le(ChcExpr::var(w2), ChcExpr::int(5));
    let formula = ChcExpr::and(c1, c2);

    let result = PdrSolver::filter_non_canonical_conjuncts(&formula, &[a0]);
    assert!(matches!(result, ChcExpr::Bool(true)));
}

#[test]
fn filter_non_canonical_true_unchanged() {
    let a0 = int_var("a0");
    let formula = ChcExpr::Bool(true);
    let result = PdrSolver::filter_non_canonical_conjuncts(&formula, &[a0]);
    assert!(matches!(result, ChcExpr::Bool(true)));
}

/// Single conjunct with non-canonical var should be filtered to true.
#[test]
fn filter_non_canonical_single_conjunct_with_witness_filtered() {
    let witness = int_var("_parity_w_a0_2");
    let a0 = int_var("a0");

    // Single conjunct referencing non-canonical variable
    let formula = ChcExpr::eq(
        ChcExpr::var(a0.clone()),
        ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(witness)),
    );

    let result = PdrSolver::filter_non_canonical_conjuncts(&formula, &[a0]);

    // Must filter to true since the only conjunct has non-canonical vars
    assert!(
        matches!(result, ChcExpr::Bool(true)),
        "Single non-canonical conjunct should be filtered: {result}"
    );
}

// ── propagate_tight_bound_constants ─────────────────────────────────

#[test]
fn tight_bounds_produces_equality() {
    let a0 = int_var("a0");

    // a0 >= 5 AND a0 <= 5
    let formula = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(a0.clone()), ChcExpr::int(5)),
        ChcExpr::le(ChcExpr::var(a0), ChcExpr::int(5)),
    );

    let result = PdrSolver::propagate_tight_bound_constants(&formula);

    // Should contain a0 = 5
    let conjuncts = result.collect_conjuncts();
    let has_equality = conjuncts.iter().any(|c| {
        matches!(c, ChcExpr::Op(ChcOp::Eq, args)
            if args.len() == 2
            && matches!(args[0].as_ref(), ChcExpr::Var(v) if v.name == "a0")
            && matches!(args[1].as_ref(), ChcExpr::Int(5)))
    });
    assert!(has_equality, "Expected a0 = 5 in result: {result}");
}

#[test]
fn tight_bounds_all_constants_not_true() {
    let a0 = int_var("a0");
    let a1 = int_var("a1");

    // a0 >= 0 AND a0 <= 0 AND a1 >= 0 AND a1 <= 0
    let formula = ChcExpr::and_all(vec![
        ChcExpr::ge(ChcExpr::var(a0.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(a0), ChcExpr::int(0)),
        ChcExpr::ge(ChcExpr::var(a1.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(a1), ChcExpr::int(0)),
    ]);

    let result = PdrSolver::propagate_tight_bound_constants(&formula);

    // Must NOT simplify to true — must preserve equalities
    assert!(
        !matches!(result, ChcExpr::Bool(true)),
        "tight bounds lost information: {result}"
    );

    // Should contain a0 = 0 AND a1 = 0
    let vars_in_result = result.vars();
    assert!(
        vars_in_result.iter().any(|v| v.name == "a0"),
        "a0 missing from result: {result}"
    );
    assert!(
        vars_in_result.iter().any(|v| v.name == "a1"),
        "a1 missing from result: {result}"
    );
}

#[test]
fn tight_bounds_preserves_remainder() {
    let a0 = int_var("a0");
    let a1 = int_var("a1");

    // a0 >= 3 AND a0 <= 3 AND a1 >= 0
    let formula = ChcExpr::and_all(vec![
        ChcExpr::ge(ChcExpr::var(a0.clone()), ChcExpr::int(3)),
        ChcExpr::le(ChcExpr::var(a0), ChcExpr::int(3)),
        ChcExpr::ge(ChcExpr::var(a1), ChcExpr::int(0)),
    ]);

    let result = PdrSolver::propagate_tight_bound_constants(&formula);

    // Should contain both a0 = 3 AND a1 >= 0 (or a1 >= 0 with a0 substituted)
    assert!(
        !matches!(result, ChcExpr::Bool(true)),
        "Should not be trivially true: {result}"
    );
    let conjuncts = result.collect_conjuncts();
    assert!(
        conjuncts.len() >= 2,
        "Expected at least 2 conjuncts (equality + remainder), got {}: {result}",
        conjuncts.len()
    );
}

#[test]
fn tight_bounds_no_bounds_unchanged() {
    let a0 = int_var("a0");

    // a0 >= 0 (no tight bounds)
    let formula = ChcExpr::ge(ChcExpr::var(a0), ChcExpr::int(0));
    let result = PdrSolver::propagate_tight_bound_constants(&formula);
    assert_eq!(result, formula);
}

#[test]
fn tight_bounds_non_matching_bounds_unchanged() {
    let a0 = int_var("a0");

    // a0 >= 0 AND a0 <= 10 (not tight)
    let formula = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(a0.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(a0), ChcExpr::int(10)),
    );
    let original = formula.clone();
    let result = PdrSolver::propagate_tight_bound_constants(&formula);
    assert_eq!(result, original);
}
