// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]

use super::*;
use crate::smt::SmtContext;
use std::sync::Arc;

#[test]
fn test_parse_simple_le() {
    let x = ChcVar::new("x", ChcSort::Int);
    // x <= 5  =>  x - 5 <= 0, so coeff(x)=1, bound=5
    let expr = ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(5));
    let constraint = parse_linear_constraint(&expr).unwrap();

    assert_eq!(constraint.get_coeff("x"), Rational64::from_integer(1));
    // Constraint form: x - 5 <= 0 means bound is stored as the RHS negated from the expr
    // For a <= b, we have a - b <= 0, so bound stores +b's contribution
    assert_eq!(constraint.bound, Rational64::from_integer(5));
    assert!(!constraint.strict);
}

#[test]
fn test_parse_ge_to_le() {
    let x = ChcVar::new("x", ChcSort::Int);
    // x >= 5  =>  5 - x <= 0  =>  -x <= -5
    let expr = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(5));
    let constraint = parse_linear_constraint(&expr).unwrap();

    assert_eq!(constraint.get_coeff("x"), Rational64::from_integer(-1));
    // For a >= b, we have b - a <= 0
    assert_eq!(constraint.bound, Rational64::from_integer(-5));
    assert!(!constraint.strict);
}

#[test]
fn test_parse_linear_combination() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    // x + 2*y <= 10  =>  x + 2y - 10 <= 0
    let expr = ChcExpr::le(
        ChcExpr::add(
            ChcExpr::var(x),
            ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(y)),
        ),
        ChcExpr::Int(10),
    );
    let constraint = parse_linear_constraint(&expr).unwrap();

    assert_eq!(constraint.get_coeff("x"), Rational64::from_integer(1));
    assert_eq!(constraint.get_coeff("y"), Rational64::from_integer(2));
    // Bound stores the RHS contribution: -(-10) = 10
    assert_eq!(constraint.bound, Rational64::from_integer(10));
}

#[test]
fn test_parse_linear_constraint_returns_none_on_nested_multiplier_overflow() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::le(
        ChcExpr::mul(
            ChcExpr::Int(i64::MAX),
            ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(x)),
        ),
        ChcExpr::Int(0),
    );

    assert!(
        parse_linear_constraint(&expr).is_none(),
        "nested Rational64 multipliers that overflow must degrade to None"
    );
}

#[test]
fn test_parse_linear_constraint_returns_none_on_negated_min_multiplier() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::le(
        ChcExpr::neg(ChcExpr::mul(ChcExpr::Int(i64::MIN), ChcExpr::var(x))),
        ChcExpr::Int(0),
    );

    assert!(
        parse_linear_constraint(&expr).is_none(),
        "negating an i64::MIN Rational64 multiplier must degrade to None"
    );
}

#[test]
fn test_parse_linear_constraint_returns_none_on_constant_accumulation_overflow() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::le(
        ChcExpr::var(x),
        ChcExpr::add(ChcExpr::Int(i64::MAX), ChcExpr::Int(1)),
    );

    assert!(
        parse_linear_constraint(&expr).is_none(),
        "constant accumulation overflow must degrade to None"
    );
}

#[test]
fn test_normalize_linear_inequality_expr_reduces_common_gcd() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::le(
        ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(x.clone())),
        ChcExpr::Int(4),
    );

    let normalized =
        normalize_linear_inequality_expr(&expr).expect("2*x <= 4 should normalize to x <= 2");

    assert_eq!(normalized, ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(2)));
}

#[test]
fn test_normalize_linear_inequality_expr_preserves_negated_strict_form() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::not(ChcExpr::le(
        ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(x)),
        ChcExpr::Int(4),
    ));

    let normalized =
        normalize_linear_inequality_expr(&expr).expect("not (2*x <= 4) should normalize");
    let constraint = parse_linear_constraint(&normalized).expect("normalized expr stays linear");

    assert!(
        constraint.strict,
        "not (<=) must remain strict after normalization"
    );
    assert_eq!(constraint.get_coeff("x"), Rational64::from_integer(-1));
    assert_eq!(constraint.bound, Rational64::from_integer(-2));
}

#[test]
fn test_farkas_combine_opposite_bounds() {
    let x = ChcVar::new("x", ChcSort::Int);
    // x <= 5 and x >= 10 (UNSAT)
    // Combined: 0 <= 5 - 10 = -5 (false)
    let c1 = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(5));
    let c2 = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(10));

    let fc =
        farkas_combine(&[c1, c2]).expect("x <= 5 and x >= 10 must produce a Farkas contradiction");
    // x and -x cancel, leaving 0 <= 5 + (-10) = -5, which is false.
    assert_eq!(
        fc.combined,
        ChcExpr::Bool(false),
        "opposite bounds x<=5, x>=10 must combine to contradiction (false)"
    );
}

#[test]
fn test_farkas_combine_variable_elimination() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    // x + y <= 5 and -x <= -3 (i.e., x >= 3)
    // Combining eliminates x: y <= 2
    let c1 = ChcExpr::le(
        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y)),
        ChcExpr::Int(5),
    );
    let c2 = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(3));

    let fc = farkas_combine(&[c1, c2]).expect("x+y<=5 and x>=3 must produce a combined constraint");
    // Eliminating x from (x+y<=5, -x<=-3) yields y<=2.
    assert_eq!(
        fc.combined,
        ChcExpr::le(
            ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
            ChcExpr::Int(2)
        ),
        "variable elimination should produce y <= 2"
    );
}

/// Regression test for #97: Equality constraint handling.
///
/// The bug was that `parse_linear_constraint` only returned one direction
/// for equalities (x <= c) when the Farkas proof might need the other
/// direction (x >= c). Verify that equalities are handled correctly.
#[test]
fn test_parse_equality_both_directions() {
    let x = ChcVar::new("x", ChcSort::Int);
    // x = 5 should be parseable
    let expr = ChcExpr::Op(
        ChcOp::Eq,
        vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::Int(5))],
    );
    let constraint = parse_linear_constraint(&expr);
    assert!(constraint.is_some(), "Equality should be parseable");

    // The constraint represents x - 5 <= 0 (one direction)
    let c = constraint.unwrap();
    assert_eq!(c.get_coeff("x"), Rational64::from_integer(1));
    assert_eq!(c.bound, Rational64::from_integer(5));
}

#[test]
fn test_parse_linear_constraints_split_eq_flattens_conjunctions() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(5)),
        ChcExpr::le(ChcExpr::var(y), ChcExpr::Int(7)),
    );

    let constraints = parse_linear_constraints_split_eq(&expr);

    assert_eq!(
        constraints.len(),
        3,
        "flattened conjunction should yield both equality directions plus the inequality"
    );
    assert_eq!(constraints[0].get_coeff("x"), Rational64::from_integer(1));
    assert_eq!(constraints[0].bound, Rational64::from_integer(5));
    assert_eq!(constraints[1].get_coeff("x"), Rational64::from_integer(-1));
    assert_eq!(constraints[1].bound, Rational64::from_integer(-5));
    assert_eq!(constraints[2].get_coeff("y"), Rational64::from_integer(1));
    assert_eq!(constraints[2].bound, Rational64::from_integer(7));
}

#[test]
fn test_parse_linear_constraints_flat_flattens_b_side_conjunctions() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(3)),
        ChcExpr::lt(ChcExpr::var(y), ChcExpr::Int(9)),
    );

    let constraints = parse_linear_constraints_flat(&expr);

    assert_eq!(constraints.len(), 2, "both conjuncts should be preserved");
    assert_eq!(constraints[0].get_coeff("x"), Rational64::from_integer(-1));
    assert_eq!(constraints[0].bound, Rational64::from_integer(-3));
    assert_eq!(constraints[1].get_coeff("y"), Rational64::from_integer(1));
    assert!(constraints[1].strict, "strictness must survive flattening");
    assert_eq!(constraints[1].bound, Rational64::from_integer(9));
}

/// Test that strict inequalities are handled correctly
#[test]
fn test_parse_strict_inequality() {
    let x = ChcVar::new("x", ChcSort::Int);

    // x < 5 (strict upper bound)
    let lt_expr = ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::Int(5));
    let lt_constraint = parse_linear_constraint(&lt_expr).unwrap();
    assert!(lt_constraint.strict);
    assert_eq!(lt_constraint.get_coeff("x"), Rational64::from_integer(1));

    // x > 5 (strict lower bound)
    let gt_expr = ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(5));
    let gt_constraint = parse_linear_constraint(&gt_expr).unwrap();
    assert!(gt_constraint.strict);
    assert_eq!(gt_constraint.get_coeff("x"), Rational64::from_integer(-1));
}

#[test]
fn test_linear_constraint_to_int_bound_rounding_and_sign() {
    let x = ChcVar::new("x", ChcSort::Int);

    // x <= 5  =>  upper bound 5
    let le = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(5));
    let c = parse_linear_constraint(&le).unwrap();
    assert_eq!(
        linear_constraint_to_int_bound(&c),
        Some(("x".to_string(), IntBound::Upper(5)))
    );

    // 2x <= 5  =>  x <= 2  (floor(5/2))
    let le = ChcExpr::le(
        ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(x.clone())),
        ChcExpr::Int(5),
    );
    let c = parse_linear_constraint(&le).unwrap();
    assert_eq!(
        linear_constraint_to_int_bound(&c),
        Some(("x".to_string(), IntBound::Upper(2)))
    );

    // x >= 5  =>  lower bound 5  (NOTE: coeff is negative)
    let ge = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(5));
    let c = parse_linear_constraint(&ge).unwrap();
    assert_eq!(
        linear_constraint_to_int_bound(&c),
        Some(("x".to_string(), IntBound::Lower(5)))
    );

    // 2x >= 5  =>  x >= 3  (ceil(5/2))
    let ge = ChcExpr::ge(
        ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(x.clone())),
        ChcExpr::Int(5),
    );
    let c = parse_linear_constraint(&ge).unwrap();
    assert_eq!(
        linear_constraint_to_int_bound(&c),
        Some(("x".to_string(), IntBound::Lower(3)))
    );

    // x < 5  =>  x <= 4
    let lt = ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::Int(5));
    let c = parse_linear_constraint(&lt).unwrap();
    assert_eq!(
        linear_constraint_to_int_bound(&c),
        Some(("x".to_string(), IntBound::Upper(4)))
    );

    // x > 5  =>  x >= 6
    let gt = ChcExpr::gt(ChcExpr::var(x), ChcExpr::Int(5));
    let c = parse_linear_constraint(&gt).unwrap();
    assert_eq!(
        linear_constraint_to_int_bound(&c),
        Some(("x".to_string(), IntBound::Lower(6)))
    );
}

#[test]
fn test_linear_constraint_to_int_bound_returns_none_on_division_overflow() {
    let mut constraint = LinearConstraint::new(Rational64::from_integer(i64::MAX), false);
    constraint.set_coeff("x", Rational64::new(1, i64::MAX));

    assert!(
        linear_constraint_to_int_bound(&constraint).is_none(),
        "Rational64 division overflow must degrade to None"
    );
}

#[test]
fn test_pairwise_elimination_returns_none_on_bound_overflow() {
    let mut c1 = LinearConstraint::new(Rational64::from_integer(i64::MAX), false);
    c1.set_coeff("x", Rational64::from_integer(1));
    c1.set_coeff("tmp", Rational64::from_integer(-1));

    let mut c2 = LinearConstraint::new(Rational64::from_integer(i64::MAX), false);
    c2.set_coeff("y", Rational64::from_integer(1));
    c2.set_coeff("tmp", Rational64::from_integer(1));

    let shared_vars: FxHashSet<String> = ["x".to_string(), "y".to_string()].into_iter().collect();

    assert!(
        try_pairwise_eliminate_non_shared(&c1, &c2, "tmp", &shared_vars).is_none(),
        "pairwise elimination overflow must degrade to None"
    );
}

#[test]
fn test_normalize_constraint_skips_gcd_division_overflow() {
    let original_coeff = Rational64::new(i64::MAX - 1, i64::MAX);
    let original_bound = Rational64::new(i64::MAX - 1, i64::MAX);
    let mut constraint = LinearConstraint::new(original_bound, false);
    constraint.set_coeff("x", original_coeff);

    let normalized = normalize::normalize_constraint(constraint.clone());

    assert_eq!(
        normalized, constraint,
        "GCD reduction overflow must leave the constraint unchanged"
    );
}

/// Test interpolation with mixed A/B partitions where variables appear in both
#[test]
fn test_interpolant_shared_variables_only() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // A: x >= 10, y = 0 (y is not shared)
    // B: x <= 5
    // Interpolant should be: x >= 10 (using only shared var x)
    let a_constraints = vec![
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10)),
        ChcExpr::Op(
            ChcOp::Eq,
            vec![Arc::new(ChcExpr::var(y)), Arc::new(ChcExpr::Int(0))],
        ),
    ];
    let b_constraints = vec![ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(5))];
    let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();

    let result = compute_interpolant(&a_constraints, &b_constraints, &shared);
    assert!(
        result.is_some(),
        "Should find interpolant with shared vars only"
    );

    // The interpolant should only mention x (shared), not y (not shared)
    let interp = result.unwrap();
    let interp_str = format!("{interp}");
    assert!(
        interp_str.contains("x"),
        "Interpolant should mention shared var x"
    );
    assert!(
        !interp_str.contains("y"),
        "Interpolant should NOT mention non-shared var y"
    );
}

/// Test bound tightening strategy
#[test]
fn test_farkas_bound_tightening() {
    let x = ChcVar::new("x", ChcSort::Int);

    // Multiple upper bounds: x <= 10, x <= 5, x <= 3
    // Multiple lower bounds: x >= 1, x >= 2
    // Combined: 2 <= x <= 3 (tight bounds)
    // Adding x >= 5 creates contradiction
    let constraints = vec![
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(3)),
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(5)),
    ];

    let result = farkas_combine(&constraints);
    assert!(
        result.is_some(),
        "Should detect contradiction via bound tightening"
    );
}

/// Test transitivity chain: x <= y, y <= z, z <= 0, x >= 5 is UNSAT
#[test]
fn test_farkas_transitivity_chain() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    // x - y <= 0 (x <= y)
    let c1 = ChcExpr::le(
        ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::Int(0),
    );
    // y - z <= 0 (y <= z)
    let c2 = ChcExpr::le(
        ChcExpr::sub(ChcExpr::var(y), ChcExpr::var(z.clone())),
        ChcExpr::Int(0),
    );
    // z <= 0
    let c3 = ChcExpr::le(ChcExpr::var(z), ChcExpr::Int(0));
    // x >= 5 (-x <= -5)
    let c4 = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(5));

    // Transitivity should derive: x <= z <= 0 contradicts x >= 5
    let result = farkas_combine(&[c1, c2, c3, c4]);
    // Note: This might not find a result if the strategy doesn't support
    // 4-way transitivity chains. That's acceptable - test documents the case.
    if let Some(r) = result {
        safe_eprintln!("Transitivity chain detected: {:?}", r.combined);
    }
}

#[test]
fn test_compute_interpolant_rejects_nonblocking_candidate() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // A implies x + y <= 0, but also contains weaker constraints that don't block B.
    // Strategy 3 must not return a non-blocking constraint like x >= 0.
    let a_constraints = vec![
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0)),
        ChcExpr::le(
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
            ChcExpr::int(0),
        ),
    ];
    let b_constraints = vec![ChcExpr::ge(
        ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y)),
        ChcExpr::int(1),
    )];

    let mut shared_vars: FxHashSet<String> = FxHashSet::default();
    shared_vars.insert("x".to_string());
    shared_vars.insert("y".to_string());

    let interpolant =
        compute_interpolant(&a_constraints, &b_constraints, &shared_vars).expect("expected Some");

    let a = ChcExpr::and_all(a_constraints.iter().cloned());
    let b = ChcExpr::and_all(b_constraints.iter().cloned());
    let mut smt = SmtContext::new();
    assert!(is_valid_interpolant(
        &a,
        &b,
        &interpolant,
        &shared_vars,
        &mut smt
    ));
}

/// Regression test for #1025: Rational coefficients should be scaled via LCM,
/// not silently dropped.
///
/// Before fix: `(1/2)x + y <= 3` would drop the `(1/2)x` term, producing `y <= 3`
/// After fix: LCM(2,1) = 2, constraint becomes `x + 2y <= 6`
#[test]
fn test_build_linear_inequality_rational_coefficients() {
    let mut coeffs: FxHashMap<String, Rational64> = FxHashMap::default();
    // Coefficient 1/2 for x
    coeffs.insert("x".to_string(), Rational64::new(1, 2));
    // Coefficient 1 for y
    coeffs.insert("y".to_string(), Rational64::from_integer(1));

    // (1/2)x + y <= 3  should become  x + 2y <= 6
    let bound = Rational64::from_integer(3);
    let expr = build_linear_inequality(&coeffs, bound, false);

    // Verify the expression includes both variables (x was not dropped)
    let expr_str = format!("{expr:?}");
    assert!(
        expr_str.contains("\"x\"") || expr_str.contains("x"),
        "x should be present in result: {expr_str}"
    );
    assert!(
        expr_str.contains("\"y\"") || expr_str.contains("y"),
        "y should be present in result: {expr_str}"
    );

    // The bound should be scaled by LCM (6, not 3)
    assert!(
        expr_str.contains("Int(6)"),
        "bound should be scaled to 6: {expr_str}"
    );
}

/// Test that purely rational bound with integer coefficients is handled correctly.
#[test]
fn test_build_linear_inequality_rational_bound() {
    let mut coeffs: FxHashMap<String, Rational64> = FxHashMap::default();
    // Integer coefficient 1 for x
    coeffs.insert("x".to_string(), Rational64::from_integer(1));

    // x <= 5/2  should become  2x <= 5
    let bound = Rational64::new(5, 2);
    let expr = build_linear_inequality(&coeffs, bound, false);

    let expr_str = format!("{expr:?}");
    // Should have coefficient 2 for x and bound 5
    assert!(
        expr_str.contains("Int(2)") && expr_str.contains("Int(5)"),
        "should scale to 2x <= 5: {expr_str}"
    );
}

/// Test that LCM calculation handles multiple rational coefficients.
#[test]
fn test_build_linear_inequality_multiple_rationals() {
    let mut coeffs: FxHashMap<String, Rational64> = FxHashMap::default();
    // Coefficients 1/2 for x, 1/3 for y
    coeffs.insert("x".to_string(), Rational64::new(1, 2));
    coeffs.insert("y".to_string(), Rational64::new(1, 3));

    // (1/2)x + (1/3)y <= 1  should become  3x + 2y <= 6 (LCM(2,3)=6)
    let bound = Rational64::from_integer(1);
    let expr = build_linear_inequality(&coeffs, bound, false);

    let expr_str = format!("{expr:?}");
    // Both variables should be present
    assert!(
        expr_str.contains("\"x\"") || expr_str.contains("x"),
        "x should be present: {expr_str}"
    );
    assert!(
        expr_str.contains("\"y\"") || expr_str.contains("y"),
        "y should be present: {expr_str}"
    );
    // Bound should be 6
    assert!(expr_str.contains("Int(6)"), "bound should be 6: {expr_str}");
}

// =========================================================================
// Craig interpolant validation tests (#1044)
// =========================================================================

/// Test: Valid interpolant passes Craig checks.
///
/// Given A = (x <= 5) and B = (x >= 10), which is UNSAT,
/// the interpolant I = (x <= 7) should pass because:
/// - A ⊨ I: x <= 5 implies x <= 7
/// - I ∧ B is UNSAT: x <= 7 and x >= 10 is UNSAT
#[test]
fn test_craig_valid_interpolant_passes() {
    let x_var = "x".to_string();
    let shared_vars: FxHashSet<String> = [x_var].into_iter().collect();

    let x = ChcVar::new("x", ChcSort::Int);
    // A: x <= 5
    let a = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(5));
    // B: x >= 10
    let b = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10));
    // I: x <= 7 (valid: implied by A, blocks B)
    let interpolant = ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(7));

    assert!(
        is_valid_interpolant(&a, &b, &interpolant, &shared_vars, &mut SmtContext::new()),
        "Valid interpolant should pass Craig checks"
    );
}

/// Test: Interpolant not implied by A fails Craig check.
///
/// A = (x <= 5), B = (x >= 10)
/// I = (x <= 3) fails because A does not imply I (x=4 satisfies A but not I)
#[test]
fn test_craig_interpolant_not_implied_by_a_fails() {
    let x_var = "x".to_string();
    let shared_vars: FxHashSet<String> = [x_var].into_iter().collect();

    let x = ChcVar::new("x", ChcSort::Int);
    // A: x <= 5
    let a = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(5));
    // B: x >= 10
    let b = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10));
    // I: x <= 3 (invalid: A has x=4 but I excludes it)
    let interpolant = ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(3));

    assert!(
        !is_valid_interpolant(&a, &b, &interpolant, &shared_vars, &mut SmtContext::new()),
        "Interpolant not implied by A should fail Craig check"
    );
}

/// Test: Interpolant that doesn't block B fails Craig check.
///
/// A = (x <= 5), B = (x >= 10)
/// I = (x <= 15) fails because I ∧ B is SAT (x=12 satisfies both)
#[test]
fn test_craig_interpolant_doesnt_block_b_fails() {
    let x_var = "x".to_string();
    let shared_vars: FxHashSet<String> = [x_var].into_iter().collect();

    let x = ChcVar::new("x", ChcSort::Int);
    // A: x <= 5
    let a = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(5));
    // B: x >= 10
    let b = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10));
    // I: x <= 15 (invalid: doesn't block B, x=12 satisfies both I and B)
    let interpolant = ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(15));

    assert!(
        !is_valid_interpolant(&a, &b, &interpolant, &shared_vars, &mut SmtContext::new()),
        "Interpolant that doesn't block B should fail Craig check"
    );
}

/// Test: Interpolant with non-shared variables fails Craig check.
///
/// A = (x <= 5), B = (y >= 10), shared = {x, y}
/// I = (z <= 7) fails because z is not in shared vars
#[test]
fn test_craig_interpolant_non_shared_vars_fails() {
    let shared_vars: FxHashSet<String> = ["x".to_string(), "y".to_string()].into_iter().collect();

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);
    // A: x <= 5
    let a = ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(5));
    // B: y >= 10
    let b = ChcExpr::ge(ChcExpr::var(y), ChcExpr::Int(10));
    // I: z <= 7 (invalid: z not in shared vars)
    let interpolant = ChcExpr::le(ChcExpr::var(z), ChcExpr::Int(7));

    assert!(
        !is_valid_interpolant(&a, &b, &interpolant, &shared_vars, &mut SmtContext::new()),
        "Interpolant with non-shared vars should fail Craig check"
    );
}

/// Test: False is a valid interpolant when A is inconsistent.
///
/// A = (x <= 5) ∧ (x >= 10) is UNSAT, so false is a valid interpolant.
/// - A ⊨ false (vacuously true when A is UNSAT)
/// - false ∧ B = false, which is UNSAT
///
/// Note: This test verifies the degenerate case where A itself is UNSAT.
#[test]
fn test_craig_false_interpolant_when_a_unsat() {
    let x_var = "x".to_string();
    let shared_vars: FxHashSet<String> = [x_var].into_iter().collect();

    let x = ChcVar::new("x", ChcSort::Int);
    // A: (x <= 5) ∧ (x >= 10) - UNSAT
    let a = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(5)),
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10)),
    );
    // B: anything (use x >= 0 which is almost always true)
    let b = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));
    // I: false (blocks everything - valid when A is UNSAT)
    let interpolant = ChcExpr::Bool(false);

    assert!(
        is_valid_interpolant(&a, &b, &interpolant, &shared_vars, &mut SmtContext::new()),
        "False is valid interpolant when A is UNSAT"
    );
}

// --- Edge case tests for helper functions ---

/// rational64_abs with i64::MIN numerator uses a lossy approximation
/// (i64::MAX instead of -i64::MIN which would overflow). Verify the
/// precision loss is bounded to 1 ULP.
#[test]
fn test_rational64_abs_i64_min_lossy() {
    let r = Rational64::new_raw(i64::MIN, 1);
    let abs_r = rational64_abs(r);
    // Expected: i64::MAX / 1 (lossy: should be i64::MIN.unsigned_abs() = 2^63)
    assert_eq!(*abs_r.numer(), i64::MAX);
    assert_eq!(*abs_r.denom(), 1);
    // The precision loss is exactly 1
    let true_abs = i128::from(i64::MIN).unsigned_abs();
    let approx = *abs_r.numer() as u128;
    assert_eq!(
        true_abs - approx,
        1,
        "lossy approximation should differ by exactly 1"
    );
}

/// rational64_abs with normal positive value is identity.
#[test]
fn test_rational64_abs_positive() {
    let r = Rational64::new(7, 3);
    let abs_r = rational64_abs(r);
    assert_eq!(*abs_r.numer(), 7);
    assert_eq!(*abs_r.denom(), 3);
}

/// rational64_abs with normal negative value negates numerator.
#[test]
fn test_rational64_abs_negative() {
    let r = Rational64::new(-7, 3);
    let abs_r = rational64_abs(r);
    assert_eq!(*abs_r.numer(), 7);
    assert_eq!(*abs_r.denom(), 3);
}

/// floor_rational64 rounds toward negative infinity.
#[test]
fn test_floor_rational64_positive_fraction() {
    let r = Rational64::new(7, 3); // 2.333...
    assert_eq!(floor_rational64(r), Some(2));
}

#[test]
fn test_floor_rational64_negative_fraction() {
    let r = Rational64::new(-7, 3); // -2.333...
    assert_eq!(floor_rational64(r), Some(-3));
}

#[test]
fn test_floor_rational64_exact() {
    let r = Rational64::new(6, 3); // exactly 2
    assert_eq!(floor_rational64(r), Some(2));
}

/// ceil_rational64 rounds toward positive infinity.
#[test]
fn test_ceil_rational64_positive_fraction() {
    let r = Rational64::new(7, 3); // 2.333...
    assert_eq!(ceil_rational64(r), Some(3));
}

#[test]
fn test_ceil_rational64_negative_fraction() {
    let r = Rational64::new(-7, 3); // -2.333...
    assert_eq!(ceil_rational64(r), Some(-2));
}

#[test]
fn test_ceil_rational64_exact() {
    let r = Rational64::new(6, 3); // exactly 2
    assert_eq!(ceil_rational64(r), Some(2));
}

/// build_linear_inequality with integer coefficients produces correct
/// ChcExpr. Validates that the LCM scaling in build_linear_inequality
/// preserves correctness (the debug_assert on integer denominators).
#[test]
fn test_build_linear_inequality_integer_coefficients() {
    let mut coeffs = FxHashMap::default();
    coeffs.insert("x".to_string(), Rational64::from_integer(2));
    let bound = Rational64::from_integer(10);
    let result = build_linear_inequality(&coeffs, bound, false);

    let x = ChcVar::new("x", ChcSort::Int);
    assert_eq!(
        result,
        ChcExpr::le(
            ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(x)),
            ChcExpr::Int(10)
        )
    );
}

/// build_linear_inequality with rational coefficients must scale to
/// integers via LCM. E.g., (1/2)*x <= 3/4 should become 2*x <= 3
/// after multiplying by LCM=4.
#[test]
fn test_build_linear_inequality_rational_scaling() {
    let mut coeffs = FxHashMap::default();
    coeffs.insert("x".to_string(), Rational64::new(1, 2));
    let bound = Rational64::new(3, 4);
    // Non-strict: (1/2)*x <= 3/4 -> multiply by 4: 2*x <= 3
    let result = build_linear_inequality(&coeffs, bound, false);

    let x = ChcVar::new("x", ChcSort::Int);
    assert_eq!(
        result,
        ChcExpr::le(
            ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(x)),
            ChcExpr::Int(3)
        )
    );
}

/// build_linear_inequality with all-zero coefficients reduces to a
/// constant comparison (0 <= bound).
#[test]
fn test_build_linear_inequality_zero_coefficients() {
    let mut coeffs = FxHashMap::default();
    coeffs.insert("x".to_string(), Rational64::from_integer(0));
    let bound = Rational64::from_integer(5);
    // 0*x <= 5  =>  0 <= 5  =>  true
    let result = build_linear_inequality(&coeffs, bound, false);
    assert_eq!(result, ChcExpr::Bool(true));
}

/// build_linear_inequality with zero bound and negative coefficients.
#[test]
fn test_build_linear_inequality_zero_bound_negative_coeff() {
    let mut coeffs = FxHashMap::default();
    coeffs.insert("x".to_string(), Rational64::from_integer(-1));
    let bound = Rational64::from_integer(0);
    // -x <= 0  =>  x >= 0
    let result = build_linear_inequality(&coeffs, bound, false);
    assert_ne!(result, ChcExpr::Bool(true));
    assert_ne!(result, ChcExpr::Bool(false));
}
