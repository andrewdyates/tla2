// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::heuristics::extract_simple_bound;
use super::*;
use crate::{ChcSort, ChcVar};
use rustc_hash::FxHashSet;

#[test]
fn test_interpolating_sat_bound_contradiction() {
    // A: x >= 10
    // B: x <= 5
    // Should be UNSAT with interpolant x >= 10
    let x = ChcVar::new("x", ChcSort::Int);
    let a = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10));
    let b = ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(5));

    let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();

    match interpolating_sat_constraints(&[a], &[b], &shared) {
        InterpolatingSatResult::Unsat(interp) => {
            // Interpolant should be x >= 10 or equivalent
            println!("Interpolant: {interp}");
        }
        other => panic!("Expected Unsat, got {other:?}"),
    }
}

#[test]
fn test_extract_simple_bounds() {
    let x = ChcVar::new("x", ChcSort::Int);

    // x <= 5
    let le = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(5));
    assert_eq!(extract_simple_bound(&le), Some(("x".to_string(), 5, true)));

    // x >= 3
    let ge = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(3));
    assert_eq!(extract_simple_bound(&ge), Some(("x".to_string(), 3, false)));

    // Reversed operand order: c <= var, c >= var, c < var, c > var
    // 5 <= x  =>  x >= 5
    let c_le_v = ChcExpr::le(ChcExpr::Int(5), ChcExpr::var(x.clone()));
    assert_eq!(
        extract_simple_bound(&c_le_v),
        Some(("x".to_string(), 5, false)),
        "5 <= x should be recognized as x >= 5"
    );

    // 3 >= x  =>  x <= 3
    let c_ge_v = ChcExpr::ge(ChcExpr::Int(3), ChcExpr::var(x.clone()));
    assert_eq!(
        extract_simple_bound(&c_ge_v),
        Some(("x".to_string(), 3, true)),
        "3 >= x should be recognized as x <= 3"
    );

    // 5 < x  =>  x >= 6  (i.e., x >= 5+1)
    let c_lt_v = ChcExpr::lt(ChcExpr::Int(5), ChcExpr::var(x.clone()));
    assert_eq!(
        extract_simple_bound(&c_lt_v),
        Some(("x".to_string(), 6, false)),
        "5 < x should be recognized as x >= 6"
    );

    // 3 > x  =>  x <= 2  (i.e., x <= 3-1)
    let c_gt_v = ChcExpr::gt(ChcExpr::Int(3), ChcExpr::var(x));
    assert_eq!(
        extract_simple_bound(&c_gt_v),
        Some(("x".to_string(), 2, true)),
        "3 > x should be recognized as x <= 2"
    );
}

#[test]
fn test_is_valid_interpolant_rejects_bad_candidates() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let a = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10))];
    let b = vec![ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(5))];
    let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();

    // Fails A ⊨ I.
    let not_implied = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::Int(5));
    assert!(!is_valid_interpolant(&a, &b, &not_implied, &shared));

    // Fails I ∧ B UNSAT.
    let does_not_block_b = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0));
    assert!(!is_valid_interpolant(&a, &b, &does_not_block_b, &shared));

    // Fails shared-variable condition.
    let non_shared = ChcExpr::ge(ChcExpr::var(y), ChcExpr::Int(0));
    assert!(!is_valid_interpolant(&a, &b, &non_shared, &shared));
}

#[test]
fn test_interpolating_sat_constraints_sat_input_returns_unknown() {
    // SAT input (x >= 0 ∧ x <= 10). Must not produce an interpolant.
    let x = ChcVar::new("x", ChcSort::Int);
    let a = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(0));
    let b = ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(10));
    let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();

    assert!(matches!(
        interpolating_sat_constraints(&[a], &[b], &shared),
        InterpolatingSatResult::Unknown
    ));
}

#[test]
fn test_disjunction_split_combined_interpolant_satisfies_craig_conditions() {
    let x = ChcVar::new("x", ChcSort::Int);
    let a = vec![ChcExpr::or(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(1)),
    )];
    let b = vec![ChcExpr::and(
        ChcExpr::ne(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ChcExpr::ne(ChcExpr::var(x), ChcExpr::Int(1)),
    )];
    let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();

    let mut budget = DISJUNCTION_SPLIT_BRANCH_LIMIT;
    match interpolate_with_disjunction_split(&a, &b, &shared, &mut budget) {
        Some(InterpolatingSatResult::Unsat(interp)) => {
            assert!(
                is_valid_interpolant(&a, &b, &interp, &shared),
                "combined disjunctive interpolant must satisfy Craig checks"
            );
            let vars: FxHashSet<String> = interp.vars().into_iter().map(|v| v.name).collect();
            assert!(
                vars.iter().all(|v| shared.contains(v)),
                "interpolant must mention only shared vars, got {vars:?}"
            );
        }
        other => {
            panic!("expected disjunction split to produce UNSAT interpolant, got {other:?}")
        }
    }
}

/// Test 3-way disjunction: A = (x=0 ∨ x=1 ∨ x=2), B = (x≠0 ∧ x≠1 ∧ x≠2)
/// Exercises the >2 disjunct path where or_all combines 3 branch interpolants.
#[test]
fn test_disjunction_split_three_branches_satisfies_craig() {
    let x = ChcVar::new("x", ChcSort::Int);
    let a = vec![ChcExpr::or_all([
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(1)),
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(2)),
    ])];
    let b = vec![
        ChcExpr::ne(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
        ChcExpr::ne(ChcExpr::var(x.clone()), ChcExpr::Int(1)),
        ChcExpr::ne(ChcExpr::var(x), ChcExpr::Int(2)),
    ];
    let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();

    let mut budget = DISJUNCTION_SPLIT_BRANCH_LIMIT;
    match interpolate_with_disjunction_split(&a, &b, &shared, &mut budget) {
        Some(InterpolatingSatResult::Unsat(interp)) => {
            assert!(
                is_valid_interpolant(&a, &b, &interp, &shared),
                "3-way disjunctive interpolant must satisfy Craig checks"
            );
            let vars: FxHashSet<String> = interp.vars().into_iter().map(|v| v.name).collect();
            assert!(
                vars.iter().all(|v| shared.contains(v)),
                "interpolant must mention only shared vars, got {vars:?}"
            );
        }
        other => {
            panic!("expected 3-way disjunction split to produce UNSAT interpolant, got {other:?}")
        }
    }
}

/// Test budget exhaustion: a disjunction with 33 branches exceeds the 32-branch limit.
/// The function should return Unknown (sound fallback), never an unsound result.
#[test]
fn test_disjunction_split_budget_exhaustion_returns_unknown() {
    let x = ChcVar::new("x", ChcSort::Int);

    // Build A = (x=0 ∨ x=1 ∨ ... ∨ x=32) — 33 branches, exceeds budget of 32.
    let disjuncts: Vec<ChcExpr> = (0..33)
        .map(|i| ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(i)))
        .collect();
    let a = vec![ChcExpr::or_all(disjuncts)];

    let b_conjuncts: Vec<ChcExpr> = (0..33)
        .map(|i| ChcExpr::ne(ChcExpr::var(x.clone()), ChcExpr::Int(i)))
        .collect();
    let b = b_conjuncts;
    let shared: FxHashSet<String> = ["x".to_string()].into_iter().collect();

    let mut budget = DISJUNCTION_SPLIT_BRANCH_LIMIT;
    match interpolate_with_disjunction_split(&a, &b, &shared, &mut budget) {
        Some(InterpolatingSatResult::Unknown) => {
            // Budget exceeded — sound fallback to Unknown.
        }
        other => {
            panic!("expected budget exhaustion to return Unknown, got {other:?}")
        }
    }
}
