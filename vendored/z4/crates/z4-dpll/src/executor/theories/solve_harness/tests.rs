// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::FromPrimitive;
use z4_core::{Sort, TermStore};

fn rat(n: i64) -> BigRational {
    BigRational::from_i64(n).unwrap()
}

#[test]
fn test_check_split_oscillation_first_call_returns_false() {
    let mut tracking = SplitOscillationMap::new();
    let var = TermId(1);
    assert!(!check_split_oscillation(&mut tracking, var, &rat(5)));
    // Variable should be seeded with count 0
    assert_eq!(tracking[&var].1, 0);
}

#[test]
fn test_check_split_oscillation_monotonic_increase_triggers() {
    let mut tracking = SplitOscillationMap::new();
    let var = TermId(1);
    // Seed
    assert!(!check_split_oscillation(&mut tracking, var, &rat(0)));
    // 20 consecutive increases should trigger at UNBOUNDED_THRESHOLD=20
    for i in 1..=19 {
        assert!(
            !check_split_oscillation(&mut tracking, var, &rat(i)),
            "should not trigger at step {i}"
        );
    }
    // The 20th increase hits the threshold
    assert!(check_split_oscillation(&mut tracking, var, &rat(20)));
}

#[test]
fn test_check_split_oscillation_monotonic_decrease_triggers() {
    let mut tracking = SplitOscillationMap::new();
    let var = TermId(1);
    // Seed at 100
    assert!(!check_split_oscillation(&mut tracking, var, &rat(100)));
    // 20 consecutive decreases
    for i in 1..=19 {
        assert!(
            !check_split_oscillation(&mut tracking, var, &rat(100 - i)),
            "should not trigger at step {i}"
        );
    }
    assert!(check_split_oscillation(&mut tracking, var, &rat(80)));
}

#[test]
fn test_check_split_oscillation_direction_reversal_resets() {
    let mut tracking = SplitOscillationMap::new();
    let var = TermId(1);
    // Seed
    assert!(!check_split_oscillation(&mut tracking, var, &rat(0)));
    // 10 increases
    for i in 1..=10 {
        assert!(!check_split_oscillation(&mut tracking, var, &rat(i)));
    }
    assert_eq!(tracking[&var].1, 10); // count is +10
                                      // One decrease resets to -1
    assert!(!check_split_oscillation(&mut tracking, var, &rat(9)));
    assert_eq!(tracking[&var].1, -1);
    // Now 18 more decreases (total 19 including the first reversal)
    for i in 2..=19 {
        assert!(
            !check_split_oscillation(&mut tracking, var, &rat(9 - i)),
            "should not trigger at decrease step {i}"
        );
    }
    // 20th decrease triggers
    assert!(check_split_oscillation(&mut tracking, var, &rat(-12)));
}

#[test]
fn test_check_split_oscillation_equal_value_resets_to_zero() {
    let mut tracking = SplitOscillationMap::new();
    let var = TermId(1);
    assert!(!check_split_oscillation(&mut tracking, var, &rat(5)));
    // Increase 15 times
    for i in 1..=15 {
        assert!(!check_split_oscillation(&mut tracking, var, &rat(5 + i)));
    }
    assert_eq!(tracking[&var].1, 15);
    // Same value → count resets to 0
    assert!(!check_split_oscillation(&mut tracking, var, &rat(20)));
    assert_eq!(tracking[&var].1, 0);
}

#[test]
fn test_check_split_oscillation_independent_variables() {
    let mut tracking = SplitOscillationMap::new();
    let var_a = TermId(1);
    let var_b = TermId(2);
    // Seed both
    assert!(!check_split_oscillation(&mut tracking, var_a, &rat(0)));
    assert!(!check_split_oscillation(&mut tracking, var_b, &rat(0)));
    // Increase var_a 19 times
    for i in 1..=19 {
        assert!(!check_split_oscillation(&mut tracking, var_a, &rat(i)));
    }
    // var_b has its own count — 1 increase does not trigger
    assert!(!check_split_oscillation(&mut tracking, var_b, &rat(1)));
    assert_eq!(tracking[&var_b].1, 1);
    // var_a's 20th triggers
    assert!(check_split_oscillation(&mut tracking, var_a, &rat(20)));
}

#[test]
fn test_create_disequality_split_atoms_skips_non_numeric_variables() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Bool);
    let split = z4_core::DisequalitySplitRequest {
        variable: b,
        excluded_value: rat(1),
        disequality_term: None,
        is_distinct: false,
    };

    assert!(matches!(
        create_disequality_split_atoms(&mut terms, &split),
        DisequalitySplitAtoms::Skip
    ));
}

#[test]
fn test_create_disequality_split_atoms_int_fractional_uses_floor_ceil_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let split = z4_core::DisequalitySplitRequest {
        variable: x,
        excluded_value: BigRational::new(BigInt::from(7), BigInt::from(2)),
        disequality_term: None,
        is_distinct: false,
    };

    let three = terms.mk_int(BigInt::from(3));
    let four = terms.mk_int(BigInt::from(4));
    let expected_le = terms.mk_le(x, three);
    let expected_ge = terms.mk_ge(x, four);

    match create_disequality_split_atoms(&mut terms, &split) {
        DisequalitySplitAtoms::IntFractional { le, ge } => {
            assert_eq!(le, expected_le);
            assert_eq!(ge, expected_ge);
        }
        _ => panic!("expected IntFractional split atoms"),
    }
}

#[test]
fn test_create_disequality_split_atoms_int_exact_preserves_context() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let eq = terms.mk_eq(x, five);
    let diseq = terms.mk_not(eq);
    let split = z4_core::DisequalitySplitRequest {
        variable: x,
        excluded_value: rat(5),
        disequality_term: Some(diseq),
        is_distinct: true,
    };

    let four = terms.mk_int(BigInt::from(4));
    let six = terms.mk_int(BigInt::from(6));
    let expected_le = terms.mk_le(x, four);
    let expected_ge = terms.mk_ge(x, six);

    match create_disequality_split_atoms(&mut terms, &split) {
        DisequalitySplitAtoms::IntExact {
            le,
            ge,
            disequality_term,
            is_distinct,
        } => {
            assert_eq!(le, expected_le);
            assert_eq!(ge, expected_ge);
            assert_eq!(disequality_term, Some(diseq));
            assert!(is_distinct);
        }
        _ => panic!("expected IntExact split atoms"),
    }
}

#[test]
fn test_create_disequality_split_atoms_real_uses_strict_inequalities() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let excluded_term_for_eq =
        terms.mk_rational(BigRational::new(BigInt::from(9), BigInt::from(4)));
    let eq = terms.mk_eq(x, excluded_term_for_eq);
    let excluded = BigRational::new(BigInt::from(9), BigInt::from(4));
    let split = z4_core::DisequalitySplitRequest {
        variable: x,
        excluded_value: excluded.clone(),
        disequality_term: Some(eq),
        is_distinct: false,
    };

    let excluded_term = terms.mk_rational(excluded);
    let expected_lt = terms.mk_lt(x, excluded_term);
    let expected_gt = terms.mk_gt(x, excluded_term);

    match create_disequality_split_atoms(&mut terms, &split) {
        DisequalitySplitAtoms::Real {
            lt,
            gt,
            disequality_term,
            is_distinct,
        } => {
            assert_eq!(lt, expected_lt);
            assert_eq!(gt, expected_gt);
            assert_eq!(disequality_term, Some(eq));
            assert!(!is_distinct);
        }
        _ => panic!("expected Real split atoms"),
    }
}

#[test]
fn test_create_int_split_atoms_real_sort_uses_rational_constants_and_prefer_ceil() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let split = z4_core::SplitRequest {
        variable: x,
        value: BigRational::new(BigInt::from(7), BigInt::from(4)),
        floor: BigInt::from(1),
        ceil: BigInt::from(2),
    };

    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let expected_le = terms.mk_le(x, one);
    let expected_ge = terms.mk_ge(x, two);

    let (le, ge, prefer_ceil) = create_int_split_atoms(&mut terms, &split);
    assert_eq!(le, expected_le);
    assert_eq!(ge, expected_ge);
    assert_eq!(prefer_ceil, Some(true));
}

#[test]
fn test_create_int_split_atoms_exact_half_prefers_floor_first() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let split = z4_core::SplitRequest {
        variable: x,
        value: BigRational::new(BigInt::from(3), BigInt::from(2)),
        floor: BigInt::from(1),
        ceil: BigInt::from(2),
    };

    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let expected_le = terms.mk_le(x, one);
    let expected_ge = terms.mk_ge(x, two);

    let (le, ge, prefer_ceil) = create_int_split_atoms(&mut terms, &split);
    assert_eq!(le, expected_le);
    assert_eq!(ge, expected_ge);
    assert_eq!(prefer_ceil, Some(false));
}
