// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;

fn setup_term_store() -> TermStore {
    TermStore::new()
}

// ===== Tests for contains_int_mod_div_by_constant =====

#[test]
fn test_contains_mod_div_empty_formulas() {
    let terms = setup_term_store();
    assert!(!contains_int_mod_div_by_constant(&terms, &[]));
}

#[test]
fn test_contains_mod_div_no_mod_div() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let sum = terms.mk_add(vec![x, y]);

    assert!(!contains_int_mod_div_by_constant(&terms, &[sum]));
}

#[test]
fn test_contains_mod_with_constant_divisor() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let mod_expr = terms.mk_mod(x, three);

    assert!(contains_int_mod_div_by_constant(&terms, &[mod_expr]));
}

#[test]
fn test_contains_div_with_constant_divisor() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let div_expr = terms.mk_intdiv(x, five);

    assert!(contains_int_mod_div_by_constant(&terms, &[div_expr]));
}

#[test]
fn test_contains_mod_with_variable_divisor_returns_false() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let mod_expr = terms.mk_mod(x, y);

    // mod by variable, not constant - should return false
    assert!(!contains_int_mod_div_by_constant(&terms, &[mod_expr]));
}

#[test]
fn test_contains_nested_mod_div() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let mod_expr = terms.mk_mod(x, two);

    // Wrap mod in another expression
    let y = terms.mk_fresh_var("y", Sort::Int);
    let sum = terms.mk_add(vec![mod_expr, y]);

    assert!(contains_int_mod_div_by_constant(&terms, &[sum]));
}

#[test]
fn test_contains_mod_in_ite() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let mod_expr = terms.mk_mod(x, three);

    let cond = terms.mk_fresh_var("c", Sort::Bool);
    let zero = terms.mk_int(BigInt::from(0));
    let ite = terms.mk_ite(cond, mod_expr, zero);

    assert!(contains_int_mod_div_by_constant(&terms, &[ite]));
}

// ===== Tests for eliminate_int_mod_div_by_constant =====

#[test]
fn test_eliminate_no_mod_div_unchanged() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let sum = terms.mk_add(vec![x, y]);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[sum]);

    assert!(result.constraints.is_empty());
    assert_eq!(result.rewritten.len(), 1);
    assert_eq!(result.rewritten[0], sum);
}

#[test]
fn test_eliminate_mod_generates_constraints() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let mod_expr = terms.mk_mod(x, three);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_expr]);

    // Should generate 3 constraints: x = k*q + r, 0 <= r, r < |k|
    assert_eq!(result.constraints.len(), 3);
    assert_eq!(result.rewritten.len(), 1);
    // The rewritten expression should be the remainder variable, not the original
    assert_ne!(result.rewritten[0], mod_expr);
}

#[test]
fn test_eliminate_div_generates_constraints() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let div_expr = terms.mk_intdiv(x, five);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[div_expr]);

    // Should generate 3 constraints: x = k*q + r, 0 <= r, r < |k|
    assert_eq!(result.constraints.len(), 3);
    assert_eq!(result.rewritten.len(), 1);
    // The rewritten expression should be the quotient variable, not the original
    assert_ne!(result.rewritten[0], div_expr);
}

#[test]
fn test_eliminate_mod_by_zero_returns_dividend() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let mod_expr = terms.mk_mod(x, zero);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_expr]);

    // SMT-LIB total semantics: (mod x 0) = x
    assert!(result.constraints.is_empty());
    assert_eq!(result.rewritten.len(), 1);
    assert_eq!(result.rewritten[0], x);
}

#[test]
fn test_eliminate_div_by_zero_returns_zero() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let div_expr = terms.mk_intdiv(x, zero);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[div_expr]);

    // SMT-LIB total semantics: (div x 0) = 0
    assert!(result.constraints.is_empty());
    assert_eq!(result.rewritten.len(), 1);

    // Check the result is the integer 0
    if let TermData::Const(Constant::Int(n)) = terms.get(result.rewritten[0]) {
        assert_eq!(*n, BigInt::from(0));
    } else {
        panic!("Expected integer constant 0");
    }
}

#[test]
fn test_eliminate_with_negative_divisor() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let neg_three = terms.mk_int(BigInt::from(-3));
    let mod_expr = terms.mk_mod(x, neg_three);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_expr]);

    // Should generate constraints with |k| = 3
    assert_eq!(result.constraints.len(), 3);

    // Verify that one constraint has r < 3 (not r < -3)
    let mut found_r_lt_abs_k = false;
    for constraint in &result.constraints {
        if let TermData::App(Symbol::Named(name), args) = terms.get(*constraint) {
            if name == "<" && args.len() == 2 {
                if let TermData::Const(Constant::Int(n)) = terms.get(args[1]) {
                    if *n == BigInt::from(3) {
                        found_r_lt_abs_k = true;
                    }
                }
            }
        }
    }
    assert!(found_r_lt_abs_k, "Expected constraint r < |k| = 3");
}

#[test]
fn test_eliminate_nested_mod_div() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));

    // (mod (div x 3) 2)
    let div_expr = terms.mk_intdiv(x, three);
    let mod_expr = terms.mk_mod(div_expr, two);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_expr]);

    // Should generate constraints for both div and mod
    // div: 3 constraints, mod: 3 constraints = 6 total
    assert_eq!(result.constraints.len(), 6);
}

#[test]
fn test_eliminate_multiple_formulas() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));

    let mod_x = terms.mk_mod(x, two);
    let div_y = terms.mk_intdiv(y, three);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_x, div_y]);

    // 3 constraints for mod + 3 constraints for div = 6 total
    assert_eq!(result.constraints.len(), 6);
    assert_eq!(result.rewritten.len(), 2);
}

#[test]
fn test_eliminate_preserves_other_terms() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));

    // Mix of mod and non-mod expressions
    let mod_expr = terms.mk_mod(x, three);
    let plain_add = terms.mk_add(vec![x, y]);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_expr, plain_add]);

    assert_eq!(result.constraints.len(), 3); // Only mod generates constraints
    assert_eq!(result.rewritten.len(), 2);
    assert_eq!(result.rewritten[1], plain_add); // Plain add unchanged
}

// ===== Tests for constraint correctness =====

#[test]
fn test_mod_constraints_structure() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let mod_expr = terms.mk_mod(x, five);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_expr]);

    // Verify constraint structure:
    // 1. Equality constraint: x = k*q + r
    // 2. Lower bound: 0 <= r (mk_ge(r, zero) normalizes to mk_le(zero, r))
    // 3. Upper bound: r < |k|

    let mut has_eq = false;
    let mut has_le = false; // mk_ge(r, zero) normalized to mk_le(zero, r)
    let mut has_lt = false;

    for constraint in &result.constraints {
        if let TermData::App(Symbol::Named(name), _) = terms.get(*constraint) {
            match name.as_str() {
                "=" => has_eq = true,
                "<=" => has_le = true,
                "<" => has_lt = true,
                _ => {}
            }
        }
    }

    assert!(has_eq, "Missing equality constraint x = k*q + r");
    assert!(has_le, "Missing lower bound constraint 0 <= r");
    assert!(has_lt, "Missing upper bound constraint r < |k|");
}

#[test]
fn test_mod_div_same_expression_share_constraints() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));

    // (mod x 3) and (div x 3) on the same dividend
    let mod_expr = terms.mk_mod(x, three);
    let div_expr = terms.mk_intdiv(x, three);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_expr, div_expr]);

    // Each generates its own fresh q,r variables, so 6 constraints total
    // (no sharing in current implementation - could be optimized)
    assert_eq!(result.constraints.len(), 6);
}

#[test]
fn test_not_wrapping_preserved() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let mod_expr = terms.mk_mod(x, three);
    let zero = terms.mk_int(BigInt::from(0));
    let eq = terms.mk_eq(mod_expr, zero);
    let not_eq = terms.mk_not(eq);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[not_eq]);

    // Should rewrite the inner mod but preserve the not structure
    assert_eq!(result.constraints.len(), 3);

    // Check that the result is a Not node
    if let TermData::Not(_) = terms.get(result.rewritten[0]) {
        // Good - Not structure preserved
    } else {
        panic!("Expected Not wrapper to be preserved");
    }
}

#[test]
fn test_ite_preserved() {
    let mut terms = setup_term_store();
    let cond = terms.mk_fresh_var("c", Sort::Bool);
    let x = terms.mk_fresh_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let mod_expr = terms.mk_mod(x, three);
    let one = terms.mk_int(BigInt::from(1));

    let ite = terms.mk_ite(cond, mod_expr, one);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[ite]);

    // Should rewrite the mod in the then branch
    assert_eq!(result.constraints.len(), 3);

    // Check that the result is still an ITE
    if let TermData::Ite(_, _, _) = terms.get(result.rewritten[0]) {
        // Good - ITE structure preserved
    } else {
        panic!("Expected ITE wrapper to be preserved");
    }
}

#[test]
fn test_memoization_prevents_duplicate_constraints() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let mod_expr = terms.mk_mod(x, three);

    // Use the same mod expression twice
    let sum = terms.mk_add(vec![mod_expr, mod_expr]);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[sum]);

    // Should only generate 3 constraints (memoization)
    assert_eq!(result.constraints.len(), 3);
}
