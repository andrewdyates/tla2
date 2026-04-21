// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Farkas lemma based constraint combination
//!
//! This module implements Farkas-based combination of linear constraints
//! for generating interpolants in PDR. When a set of linear inequalities
//! is UNSAT, Farkas' lemma guarantees there exist non-negative coefficients
//! that when used to combine the inequalities, produce a contradiction.
//!
//! The combined constraint is often more general than the original constraints,
//! making it useful for lemma generalization in PDR.
//!
//! ## Algorithm
//!
//! Given constraints: a₁·x ≤ b₁, a₂·x ≤ b₂, ..., aₙ·x ≤ bₙ that are UNSAT,
//! find λ₁, ..., λₙ ≥ 0 such that:
//! - Σᵢ λᵢ·aᵢ = 0  (coefficients cancel)
//! - Σᵢ λᵢ·bᵢ < 0  (RHS is negative)
//!
//! The combined constraint Σᵢ λᵢ·(aᵢ·x - bᵢ) ≤ 0 is a valid lemma.

mod combine;
mod interpolant;
mod linear;
mod normalize;

pub(crate) use combine::farkas_combine;
pub(crate) use interpolant::compute_interpolant;
pub(crate) use linear::{
    checked_r64_add, checked_r64_mul, parse_linear_constraint, parse_linear_constraints_split_eq,
    LinearConstraint,
};

// Re-exports for tests (visible via `use super::*` in tests.rs)
#[cfg(test)]
use crate::proof_interpolation::rational64_abs;
#[cfg(test)]
use interpolant::{is_valid_interpolant, try_pairwise_eliminate_non_shared};
#[cfg(test)]
use linear::{
    ceil_rational64, floor_rational64, linear_constraint_to_int_bound,
    parse_linear_constraints_flat, IntBound,
};

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use num_rational::Rational64;
use rustc_hash::FxHashMap;
#[cfg(test)]
use rustc_hash::FxHashSet;
use std::sync::Arc;

use normalize::lcm;

/// Build a ChcExpr from a linear constraint: Σᵢ aᵢ·xᵢ ≤ b (or <)
///
/// Per Z3's `normalize_coeffs()` in smt_farkas_util.cpp, we scale the entire
/// constraint by the LCM of all denominators to produce integer coefficients.
/// This is necessary because Farkas combination can produce rational coefficients
/// even from integer input constraints.
pub(crate) fn build_linear_inequality(
    coeffs: &FxHashMap<String, Rational64>,
    bound: Rational64,
    strict: bool,
) -> ChcExpr {
    if coeffs.is_empty() {
        // Pure constant comparison: 0 ≤ bound or 0 < bound
        let result = if strict {
            Rational64::from_integer(0) < bound
        } else {
            Rational64::from_integer(0) <= bound
        };
        return ChcExpr::Bool(result);
    }

    // Compute LCM of all denominators (coefficients and bound) per Z3 pattern
    // Reference: z3/src/smt/smt_farkas_util.cpp:100-108
    let mut denom_lcm: i64 = 1;
    for coeff in coeffs.values() {
        denom_lcm = lcm(denom_lcm, *coeff.denom());
    }
    denom_lcm = lcm(denom_lcm, *bound.denom());

    // Build LHS: Σᵢ (aᵢ * lcm)·xᵢ (now with integer coefficients)
    let mut terms: Vec<ChcExpr> = Vec::new();
    let mut sorted_vars: Vec<_> = coeffs.iter().collect();
    sorted_vars.sort_by(|a, b| a.0.cmp(b.0));

    for (var_name, coeff) in sorted_vars {
        let var = ChcVar::new(var_name, ChcSort::Int);
        let var_expr = ChcExpr::var(var);

        // Scale coefficient by LCM to get integer using i128 to avoid overflow.
        // coeff * denom_lcm should produce an integer (denom divides LCM).
        let cn = i128::from(*coeff.numer());
        let cd = i128::from(*coeff.denom());
        let lcm128 = i128::from(denom_lcm);
        let scaled = cn * lcm128 / cd;
        let numer =
            i64::try_from(scaled).unwrap_or(if scaled > 0 { i64::MAX } else { i64::MIN + 1 });

        if numer == 0 {
            continue; // Skip zero coefficients
        } else if numer == 1 {
            terms.push(var_expr);
        } else if numer == -1 {
            terms.push(ChcExpr::neg(var_expr));
        } else {
            // Handle both positive (> 1) and negative (< -1) cases
            terms.push(ChcExpr::mul(ChcExpr::Int(numer), var_expr));
        }
    }

    // Scale bound by LCM using i128 to avoid overflow.
    let bn = i128::from(*bound.numer());
    let bd = i128::from(*bound.denom());
    let lcm128 = i128::from(denom_lcm);
    let scaled_bound_128 = bn * lcm128 / bd;

    // Handle case where all coefficients became zero after scaling
    if terms.is_empty() {
        let result = if strict {
            0 < scaled_bound_128
        } else {
            0 <= scaled_bound_128
        };
        return ChcExpr::Bool(result);
    }

    let lhs = if terms.len() == 1 {
        terms.pop().expect("len == 1")
    } else {
        ChcExpr::Op(ChcOp::Add, terms.into_iter().map(Arc::new).collect())
    };

    // Build RHS from i128, saturating to i64 range.
    let rhs_i64 = i64::try_from(scaled_bound_128).unwrap_or(if scaled_bound_128 > 0 {
        i64::MAX
    } else {
        i64::MIN + 1
    });
    let rhs = ChcExpr::Int(rhs_i64);

    // Build comparison
    if strict {
        ChcExpr::lt(lhs, rhs)
    } else {
        ChcExpr::le(lhs, rhs)
    }
}

/// Normalize a linear inequality expression by clearing fractions and dividing
/// integer coefficients by their GCD when possible.
///
/// Returns `None` when `expr` is not a supported linear inequality or when the
/// normalized form is identical to the parsed constraint.
pub(crate) fn normalize_linear_inequality_expr(expr: &ChcExpr) -> Option<ChcExpr> {
    let parsed = match expr {
        ChcExpr::Op(ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt, args) if args.len() == 2 => {
            parse_linear_constraint(expr)?
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
            ChcExpr::Op(ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt, inner)
                if inner.len() == 2 =>
            {
                parse_linear_constraint(expr)?
            }
            _ => return None,
        },
        _ => return None,
    };

    let normalized = normalize::normalize_constraint(parsed.clone());
    if normalized == parsed {
        return None;
    }

    Some(
        build_linear_inequality(&normalized.coeffs, normalized.bound, normalized.strict)
            .simplify_constants(),
    )
}

#[cfg(test)]
mod tests;
