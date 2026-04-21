// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear constraint types and parsing for Farkas combination.
//!
//! Provides `LinearConstraint`, parsing from `ChcExpr`, checked Rational64
//! arithmetic, integer bound extraction, and floor/ceil rounding.

use crate::expr::walk_linear_expr;
use crate::{ChcExpr, ChcOp, ChcSort};
use num_rational::Rational64;
use rustc_hash::FxHashMap;

/// Checked addition for Rational64 that returns None on i64 overflow.
///
/// Rational64 operations internally cross-multiply numerators and
/// denominators, which can overflow i64. With `panic = "abort"` in
/// release, this causes a hard crash. This function detects overflow
/// via i128 intermediates before performing the operation.
pub(crate) fn checked_r64_add(a: Rational64, b: Rational64) -> Option<Rational64> {
    let an = i128::from(*a.numer());
    let ad = i128::from(*a.denom());
    let bn = i128::from(*b.numer());
    let bd = i128::from(*b.denom());
    // a/ad + b/bd = (an*bd + bn*ad) / (ad*bd)
    let num = an.checked_mul(bd)?.checked_add(bn.checked_mul(ad)?)?;
    let den = ad.checked_mul(bd)?;
    let num_i64 = i64::try_from(num).ok()?;
    let den_i64 = i64::try_from(den).ok()?;
    if den_i64 == 0 {
        return None;
    }
    Some(Rational64::new(num_i64, den_i64))
}

/// Checked multiplication for Rational64 that returns None on i64 overflow.
pub(crate) fn checked_r64_mul(a: Rational64, b: Rational64) -> Option<Rational64> {
    let an = i128::from(*a.numer());
    let ad = i128::from(*a.denom());
    let bn = i128::from(*b.numer());
    let bd = i128::from(*b.denom());
    let num = an.checked_mul(bn)?;
    let den = ad.checked_mul(bd)?;
    let num_i64 = i64::try_from(num).ok()?;
    let den_i64 = i64::try_from(den).ok()?;
    if den_i64 == 0 {
        return None;
    }
    Some(Rational64::new(num_i64, den_i64))
}

/// Checked negation for Rational64 that returns None on i64::MIN.
pub(super) fn checked_r64_neg(a: Rational64) -> Option<Rational64> {
    let n = (*a.numer()).checked_neg()?;
    Some(Rational64::new(n, *a.denom()))
}

/// Checked division for Rational64 that returns None on i64 overflow or division by zero.
pub(super) fn checked_r64_div(a: Rational64, b: Rational64) -> Option<Rational64> {
    let an = i128::from(*a.numer());
    let ad = i128::from(*a.denom());
    let bn = i128::from(*b.numer());
    let bd = i128::from(*b.denom());
    if bn == 0 {
        return None;
    }
    let num = an.checked_mul(bd)?;
    let den = ad.checked_mul(bn)?;
    let num_i64 = i64::try_from(num).ok()?;
    let den_i64 = i64::try_from(den).ok()?;
    if den_i64 == 0 {
        return None;
    }
    Some(Rational64::new(num_i64, den_i64))
}

/// A linear constraint in the form: Σᵢ aᵢ·xᵢ ≤ b (or < for strict)
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LinearConstraint {
    /// Variable name -> coefficient
    pub(crate) coeffs: FxHashMap<String, Rational64>,
    /// Constant bound (RHS)
    pub(crate) bound: Rational64,
    /// Whether this is strict (< vs ≤)
    pub(crate) strict: bool,
}

impl LinearConstraint {
    pub(super) fn new(bound: Rational64, strict: bool) -> Self {
        Self {
            coeffs: FxHashMap::default(),
            bound,
            strict,
        }
    }

    pub(super) fn set_coeff(&mut self, var: &str, coeff: Rational64) {
        if coeff == Rational64::from_integer(0) {
            self.coeffs.remove(var);
        } else {
            self.coeffs.insert(var.to_string(), coeff);
        }
    }

    pub(crate) fn get_coeff(&self, var: &str) -> Rational64 {
        self.coeffs
            .get(var)
            .copied()
            .unwrap_or(Rational64::from_integer(0))
    }
}

/// Try to parse a ChcExpr as a linear constraint.
/// Returns None if the expression is not a linear inequality.
pub(crate) fn parse_linear_constraint(expr: &ChcExpr) -> Option<LinearConstraint> {
    match expr {
        // a ≤ b  =>  a - b ≤ 0
        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
            let mut constraint = LinearConstraint::new(Rational64::from_integer(0), false);
            add_linear_expr(&args[0], Rational64::from_integer(1), &mut constraint)?;
            add_linear_expr(&args[1], Rational64::from_integer(-1), &mut constraint)?;
            Some(constraint)
        }
        // a < b  =>  a - b < 0
        ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
            let mut constraint = LinearConstraint::new(Rational64::from_integer(0), true);
            add_linear_expr(&args[0], Rational64::from_integer(1), &mut constraint)?;
            add_linear_expr(&args[1], Rational64::from_integer(-1), &mut constraint)?;
            Some(constraint)
        }
        // a ≥ b  =>  b - a ≤ 0
        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
            let mut constraint = LinearConstraint::new(Rational64::from_integer(0), false);
            add_linear_expr(&args[1], Rational64::from_integer(1), &mut constraint)?;
            add_linear_expr(&args[0], Rational64::from_integer(-1), &mut constraint)?;
            Some(constraint)
        }
        // a > b  =>  b - a < 0
        ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
            let mut constraint = LinearConstraint::new(Rational64::from_integer(0), true);
            add_linear_expr(&args[1], Rational64::from_integer(1), &mut constraint)?;
            add_linear_expr(&args[0], Rational64::from_integer(-1), &mut constraint)?;
            Some(constraint)
        }
        // a = b  =>  a - b ≤ 0 AND b - a ≤ 0 (we return one direction)
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            // For equalities, we treat as a <= b (caller may want both directions)
            let mut constraint = LinearConstraint::new(Rational64::from_integer(0), false);
            add_linear_expr(&args[0], Rational64::from_integer(1), &mut constraint)?;
            add_linear_expr(&args[1], Rational64::from_integer(-1), &mut constraint)?;
            Some(constraint)
        }
        // Handle negated comparisons
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            match args[0].as_ref() {
                // NOT(a ≤ b)  =>  a > b  =>  b - a < 0
                ChcExpr::Op(ChcOp::Le, inner_args) if inner_args.len() == 2 => {
                    let mut constraint = LinearConstraint::new(Rational64::from_integer(0), true);
                    add_linear_expr(&inner_args[1], Rational64::from_integer(1), &mut constraint)?;
                    add_linear_expr(
                        &inner_args[0],
                        Rational64::from_integer(-1),
                        &mut constraint,
                    )?;
                    Some(constraint)
                }
                // NOT(a < b)  =>  a ≥ b  =>  b - a ≤ 0
                ChcExpr::Op(ChcOp::Lt, inner_args) if inner_args.len() == 2 => {
                    let mut constraint = LinearConstraint::new(Rational64::from_integer(0), false);
                    add_linear_expr(&inner_args[1], Rational64::from_integer(1), &mut constraint)?;
                    add_linear_expr(
                        &inner_args[0],
                        Rational64::from_integer(-1),
                        &mut constraint,
                    )?;
                    Some(constraint)
                }
                // NOT(a ≥ b)  =>  a < b  =>  a - b < 0
                ChcExpr::Op(ChcOp::Ge, inner_args) if inner_args.len() == 2 => {
                    let mut constraint = LinearConstraint::new(Rational64::from_integer(0), true);
                    add_linear_expr(&inner_args[0], Rational64::from_integer(1), &mut constraint)?;
                    add_linear_expr(
                        &inner_args[1],
                        Rational64::from_integer(-1),
                        &mut constraint,
                    )?;
                    Some(constraint)
                }
                // NOT(a > b)  =>  a ≤ b  =>  a - b ≤ 0
                ChcExpr::Op(ChcOp::Gt, inner_args) if inner_args.len() == 2 => {
                    let mut constraint = LinearConstraint::new(Rational64::from_integer(0), false);
                    add_linear_expr(&inner_args[0], Rational64::from_integer(1), &mut constraint)?;
                    add_linear_expr(
                        &inner_args[1],
                        Rational64::from_integer(-1),
                        &mut constraint,
                    )?;
                    Some(constraint)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Parse a ChcExpr as zero or more linear constraints.
/// Recursively flattens conjunctions and returns every parseable member.
pub(crate) fn parse_linear_constraints_flat(expr: &ChcExpr) -> Vec<LinearConstraint> {
    match expr {
        ChcExpr::Op(ChcOp::And, args) => args
            .iter()
            .flat_map(|arg| parse_linear_constraints_flat(arg))
            .collect(),
        _ => parse_linear_constraint(expr).into_iter().collect(),
    }
}

/// Parse a linear constraint, splitting equalities into both directions.
/// `a = b` becomes `[a - b <= 0, b - a <= 0]`.
/// Non-equalities return a single constraint (or empty if not parseable).
pub(crate) fn parse_linear_constraints_split_eq(expr: &ChcExpr) -> Vec<LinearConstraint> {
    match expr {
        ChcExpr::Op(ChcOp::And, args) => args
            .iter()
            .flat_map(|arg| parse_linear_constraints_split_eq(arg))
            .collect(),
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            let mut results = Vec::new();
            // Direction 1: a - b <= 0
            let mut c1 = LinearConstraint::new(Rational64::from_integer(0), false);
            if add_linear_expr(&args[0], Rational64::from_integer(1), &mut c1).is_some()
                && add_linear_expr(&args[1], Rational64::from_integer(-1), &mut c1).is_some()
            {
                results.push(c1);
            }
            // Direction 2: b - a <= 0
            let mut c2 = LinearConstraint::new(Rational64::from_integer(0), false);
            if add_linear_expr(&args[1], Rational64::from_integer(1), &mut c2).is_some()
                && add_linear_expr(&args[0], Rational64::from_integer(-1), &mut c2).is_some()
            {
                results.push(c2);
            }
            results
        }
        _ => parse_linear_constraint(expr).into_iter().collect(),
    }
}

/// Add a linear expression to a constraint with a multiplier.
/// Returns None if the expression is not linear.
fn add_linear_expr(
    expr: &ChcExpr,
    mult: Rational64,
    constraint: &mut LinearConstraint,
) -> Option<()> {
    // Split borrows so both closures can access disjoint fields.
    let bound = &mut constraint.bound;
    let coeffs = &mut constraint.coeffs;
    walk_linear_expr(
        expr,
        mult,
        &mut |m, n| {
            let term = checked_r64_mul(m, Rational64::from_integer(n))?;
            *bound = checked_r64_add(*bound, checked_r64_neg(term)?)?;
            Some(())
        },
        &mut |m, v| {
            if !matches!(v.sort, ChcSort::Int) {
                return None;
            }
            let zero = Rational64::from_integer(0);
            let current = coeffs.get(&v.name).copied().unwrap_or(zero);
            let new_val = checked_r64_add(current, m)?;
            if new_val == zero {
                coeffs.remove(&v.name);
            } else {
                coeffs.insert(v.name.clone(), new_val);
            }
            Some(())
        },
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum IntBound {
    Lower(i64),
    Upper(i64),
}

pub(super) fn floor_rational64(r: Rational64) -> Option<i64> {
    let n = i128::from(*r.numer());
    let d = i128::from(*r.denom());
    // Denominator must be positive for correct Euclidean division (#3095).
    if d <= 0 {
        safe_eprintln!("BUG: floor_rational64: non-positive denominator {d}");
        return None;
    }
    i64::try_from(n.div_euclid(d)).ok()
}

pub(super) fn ceil_rational64(r: Rational64) -> Option<i64> {
    let n = i128::from(*r.numer());
    let d = i128::from(*r.denom());
    // Denominator must be positive for correct Euclidean division (#3095).
    if d <= 0 {
        safe_eprintln!("BUG: ceil_rational64: non-positive denominator {d}");
        return None;
    }
    i64::try_from(-((-n).div_euclid(d))).ok()
}

pub(super) fn linear_constraint_to_int_bound(c: &LinearConstraint) -> Option<(String, IntBound)> {
    if c.coeffs.len() != 1 {
        return None;
    }
    let (var, coeff) = c.coeffs.iter().next()?;
    if *coeff == Rational64::from_integer(0) {
        return None;
    }

    // c is: coeff * x <= bound (or < if strict).
    // Divide by coeff to isolate x, taking care with strictness/rounding over Int.
    let r = checked_r64_div(c.bound, *coeff)?;
    if *coeff > Rational64::from_integer(0) {
        // x <= r  (or x < r if strict)
        let upper = if c.strict {
            // x < r  over Int  =>  x <= ceil(r) - 1
            let ceil_r = i128::from(ceil_rational64(r)?);
            i64::try_from(ceil_r - 1).ok()?
        } else {
            // x <= r  over Int  =>  x <= floor(r)
            floor_rational64(r)?
        };
        Some((var.clone(), IntBound::Upper(upper)))
    } else {
        // x >= r  (or x > r if strict)
        let lower = if c.strict {
            // x > r  over Int  =>  x >= floor(r) + 1
            let floor_r = i128::from(floor_rational64(r)?);
            i64::try_from(floor_r + 1).ok()?
        } else {
            // x >= r  over Int  =>  x >= ceil(r)
            ceil_rational64(r)?
        };
        Some((var.clone(), IntBound::Lower(lower)))
    }
}
