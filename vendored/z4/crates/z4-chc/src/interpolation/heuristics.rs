// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use rustc_hash::{FxHashMap, FxHashSet};

/// Compute a simple bound interpolant from A and B constraints.
///
/// Looks for cases where A implies a bound on a shared variable
/// that contradicts B.
pub(super) fn compute_bound_interpolant(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    // Extract bounds from A constraints.
    let a_bounds = extract_variable_bounds(a_constraints);

    // Extract bounds from B constraints.
    let b_bounds = extract_variable_bounds(b_constraints);

    // Look for contradicting bounds on shared variables.
    for (var, (a_lower, a_upper)) in &a_bounds {
        if !shared_vars.contains(var) {
            continue;
        }

        if let Some((b_lower, b_upper)) = b_bounds.get(var) {
            // A says var >= a_lower, B says var < b_upper where b_upper <= a_lower.
            if let (Some(a_lb), Some(b_ub)) = (a_lower, b_upper) {
                if *b_ub < *a_lb {
                    let v = ChcVar::new(var, ChcSort::Int);
                    return Some(ChcExpr::ge(ChcExpr::var(v), ChcExpr::Int(*a_lb)));
                }
            }

            // A says var <= a_upper, B says var > b_lower where b_lower >= a_upper.
            if let (Some(a_ub), Some(b_lb)) = (a_upper, b_lower) {
                if *b_lb > *a_ub {
                    let v = ChcVar::new(var, ChcSort::Int);
                    return Some(ChcExpr::le(ChcExpr::var(v), ChcExpr::Int(*a_ub)));
                }
            }
        }
    }

    None
}

/// Compute a transitivity-based interpolant.
///
/// For constraint chains like: A says x <= y, B says y < x,
/// derive contradiction and produce interpolant involving shared variables.
pub(super) fn compute_transitivity_interpolant(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    // Extract relational constraints from A (x <= y + c, x < y + c, etc.).
    let a_relations = extract_relational_constraints(a_constraints);

    // Extract relational constraints from B.
    let b_relations = extract_relational_constraints(b_constraints);

    // Look for transitivity contradictions.
    // A: x - y <= c1, B: y - x <= c2 where c1 + c2 < 0 is contradiction.
    for (a_vars, a_bound) in &a_relations {
        if a_vars.0 == a_vars.1 {
            continue;
        }

        // Look for opposite relation in B.
        let opposite = (a_vars.1.clone(), a_vars.0.clone());
        for (b_vars, b_bound) in &b_relations {
            if *b_vars == opposite
                && a_bound + b_bound < 0
                && shared_vars.contains(&a_vars.0)
                && shared_vars.contains(&a_vars.1)
            {
                let x = ChcVar::new(&a_vars.0, ChcSort::Int);
                let y = ChcVar::new(&a_vars.1, ChcSort::Int);
                return Some(ChcExpr::le(
                    ChcExpr::sub(ChcExpr::var(x), ChcExpr::var(y)),
                    ChcExpr::Int(*a_bound),
                ));
            }
        }
    }

    None
}

/// Extract a simple bound from an expression: var <= c or var >= c.
/// Returns (variable_name, bound_value, is_upper_bound).
pub(super) fn extract_simple_bound(expr: &ChcExpr) -> Option<(String, i64, bool)> {
    match expr {
        // var <= c  OR  c <= var (=> var >= c)
        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), *c, true))
                }
                (ChcExpr::Int(c), ChcExpr::Var(v)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), *c, false))
                }
                _ => None,
            }
        }
        // var < c (=> var <= c-1)  OR  c < var (=> var >= c+1)
        ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), *c - 1, true))
                }
                (ChcExpr::Int(c), ChcExpr::Var(v)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), *c + 1, false))
                }
                _ => None,
            }
        }
        // var >= c  OR  c >= var (=> var <= c)
        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), *c, false))
                }
                (ChcExpr::Int(c), ChcExpr::Var(v)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), *c, true))
                }
                _ => None,
            }
        }
        // var > c (=> var >= c+1)  OR  c > var (=> var <= c-1)
        ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), *c + 1, false))
                }
                (ChcExpr::Int(c), ChcExpr::Var(v)) if matches!(v.sort, ChcSort::Int) => {
                    Some((v.name.clone(), *c - 1, true))
                }
                _ => None,
            }
        }
        // var = c  =>  var >= c AND var <= c
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) | (ChcExpr::Int(c), ChcExpr::Var(v))
                    if matches!(v.sort, ChcSort::Int) =>
                {
                    // Return as lower bound; caller should handle both.
                    Some((v.name.clone(), *c, false))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Extract variable bounds from a list of constraints.
/// Returns map from variable name to (Option<lower_bound>, Option<upper_bound>).
fn extract_variable_bounds(
    constraints: &[ChcExpr],
) -> FxHashMap<String, (Option<i64>, Option<i64>)> {
    let mut bounds: FxHashMap<String, (Option<i64>, Option<i64>)> = FxHashMap::default();

    for c in constraints {
        if let Some((var, bound, is_upper)) = extract_simple_bound(c) {
            let entry = bounds.entry(var).or_insert((None, None));
            if is_upper {
                entry.1 = Some(entry.1.map_or(bound, |b| b.min(bound)));
            } else {
                entry.0 = Some(entry.0.map_or(bound, |b| b.max(bound)));
            }
        }
    }

    bounds
}

/// Extract relational constraints of form x - y <= c.
/// Returns list of ((x, y), c) tuples.
fn extract_relational_constraints(constraints: &[ChcExpr]) -> Vec<((String, String), i64)> {
    let mut result = Vec::new();

    for c in constraints {
        if let Some(rel) = extract_difference_constraint(c) {
            result.push(rel);
        }
    }

    result
}

/// Extract a difference constraint: x - y <= c or x - y < c.
fn extract_difference_constraint(expr: &ChcExpr) -> Option<((String, String), i64)> {
    match expr {
        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
            extract_difference_lhs(&args[0], &args[1], 0)
        }
        ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
            extract_difference_lhs(&args[0], &args[1], -1)
        }
        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
            // y >= x + c  =>  x - y <= -c
            extract_difference_lhs(&args[1], &args[0], 0).map(|((x, y), c)| ((y, x), -c))
        }
        ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
            extract_difference_lhs(&args[1], &args[0], -1).map(|((x, y), c)| ((y, x), -c))
        }
        _ => None,
    }
}

/// Extract x - y from LHS, c from RHS.
fn extract_difference_lhs(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    adjust: i64,
) -> Option<((String, String), i64)> {
    let c = match rhs {
        ChcExpr::Int(n) => *n + adjust,
        _ => return None,
    };

    match lhs {
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(x), ChcExpr::Var(y))
                    if matches!(x.sort, ChcSort::Int) && matches!(y.sort, ChcSort::Int) =>
                {
                    Some(((x.name.clone(), y.name.clone()), c))
                }
                _ => None,
            }
        }
        _ => None,
    }
}
