// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constant simplification for CHC expressions.
//!
//! Extracted from methods.rs — the `simplify_constants` method and its
//! helper `bv_signed_cmp`.

use std::sync::Arc;

use super::{
    maybe_grow_expr_stack, smt_euclid_div, smt_euclid_mod, ChcExpr, ChcOp,
    MAX_EXPR_RECURSION_DEPTH, MAX_PREPROCESSING_NODES,
};

impl ChcExpr {
    /// Simplify constant expressions, especially mod with constant arguments.
    ///
    /// Uses a node budget (#2771) to prevent unbounded heap allocation on
    /// pathological expression trees. On budget exhaustion, returns `self`
    /// unchanged — semantically correct, just unsimplified.
    pub(crate) fn simplify_constants(&self) -> Self {
        use std::cell::Cell;

        let budget = Cell::new(MAX_PREPROCESSING_NODES);

        fn simplify_inner(expr: &ChcExpr, budget: &Cell<usize>, depth: usize) -> Option<ChcExpr> {
            maybe_grow_expr_stack(|| {
                // Depth bound (#2988): prevent unbounded stacker heap allocation.
                // At depth 500, stacker has allocated up to 1 GB of heap segments.
                if depth >= MAX_EXPR_RECURSION_DEPTH {
                    return None;
                }
                let remaining = budget.get();
                if remaining == 0 {
                    return None;
                }
                budget.set(remaining - 1);

                Some(match expr {
                    ChcExpr::Bool(_)
                    | ChcExpr::Int(_)
                    | ChcExpr::Real(_, _)
                    | ChcExpr::BitVec(_, _)
                    | ChcExpr::Var(_) => expr.clone(),
                    ChcExpr::Op(op, args) => {
                        // First simplify all arguments
                        let simplified_args: Vec<Arc<ChcExpr>> = args
                            .iter()
                            .map(|a| {
                                Arc::new(
                                    simplify_inner(a, budget, depth + 1)
                                        .unwrap_or_else(|| a.as_ref().clone()),
                                )
                            })
                            .collect();

                        // Then try to simplify this operation
                        match op {
                            ChcOp::Ite if simplified_args.len() == 3 => {
                                // ITE with constant condition
                                match simplified_args[0].as_ref() {
                                    ChcExpr::Bool(true) => simplified_args[1].as_ref().clone(),
                                    ChcExpr::Bool(false) => simplified_args[2].as_ref().clone(),
                                    _ => ChcExpr::Op(op.clone(), simplified_args),
                                }
                            }
                            ChcOp::Add if simplified_args.len() >= 2 => {
                                // Flatten nested additions and collect terms with coefficients
                                let mut constant_sum: i64 = 0;
                                let mut var_terms: Vec<Arc<ChcExpr>> = Vec::new();

                                /// Push an expression scaled by `coeff` into `var_terms`.
                                /// coeff=1 → push as-is; coeff=-1 → wrap in Neg; else → wrap in Mul.
                                fn push_scaled_term(
                                    var_terms: &mut Vec<Arc<ChcExpr>>,
                                    expr: &ChcExpr,
                                    coeff: i64,
                                ) {
                                    if coeff == 1 {
                                        var_terms.push(Arc::new(expr.clone()));
                                    } else if coeff == -1 {
                                        var_terms.push(Arc::new(ChcExpr::Op(
                                            ChcOp::Neg,
                                            vec![Arc::new(expr.clone())],
                                        )));
                                    } else {
                                        var_terms.push(Arc::new(ChcExpr::Op(
                                            ChcOp::Mul,
                                            vec![
                                                Arc::new(ChcExpr::Int(coeff)),
                                                Arc::new(expr.clone()),
                                            ],
                                        )));
                                    }
                                }

                                fn collect_add_terms(
                                    expr: &ChcExpr,
                                    coeff: i64,
                                    constant_sum: &mut i64,
                                    var_terms: &mut Vec<Arc<ChcExpr>>,
                                    budget: &Cell<usize>,
                                    depth: usize,
                                ) {
                                    // Depth bound (#2988)
                                    if depth >= MAX_EXPR_RECURSION_DEPTH {
                                        push_scaled_term(var_terms, expr, coeff);
                                        return;
                                    }
                                    let remaining = budget.get();
                                    if remaining == 0 {
                                        push_scaled_term(var_terms, expr, coeff);
                                        return;
                                    }
                                    budget.set(remaining - 1);

                                    maybe_grow_expr_stack(|| match expr {
                                        ChcExpr::Int(n) => {
                                            // Checked arithmetic: overflow → treat as opaque term (#3693)
                                            // Use coeff-aware push on bailout (same as depth/budget
                                            // bailout above) to preserve the sign when coeff = -1.
                                            if let Some(product) = coeff.checked_mul(*n) {
                                                if let Some(new_sum) =
                                                    constant_sum.checked_add(product)
                                                {
                                                    *constant_sum = new_sum;
                                                } else {
                                                    // Sum overflows: push coeff*n as separate term
                                                    var_terms.push(Arc::new(ChcExpr::Int(product)));
                                                }
                                            } else {
                                                // coeff * n overflows: preserve coeff in expression
                                                push_scaled_term(var_terms, expr, coeff);
                                            }
                                        }
                                        // (#3121) Propagate coeff through Add/Sub/Neg for
                                        // proper flattening.  Previous `coeff == 1` guards
                                        // prevented simplification of nested arithmetic
                                        // (e.g. `Add(Neg(Sub(a,b)), a)` → `b`).
                                        ChcExpr::Op(ChcOp::Add, args) => {
                                            for arg in args {
                                                collect_add_terms(
                                                    arg.as_ref(),
                                                    coeff,
                                                    constant_sum,
                                                    var_terms,
                                                    budget,
                                                    depth + 1,
                                                );
                                            }
                                        }
                                        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                                            collect_add_terms(
                                                args[0].as_ref(),
                                                coeff,
                                                constant_sum,
                                                var_terms,
                                                budget,
                                                depth + 1,
                                            );
                                            collect_add_terms(
                                                args[1].as_ref(),
                                                -coeff,
                                                constant_sum,
                                                var_terms,
                                                budget,
                                                depth + 1,
                                            );
                                        }
                                        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                                            collect_add_terms(
                                                args[0].as_ref(),
                                                -coeff,
                                                constant_sum,
                                                var_terms,
                                                budget,
                                                depth + 1,
                                            );
                                        }
                                        _ => {
                                            push_scaled_term(var_terms, expr, coeff);
                                        }
                                    });
                                }

                                for arg in &simplified_args {
                                    collect_add_terms(
                                        arg.as_ref(),
                                        1,
                                        &mut constant_sum,
                                        &mut var_terms,
                                        budget,
                                        depth + 1,
                                    );
                                }

                                // Build result
                                if var_terms.is_empty() {
                                    ChcExpr::Int(constant_sum)
                                } else if constant_sum == 0 {
                                    if var_terms.len() == 1 {
                                        return Some(var_terms[0].as_ref().clone());
                                    }
                                    ChcExpr::Op(ChcOp::Add, var_terms)
                                } else {
                                    var_terms.push(Arc::new(ChcExpr::Int(constant_sum)));
                                    ChcExpr::Op(ChcOp::Add, var_terms)
                                }
                            }
                            ChcOp::Mul if simplified_args.len() >= 2 => {
                                if simplified_args
                                    .iter()
                                    .all(|a| matches!(a.as_ref(), ChcExpr::Int(_)))
                                {
                                    // Checked arithmetic: overflow → return unsimplified (#3693)
                                    let prod = simplified_args.iter().try_fold(1i64, |acc, a| {
                                        if let ChcExpr::Int(n) = a.as_ref() {
                                            acc.checked_mul(*n)
                                        } else {
                                            Some(acc)
                                        }
                                    });
                                    if let Some(p) = prod {
                                        return Some(ChcExpr::Int(p));
                                    }
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            ChcOp::Sub | ChcOp::Div | ChcOp::Mod if simplified_args.len() == 2 => {
                                if let (ChcExpr::Int(a), ChcExpr::Int(b)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    // Checked arithmetic: overflow → return unsimplified (#3693)
                                    let result = match op {
                                        ChcOp::Sub => a.checked_sub(*b),
                                        ChcOp::Div => smt_euclid_div(*a, *b),
                                        ChcOp::Mod => smt_euclid_mod(*a, *b),
                                        _ => None, // #6091: defensive
                                    };
                                    if let Some(val) = result {
                                        return Some(ChcExpr::Int(val));
                                    }
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            ChcOp::Neg if simplified_args.len() == 1 => {
                                if let ChcExpr::Int(n) = simplified_args[0].as_ref() {
                                    // Checked arithmetic: -i64::MIN overflows (#3693)
                                    if let Some(neg) = n.checked_neg() {
                                        return Some(ChcExpr::Int(neg));
                                    }
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            ChcOp::Eq | ChcOp::Ne if simplified_args.len() == 2 => {
                                let is_eq = matches!(op, ChcOp::Eq);
                                if let (ChcExpr::Int(a), ChcExpr::Int(b)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    return Some(ChcExpr::Bool((a == b) == is_eq));
                                }
                                if let (ChcExpr::Bool(a), ChcExpr::Bool(b)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    return Some(ChcExpr::Bool((a == b) == is_eq));
                                }
                                if let (ChcExpr::BitVec(a, _), ChcExpr::BitVec(b, _)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    return Some(ChcExpr::Bool((a == b) == is_eq));
                                }
                                if simplified_args[0] == simplified_args[1] {
                                    return Some(ChcExpr::Bool(is_eq));
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge
                                if simplified_args.len() == 2 =>
                            {
                                if let (ChcExpr::Int(a), ChcExpr::Int(b)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    let result = match op {
                                        ChcOp::Lt => Some(a < b),
                                        ChcOp::Le => Some(a <= b),
                                        ChcOp::Gt => Some(a > b),
                                        ChcOp::Ge => Some(a >= b),
                                        _ => None, // #6091: defensive
                                    };
                                    if let Some(r) = result {
                                        return Some(ChcExpr::Bool(r));
                                    }
                                }
                                // #1362: Simplify reflexive comparisons (>= x x) → true, (> x x) → false
                                if simplified_args[0] == simplified_args[1] {
                                    return Some(ChcExpr::Bool(matches!(
                                        op,
                                        ChcOp::Le | ChcOp::Ge
                                    )));
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            ChcOp::Not if simplified_args.len() == 1 => {
                                if let ChcExpr::Bool(b) = simplified_args[0].as_ref() {
                                    return Some(ChcExpr::Bool(!b));
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            ChcOp::And => {
                                fn flatten_and(
                                    expr: &ChcExpr,
                                    result: &mut Vec<Arc<ChcExpr>>,
                                    depth: usize,
                                ) -> bool {
                                    // Depth bound (#2988)
                                    if depth >= MAX_EXPR_RECURSION_DEPTH {
                                        result.push(Arc::new(expr.clone()));
                                        return true;
                                    }
                                    maybe_grow_expr_stack(|| match expr {
                                        ChcExpr::Bool(true) => true,
                                        ChcExpr::Bool(false) => false,
                                        ChcExpr::Op(ChcOp::And, args) => {
                                            for arg in args {
                                                if !flatten_and(arg.as_ref(), result, depth + 1) {
                                                    return false;
                                                }
                                            }
                                            true
                                        }
                                        _ => {
                                            result.push(Arc::new(expr.clone()));
                                            true
                                        }
                                    })
                                }

                                let mut new_args = Vec::new();
                                for arg in &simplified_args {
                                    if !flatten_and(arg.as_ref(), &mut new_args, depth + 1) {
                                        return Some(ChcExpr::Bool(false));
                                    }
                                }

                                if new_args.is_empty() {
                                    return Some(ChcExpr::Bool(true));
                                }
                                if new_args.len() == 1 {
                                    return Some(new_args[0].as_ref().clone());
                                }

                                let mut positive_conjuncts: Vec<&ChcExpr> = Vec::new();
                                let mut negated_conjuncts: Vec<&ChcExpr> = Vec::new();

                                for arg in &new_args {
                                    if let ChcExpr::Op(ChcOp::Not, not_args) = arg.as_ref() {
                                        if not_args.len() == 1 {
                                            negated_conjuncts.push(not_args[0].as_ref());
                                        }
                                    } else {
                                        positive_conjuncts.push(arg.as_ref());
                                    }
                                }

                                for pos in &positive_conjuncts {
                                    for neg in &negated_conjuncts {
                                        if pos == neg {
                                            return Some(ChcExpr::Bool(false));
                                        }
                                    }
                                }

                                ChcExpr::Op(ChcOp::And, new_args)
                            }
                            ChcOp::Or => {
                                let mut new_args = Vec::new();
                                for arg in &simplified_args {
                                    match arg.as_ref() {
                                        ChcExpr::Bool(false) => {}
                                        ChcExpr::Bool(true) => return Some(ChcExpr::Bool(true)),
                                        _ => new_args.push(arg.clone()),
                                    }
                                }
                                if new_args.is_empty() {
                                    return Some(ChcExpr::Bool(false));
                                }
                                if new_args.len() == 1 {
                                    return Some(new_args[0].as_ref().clone());
                                }
                                ChcExpr::Op(ChcOp::Or, new_args)
                            }
                            ChcOp::Implies if simplified_args.len() == 2 => {
                                let lhs = simplified_args[0].as_ref();
                                let rhs = simplified_args[1].as_ref();
                                match (lhs, rhs) {
                                    (ChcExpr::Bool(false), _) => ChcExpr::Bool(true),
                                    (ChcExpr::Bool(true), _) => rhs.clone(),
                                    (_, ChcExpr::Bool(true)) => ChcExpr::Bool(true),
                                    (_, ChcExpr::Bool(false)) => {
                                        ChcExpr::Op(ChcOp::Not, vec![simplified_args[0].clone()])
                                    }
                                    _ => ChcExpr::Op(op.clone(), simplified_args),
                                }
                            }
                            // BV constant folding: concat, extract, zero/sign-extend
                            ChcOp::BvConcat if simplified_args.len() == 2 => {
                                if let (ChcExpr::BitVec(a, wa), ChcExpr::BitVec(b, wb)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    let width = wa + wb;
                                    // Can only fold if result fits in u128
                                    if width <= 128 {
                                        let mask = if width >= 128 {
                                            u128::MAX
                                        } else {
                                            (1u128 << width) - 1
                                        };
                                        return Some(ChcExpr::BitVec(
                                            ((a << wb) | b) & mask,
                                            width,
                                        ));
                                    }
                                    // width > 128: leave as BvConcat tree (can't fit in u128)
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            ChcOp::BvExtract(hi, lo) if simplified_args.len() == 1 => {
                                if let ChcExpr::BitVec(v, _w) = simplified_args[0].as_ref() {
                                    let width = hi - lo + 1;
                                    let mask = if width >= 128 {
                                        u128::MAX
                                    } else {
                                        (1u128 << width) - 1
                                    };
                                    return Some(ChcExpr::BitVec((v >> lo) & mask, width));
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            ChcOp::BvZeroExtend(n) if simplified_args.len() == 1 => {
                                if let ChcExpr::BitVec(v, w) = simplified_args[0].as_ref() {
                                    return Some(ChcExpr::BitVec(*v, w + n));
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            ChcOp::BvSignExtend(n) if simplified_args.len() == 1 => {
                                if let ChcExpr::BitVec(v, w) = simplified_args[0].as_ref() {
                                    // Sign-extend: replicate the sign bit
                                    let sign_bit = if *w > 0 { (v >> (w - 1)) & 1 } else { 0 };
                                    let new_width = w + n;
                                    let result = if sign_bit == 1 {
                                        let upper_mask = if new_width >= 128 {
                                            u128::MAX
                                        } else {
                                            (1u128 << new_width) - 1
                                        };
                                        let lower_mask = if *w >= 128 {
                                            u128::MAX
                                        } else {
                                            (1u128 << w) - 1
                                        };
                                        (v & lower_mask) | (upper_mask & !lower_mask)
                                    } else {
                                        *v
                                    };
                                    return Some(ChcExpr::BitVec(result, new_width));
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            ChcOp::BvNot if simplified_args.len() == 1 => {
                                if let ChcExpr::BitVec(v, w) = simplified_args[0].as_ref() {
                                    let mask = if *w >= 128 {
                                        u128::MAX
                                    } else {
                                        (1u128 << w) - 1
                                    };
                                    return Some(ChcExpr::BitVec(!v & mask, *w));
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            ChcOp::BvNeg if simplified_args.len() == 1 => {
                                if let ChcExpr::BitVec(v, w) = simplified_args[0].as_ref() {
                                    let mask = if *w >= 128 {
                                        u128::MAX
                                    } else {
                                        (1u128 << w) - 1
                                    };
                                    return Some(ChcExpr::BitVec(v.wrapping_neg() & mask, *w));
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            ChcOp::BvAdd
                            | ChcOp::BvSub
                            | ChcOp::BvMul
                            | ChcOp::BvAnd
                            | ChcOp::BvOr
                            | ChcOp::BvXor
                                if simplified_args.len() == 2 =>
                            {
                                if let (ChcExpr::BitVec(a, wa), ChcExpr::BitVec(b, _wb)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    let mask = if *wa >= 128 {
                                        u128::MAX
                                    } else {
                                        (1u128 << wa) - 1
                                    };
                                    let result = match op {
                                        ChcOp::BvAdd => Some(a.wrapping_add(*b) & mask),
                                        ChcOp::BvSub => Some(a.wrapping_sub(*b) & mask),
                                        ChcOp::BvMul => Some(a.wrapping_mul(*b) & mask),
                                        ChcOp::BvAnd => Some(a & b),
                                        ChcOp::BvOr => Some(a | b),
                                        ChcOp::BvXor => Some(a ^ b),
                                        _ => None, // #6091: defensive
                                    };
                                    if let Some(r) = result {
                                        return Some(ChcExpr::BitVec(r, *wa));
                                    }
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            ChcOp::BvUDiv | ChcOp::BvURem if simplified_args.len() == 2 => {
                                if let (ChcExpr::BitVec(a, wa), ChcExpr::BitVec(b, wb)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    if wa == wb {
                                        let mask = if *wa >= 128 {
                                            u128::MAX
                                        } else {
                                            (1u128 << wa) - 1
                                        };
                                        let dividend = a & mask;
                                        let divisor = b & mask;
                                        let result = match op {
                                            // SMT-LIB: bvudiv by 0 returns all-ones.
                                            ChcOp::BvUDiv => Some(if divisor == 0 {
                                                mask
                                            } else {
                                                dividend / divisor
                                            }),
                                            // SMT-LIB: bvurem by 0 returns the dividend.
                                            ChcOp::BvURem => Some(if divisor == 0 {
                                                dividend
                                            } else {
                                                dividend % divisor
                                            }),
                                            _ => None, // #6091: defensive
                                        };
                                        if let Some(r) = result {
                                            return Some(ChcExpr::BitVec(r & mask, *wa));
                                        }
                                    }
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            // BV comparison constant folding
                            ChcOp::BvULt
                            | ChcOp::BvULe
                            | ChcOp::BvUGt
                            | ChcOp::BvUGe
                            | ChcOp::BvSLt
                            | ChcOp::BvSLe
                            | ChcOp::BvSGt
                            | ChcOp::BvSGe
                                if simplified_args.len() == 2 =>
                            {
                                if let (ChcExpr::BitVec(a, wa), ChcExpr::BitVec(b, _)) =
                                    (simplified_args[0].as_ref(), simplified_args[1].as_ref())
                                {
                                    let result = match op {
                                        ChcOp::BvULt => a < b,
                                        ChcOp::BvULe => a <= b,
                                        ChcOp::BvUGt => a > b,
                                        ChcOp::BvUGe => a >= b,
                                        ChcOp::BvSLt => {
                                            bv_signed_cmp(*a, *b, *wa) == std::cmp::Ordering::Less
                                        }
                                        ChcOp::BvSLe => {
                                            bv_signed_cmp(*a, *b, *wa)
                                                != std::cmp::Ordering::Greater
                                        }
                                        ChcOp::BvSGt => {
                                            bv_signed_cmp(*a, *b, *wa)
                                                == std::cmp::Ordering::Greater
                                        }
                                        ChcOp::BvSGe => {
                                            bv_signed_cmp(*a, *b, *wa) != std::cmp::Ordering::Less
                                        }
                                        _ => unreachable!(),
                                    };
                                    return Some(ChcExpr::Bool(result));
                                }
                                ChcExpr::Op(op.clone(), simplified_args)
                            }
                            _ => ChcExpr::Op(op.clone(), simplified_args),
                        }
                    }
                    _ => expr.map_children_with(|child| {
                        simplify_inner(child, budget, depth + 1).unwrap_or_else(|| child.clone())
                    }),
                })
            })
        }

        simplify_inner(self, &budget, 0).unwrap_or_else(|| self.clone())
    }
}

/// Compare two BV values as signed (two's complement) for constant folding.
fn bv_signed_cmp(a: u128, b: u128, width: u32) -> std::cmp::Ordering {
    if width == 0 || width > 128 {
        return a.cmp(&b);
    }
    if width == 128 {
        return (a as i128).cmp(&(b as i128));
    }
    let sign_bit = 1u128 << (width - 1);
    let a_neg = a & sign_bit != 0;
    let b_neg = b & sign_bit != 0;
    match (a_neg, b_neg) {
        (true, false) => std::cmp::Ordering::Less, // negative < positive
        (false, true) => std::cmp::Ordering::Greater, // positive > negative
        _ => a.cmp(&b),                            // same sign: unsigned comparison is correct
    }
}
