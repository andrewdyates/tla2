// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Expression simplification for BTOR2-to-CHC translation.
//
// Applied at the memoization point in the translator: each BTOR2 node
// is simplified exactly once before caching. This reduces the size of
// the CHC problem before it reaches the z4-chc solver.
//
// Simplifications performed:
// - Constant folding for BV arithmetic and bitwise ops
// - Identity elimination (x + 0 → x, x & all_ones → x)
// - Annihilation (x & 0 → 0)
// - Double negation (~~x → x)
// - ITE simplification (ite(true, a, b) → a; ite(c, x, x) → x)
// - Comparison simplification (x == x → true)
// - Boolean simplification

use std::sync::Arc;

use z4_chc::{ChcExpr, ChcOp};

/// Simplify a CHC expression bottom-up.
///
/// Recursively simplifies children first, then applies local rewrites.
pub(crate) fn simplify_expr(expr: &ChcExpr) -> ChcExpr {
    match expr {
        ChcExpr::Op(op, args) => {
            // Recursively simplify children.
            let simplified_args: Vec<Arc<ChcExpr>> =
                args.iter().map(|a| Arc::new(simplify_expr(a))).collect();
            // Try to simplify this node.
            simplify_op(op, &simplified_args)
        }
        // Leaves (Var, Bool, BitVec, Int) are already simple.
        other => other.clone(),
    }
}

/// Extract a BV constant value and width from a ChcExpr.
fn as_bv_const(expr: &ChcExpr) -> Option<(u128, u32)> {
    match expr {
        ChcExpr::BitVec(v, w) => Some((*v, *w)),
        _ => None,
    }
}

/// Create a BV constant expression.
fn make_bv(value: u128, width: u32) -> ChcExpr {
    let mask = bv_mask(width);
    ChcExpr::BitVec(value & mask, width)
}

/// Compute the mask for a bitvector of the given width.
fn bv_mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

/// Check if an expression is the zero BV constant.
fn is_bv_zero(expr: &ChcExpr) -> bool {
    matches!(expr, ChcExpr::BitVec(0, _))
}

/// Check if an expression is the one BV constant.
fn is_bv_one(expr: &ChcExpr) -> bool {
    matches!(expr, ChcExpr::BitVec(1, _))
}

/// Check if an expression is all-ones for its width.
fn is_bv_all_ones(expr: &ChcExpr) -> bool {
    if let ChcExpr::BitVec(v, w) = expr {
        *v == bv_mask(*w)
    } else {
        false
    }
}

/// Wrap args into a new Op expression (default, no simplification).
fn make_op(op: &ChcOp, args: &[Arc<ChcExpr>]) -> ChcExpr {
    ChcExpr::Op(op.clone(), args.to_vec())
}

/// Try to simplify an operation given its already-simplified arguments.
fn simplify_op(op: &ChcOp, args: &[Arc<ChcExpr>]) -> ChcExpr {
    match op {
        // -------------------------------------------------------------------
        // BV arithmetic: constant folding + identity
        // -------------------------------------------------------------------
        ChcOp::BvAdd => {
            if args.len() == 2 {
                if let (Some((a, wa)), Some((b, wb))) =
                    (as_bv_const(&args[0]), as_bv_const(&args[1]))
                {
                    if wa == wb {
                        return make_bv(a.wrapping_add(b), wa);
                    }
                }
                if is_bv_zero(&args[0]) {
                    return (*args[1]).clone();
                }
                if is_bv_zero(&args[1]) {
                    return (*args[0]).clone();
                }
            }
            make_op(op, args)
        }
        ChcOp::BvSub => {
            if args.len() == 2 {
                if let (Some((a, wa)), Some((b, wb))) =
                    (as_bv_const(&args[0]), as_bv_const(&args[1]))
                {
                    if wa == wb {
                        return make_bv(a.wrapping_sub(b), wa);
                    }
                }
                if is_bv_zero(&args[1]) {
                    return (*args[0]).clone();
                }
            }
            make_op(op, args)
        }
        ChcOp::BvMul => {
            if args.len() == 2 {
                if let (Some((a, wa)), Some((b, wb))) =
                    (as_bv_const(&args[0]), as_bv_const(&args[1]))
                {
                    if wa == wb {
                        return make_bv(a.wrapping_mul(b), wa);
                    }
                }
                if is_bv_zero(&args[0]) || is_bv_zero(&args[1]) {
                    if let Some((_, w)) = as_bv_const(&args[0]).or(as_bv_const(&args[1])) {
                        return make_bv(0, w);
                    }
                }
                if is_bv_one(&args[0]) {
                    return (*args[1]).clone();
                }
                if is_bv_one(&args[1]) {
                    return (*args[0]).clone();
                }
            }
            make_op(op, args)
        }

        // -------------------------------------------------------------------
        // Bitwise operations
        // -------------------------------------------------------------------
        ChcOp::BvAnd => {
            if args.len() == 2 {
                if let (Some((a, wa)), Some((b, wb))) =
                    (as_bv_const(&args[0]), as_bv_const(&args[1]))
                {
                    if wa == wb {
                        return make_bv(a & b, wa);
                    }
                }
                // x & 0 = 0
                if is_bv_zero(&args[0]) {
                    return (*args[0]).clone();
                }
                if is_bv_zero(&args[1]) {
                    return (*args[1]).clone();
                }
                // x & all_ones = x
                if is_bv_all_ones(&args[0]) {
                    return (*args[1]).clone();
                }
                if is_bv_all_ones(&args[1]) {
                    return (*args[0]).clone();
                }
            }
            make_op(op, args)
        }
        ChcOp::BvOr => {
            if args.len() == 2 {
                if let (Some((a, wa)), Some((b, wb))) =
                    (as_bv_const(&args[0]), as_bv_const(&args[1]))
                {
                    if wa == wb {
                        return make_bv(a | b, wa);
                    }
                }
                if is_bv_zero(&args[0]) {
                    return (*args[1]).clone();
                }
                if is_bv_zero(&args[1]) {
                    return (*args[0]).clone();
                }
                if is_bv_all_ones(&args[0]) {
                    return (*args[0]).clone();
                }
                if is_bv_all_ones(&args[1]) {
                    return (*args[1]).clone();
                }
            }
            make_op(op, args)
        }
        ChcOp::BvXor => {
            if args.len() == 2 {
                if let (Some((a, wa)), Some((b, wb))) =
                    (as_bv_const(&args[0]), as_bv_const(&args[1]))
                {
                    if wa == wb {
                        return make_bv(a ^ b, wa);
                    }
                }
                if is_bv_zero(&args[0]) {
                    return (*args[1]).clone();
                }
                if is_bv_zero(&args[1]) {
                    return (*args[0]).clone();
                }
                // x ^ x = 0
                if args[0] == args[1] {
                    if let Some((_, w)) = as_bv_const(&args[0]) {
                        return make_bv(0, w);
                    }
                }
            }
            make_op(op, args)
        }
        ChcOp::BvNot => {
            if args.len() == 1 {
                if let Some((v, w)) = as_bv_const(&args[0]) {
                    return make_bv(!v, w);
                }
                // Double negation: ~~x = x
                if let ChcExpr::Op(ChcOp::BvNot, inner) = args[0].as_ref() {
                    if inner.len() == 1 {
                        return (*inner[0]).clone();
                    }
                }
            }
            make_op(op, args)
        }
        ChcOp::BvNeg => {
            if args.len() == 1 {
                if let Some((v, w)) = as_bv_const(&args[0]) {
                    return make_bv((!v).wrapping_add(1), w);
                }
            }
            make_op(op, args)
        }

        // -------------------------------------------------------------------
        // Comparisons
        // -------------------------------------------------------------------
        ChcOp::Eq => {
            if args.len() == 2 {
                // const == const
                if let (Some((a, wa)), Some((b, wb))) =
                    (as_bv_const(&args[0]), as_bv_const(&args[1]))
                {
                    if wa == wb {
                        return ChcExpr::Bool(a == b);
                    }
                }
                // x == x → true
                if args[0] == args[1] {
                    return ChcExpr::Bool(true);
                }
            }
            make_op(op, args)
        }
        ChcOp::BvULt => {
            if args.len() == 2 {
                if let (Some((a, wa)), Some((b, wb))) =
                    (as_bv_const(&args[0]), as_bv_const(&args[1]))
                {
                    if wa == wb {
                        return ChcExpr::Bool(a < b);
                    }
                }
                // x < x → false
                if args[0] == args[1] {
                    return ChcExpr::Bool(false);
                }
            }
            make_op(op, args)
        }
        ChcOp::BvULe => {
            if args.len() == 2 {
                if let (Some((a, wa)), Some((b, wb))) =
                    (as_bv_const(&args[0]), as_bv_const(&args[1]))
                {
                    if wa == wb {
                        return ChcExpr::Bool(a <= b);
                    }
                }
                // x <= x → true
                if args[0] == args[1] {
                    return ChcExpr::Bool(true);
                }
            }
            make_op(op, args)
        }

        // -------------------------------------------------------------------
        // Shifts
        // -------------------------------------------------------------------
        ChcOp::BvShl | ChcOp::BvLShr => {
            if args.len() == 2 {
                if is_bv_zero(&args[0]) {
                    return (*args[0]).clone();
                }
                if is_bv_zero(&args[1]) {
                    return (*args[0]).clone();
                }
                if let (Some((a, wa)), Some((b, wb))) =
                    (as_bv_const(&args[0]), as_bv_const(&args[1]))
                {
                    if wa == wb {
                        let shift = b as u32;
                        if shift >= wa {
                            return make_bv(0, wa);
                        }
                        let result = if matches!(op, ChcOp::BvShl) {
                            a << shift
                        } else {
                            a >> shift
                        };
                        return make_bv(result, wa);
                    }
                }
            }
            make_op(op, args)
        }

        // -------------------------------------------------------------------
        // ITE (if-then-else)
        // -------------------------------------------------------------------
        ChcOp::Ite => {
            if args.len() == 3 {
                // ite(true, a, b) → a
                if *args[0] == ChcExpr::Bool(true) {
                    return (*args[1]).clone();
                }
                // ite(false, a, b) → b
                if *args[0] == ChcExpr::Bool(false) {
                    return (*args[2]).clone();
                }
                // ite(c, x, x) → x
                if args[1] == args[2] {
                    return (*args[1]).clone();
                }
            }
            make_op(op, args)
        }

        // -------------------------------------------------------------------
        // Extract
        // -------------------------------------------------------------------
        ChcOp::BvExtract(hi, lo) => {
            if args.len() == 1 {
                if let Some((v, _w)) = as_bv_const(&args[0]) {
                    let width = hi - lo + 1;
                    let mask = bv_mask(width);
                    return make_bv((v >> lo) & mask, width);
                }
            }
            make_op(op, args)
        }

        // -------------------------------------------------------------------
        // Extend
        // -------------------------------------------------------------------
        ChcOp::BvZeroExtend(extra) => {
            if args.len() == 1 {
                if *extra == 0 {
                    return (*args[0]).clone();
                }
            }
            make_op(op, args)
        }
        ChcOp::BvSignExtend(extra) => {
            if args.len() == 1 {
                if *extra == 0 {
                    return (*args[0]).clone();
                }
            }
            make_op(op, args)
        }

        // -------------------------------------------------------------------
        // Concat
        // -------------------------------------------------------------------
        ChcOp::BvConcat => {
            if args.len() == 2 {
                if let (Some((a, wa)), Some((b, wb))) =
                    (as_bv_const(&args[0]), as_bv_const(&args[1]))
                {
                    let result = ((a & bv_mask(wa)) << wb) | (b & bv_mask(wb));
                    return make_bv(result, wa + wb);
                }
            }
            make_op(op, args)
        }

        // -------------------------------------------------------------------
        // Boolean operations
        // -------------------------------------------------------------------
        ChcOp::And => {
            if args.len() == 2 {
                if *args[0] == ChcExpr::Bool(false) || *args[1] == ChcExpr::Bool(false) {
                    return ChcExpr::Bool(false);
                }
                if *args[0] == ChcExpr::Bool(true) {
                    return (*args[1]).clone();
                }
                if *args[1] == ChcExpr::Bool(true) {
                    return (*args[0]).clone();
                }
            }
            make_op(op, args)
        }
        ChcOp::Or => {
            if args.len() == 2 {
                if *args[0] == ChcExpr::Bool(true) || *args[1] == ChcExpr::Bool(true) {
                    return ChcExpr::Bool(true);
                }
                if *args[0] == ChcExpr::Bool(false) {
                    return (*args[1]).clone();
                }
                if *args[1] == ChcExpr::Bool(false) {
                    return (*args[0]).clone();
                }
            }
            make_op(op, args)
        }
        ChcOp::Not => {
            if args.len() == 1 {
                if *args[0] == ChcExpr::Bool(true) {
                    return ChcExpr::Bool(false);
                }
                if *args[0] == ChcExpr::Bool(false) {
                    return ChcExpr::Bool(true);
                }
                // Double negation
                if let ChcExpr::Op(ChcOp::Not, inner) = args[0].as_ref() {
                    if inner.len() == 1 {
                        return (*inner[0]).clone();
                    }
                }
            }
            make_op(op, args)
        }
        ChcOp::Implies => {
            if args.len() == 2 {
                if *args[0] == ChcExpr::Bool(false) || *args[1] == ChcExpr::Bool(true) {
                    return ChcExpr::Bool(true);
                }
                if *args[0] == ChcExpr::Bool(true) {
                    return (*args[1]).clone();
                }
            }
            make_op(op, args)
        }

        // Default: no simplification.
        _ => make_op(op, args),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bv_var(name: &str) -> ChcExpr {
        ChcExpr::Var(z4_chc::ChcVar {
            name: name.to_string(),
            sort: z4_chc::ChcSort::BitVec(8),
        })
    }

    #[test]
    fn test_constant_fold_add() {
        let expr = ChcExpr::Op(
            ChcOp::BvAdd,
            vec![
                Arc::new(ChcExpr::BitVec(3, 8)),
                Arc::new(ChcExpr::BitVec(5, 8)),
            ],
        );
        assert_eq!(simplify_expr(&expr), ChcExpr::BitVec(8, 8));
    }

    #[test]
    fn test_identity_add_zero() {
        let x = bv_var("x");
        let expr = ChcExpr::Op(
            ChcOp::BvAdd,
            vec![Arc::new(x.clone()), Arc::new(ChcExpr::BitVec(0, 8))],
        );
        assert_eq!(simplify_expr(&expr), x);
    }

    #[test]
    fn test_and_zero_annihilation() {
        let x = bv_var("x");
        let expr = ChcExpr::Op(
            ChcOp::BvAnd,
            vec![Arc::new(x), Arc::new(ChcExpr::BitVec(0, 8))],
        );
        assert_eq!(simplify_expr(&expr), ChcExpr::BitVec(0, 8));
    }

    #[test]
    fn test_or_zero_identity() {
        let x = bv_var("x");
        let expr = ChcExpr::Op(
            ChcOp::BvOr,
            vec![Arc::new(ChcExpr::BitVec(0, 8)), Arc::new(x.clone())],
        );
        assert_eq!(simplify_expr(&expr), x);
    }

    #[test]
    fn test_double_negation_bvnot() {
        let x = bv_var("x");
        let expr = ChcExpr::Op(
            ChcOp::BvNot,
            vec![Arc::new(ChcExpr::Op(
                ChcOp::BvNot,
                vec![Arc::new(x.clone())],
            ))],
        );
        assert_eq!(simplify_expr(&expr), x);
    }

    #[test]
    fn test_eq_same_operands() {
        let x = bv_var("x");
        let expr = ChcExpr::Op(ChcOp::Eq, vec![Arc::new(x.clone()), Arc::new(x)]);
        assert_eq!(simplify_expr(&expr), ChcExpr::Bool(true));
    }

    #[test]
    fn test_ite_true_branch() {
        let a = bv_var("a");
        let b = bv_var("b");
        let expr = ChcExpr::Op(
            ChcOp::Ite,
            vec![
                Arc::new(ChcExpr::Bool(true)),
                Arc::new(a.clone()),
                Arc::new(b),
            ],
        );
        assert_eq!(simplify_expr(&expr), a);
    }

    #[test]
    fn test_ite_false_branch() {
        let a = bv_var("a");
        let b = bv_var("b");
        let expr = ChcExpr::Op(
            ChcOp::Ite,
            vec![
                Arc::new(ChcExpr::Bool(false)),
                Arc::new(a),
                Arc::new(b.clone()),
            ],
        );
        assert_eq!(simplify_expr(&expr), b);
    }

    #[test]
    fn test_ite_same_branches() {
        let c = bv_var("c");
        let x = bv_var("x");
        let expr = ChcExpr::Op(
            ChcOp::Ite,
            vec![Arc::new(c), Arc::new(x.clone()), Arc::new(x.clone())],
        );
        assert_eq!(simplify_expr(&expr), x);
    }

    #[test]
    fn test_extract_constant() {
        // extract[3:0](0xFF) = 0x0F
        let expr = ChcExpr::Op(
            ChcOp::BvExtract(3, 0),
            vec![Arc::new(ChcExpr::BitVec(0xFF, 8))],
        );
        assert_eq!(simplify_expr(&expr), ChcExpr::BitVec(0x0F, 4));
    }

    #[test]
    fn test_boolean_and_simplification() {
        let x = bv_var("x");
        let expr = ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(ChcExpr::Bool(true)),
                Arc::new(ChcExpr::Bool(false)),
            ],
        );
        assert_eq!(simplify_expr(&expr), ChcExpr::Bool(false));

        let expr2 = ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(ChcExpr::Bool(true)),
                Arc::new(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![Arc::new(x.clone()), Arc::new(x)],
                )),
            ],
        );
        // true AND (x == x) → (x == x) → true
        assert_eq!(simplify_expr(&expr2), ChcExpr::Bool(true));
    }

    #[test]
    fn test_nested_simplification() {
        // (x + 0) + (3 + 5) → x + 8
        let x = bv_var("x");
        let expr = ChcExpr::Op(
            ChcOp::BvAdd,
            vec![
                Arc::new(ChcExpr::Op(
                    ChcOp::BvAdd,
                    vec![Arc::new(x.clone()), Arc::new(ChcExpr::BitVec(0, 8))],
                )),
                Arc::new(ChcExpr::Op(
                    ChcOp::BvAdd,
                    vec![
                        Arc::new(ChcExpr::BitVec(3, 8)),
                        Arc::new(ChcExpr::BitVec(5, 8)),
                    ],
                )),
            ],
        );
        let result = simplify_expr(&expr);
        match &result {
            ChcExpr::Op(ChcOp::BvAdd, args) if args.len() == 2 => {
                assert_eq!(*args[0], x);
                assert_eq!(*args[1], ChcExpr::BitVec(8, 8));
            }
            _ => panic!("expected BvAdd(x, 8), got: {:?}", result),
        }
    }
}
