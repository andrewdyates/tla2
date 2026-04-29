// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TIR-level constant propagation and folding pass.
//!
//! Walks the TIR expression tree and rewrites subtrees where the result
//! can be computed at compile time:
//!
//! - **Constant arithmetic**: `3 + 4` -> `7`, `2 * 5` -> `10`
//! - **Constant boolean**: `TRUE /\ FALSE` -> `FALSE`
//! - **Constant comparisons**: `3 < 5` -> `TRUE`
//! - **LET propagation**: bindings with constant bodies are substituted
//! - **IF simplification**: `IF TRUE THEN a ELSE b` -> `a`
//!
//! Both the JIT compiler and code generator can consume the folded tree
//! without independently re-deriving constant expressions.
//!
//! Part of #3930.

use crate::nodes::{
    TirArithOp, TirBoolOp, TirBoundVar, TirCaseArm, TirCmpOp, TirExceptPathElement, TirExceptSpec,
    TirExpr, TirLetDef, TirModuleRefSegment, TirOperatorRef,
};
use crate::types::TirType;
use rustc_hash::FxHashMap;
use tla_core::{NameId, Spanned};
use tla_value::Value;

/// Statistics collected during a constant propagation pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ConstPropStats {
    /// Number of arithmetic operations folded to constants.
    pub arith_folds: usize,
    /// Number of boolean operations folded to constants.
    pub bool_folds: usize,
    /// Number of comparison operations folded to constants.
    pub cmp_folds: usize,
    /// Number of IF/THEN/ELSE branches simplified.
    pub if_simplifications: usize,
    /// Number of LET bindings propagated.
    pub let_propagations: usize,
}

/// Run constant propagation and folding on a single TIR expression tree.
///
/// Returns the optimized expression and statistics about what was folded.
/// The pass is purely local and does not require cross-operator context.
#[must_use]
pub fn const_prop_expr(expr: Spanned<TirExpr>) -> (Spanned<TirExpr>, ConstPropStats) {
    let mut stats = ConstPropStats::default();
    let mut env: FxHashMap<NameId, Spanned<TirExpr>> = FxHashMap::default();
    let result = fold_expr(expr, &mut env, &mut stats);
    (result, stats)
}

/// Attempt to extract a constant i64 from a TIR expression.
fn as_const_int(expr: &TirExpr) -> Option<i64> {
    match expr {
        TirExpr::Const {
            value,
            ty: TirType::Int,
            ..
        } => value.as_i64(),
        _ => None,
    }
}

/// Attempt to extract a constant bool from a TIR expression.
fn as_const_bool(expr: &TirExpr) -> Option<bool> {
    match expr {
        TirExpr::Const {
            value,
            ty: TirType::Bool,
            ..
        } => value.as_bool(),
        _ => None,
    }
}

/// Check whether a TIR expression is a constant (Int, Bool, or Str literal).
fn is_const(expr: &TirExpr) -> bool {
    matches!(expr, TirExpr::Const { .. })
}

/// Create a constant integer TIR expression node.
fn make_int(n: i64) -> TirExpr {
    TirExpr::Const {
        value: Value::int(n),
        ty: TirType::Int,
    }
}

/// Create a constant boolean TIR expression node.
fn make_bool(b: bool) -> TirExpr {
    TirExpr::Const {
        value: Value::bool(b),
        ty: TirType::Bool,
    }
}

/// Evaluate a constant arithmetic binary operation.
fn eval_arith(op: TirArithOp, lhs: i64, rhs: i64) -> Option<i64> {
    match op {
        TirArithOp::Add => lhs.checked_add(rhs),
        TirArithOp::Sub => lhs.checked_sub(rhs),
        TirArithOp::Mul => lhs.checked_mul(rhs),
        TirArithOp::Div => {
            // TLA+ division: real division, but we only fold for exact results
            if rhs == 0 {
                None
            } else if lhs % rhs == 0 {
                Some(lhs / rhs)
            } else {
                None
            }
        }
        TirArithOp::IntDiv => {
            // TLA+ integer division: floor division
            if rhs == 0 {
                None
            } else {
                // TLA+ \div is floor division (Euclidean)
                Some(lhs.div_euclid(rhs))
            }
        }
        TirArithOp::Mod => {
            if rhs == 0 {
                None
            } else {
                // TLA+ % is Euclidean modulo (always non-negative)
                Some(lhs.rem_euclid(rhs))
            }
        }
        TirArithOp::Pow => {
            if rhs < 0 {
                None
            } else if rhs == 0 {
                Some(1)
            } else {
                let exp = rhs as u32;
                lhs.checked_pow(exp)
            }
        }
    }
}

/// Evaluate a constant boolean binary operation.
fn eval_bool(op: TirBoolOp, lhs: bool, rhs: bool) -> bool {
    match op {
        TirBoolOp::And => lhs && rhs,
        TirBoolOp::Or => lhs || rhs,
        TirBoolOp::Implies => !lhs || rhs,
        TirBoolOp::Equiv => lhs == rhs,
    }
}

/// Evaluate a constant comparison operation (integer operands).
fn eval_cmp_int(op: TirCmpOp, lhs: i64, rhs: i64) -> bool {
    match op {
        TirCmpOp::Eq => lhs == rhs,
        TirCmpOp::Neq => lhs != rhs,
        TirCmpOp::Lt => lhs < rhs,
        TirCmpOp::Leq => lhs <= rhs,
        TirCmpOp::Gt => lhs > rhs,
        TirCmpOp::Geq => lhs >= rhs,
    }
}

/// Evaluate a constant comparison on boolean operands.
fn eval_cmp_bool(op: TirCmpOp, lhs: bool, rhs: bool) -> Option<bool> {
    match op {
        TirCmpOp::Eq => Some(lhs == rhs),
        TirCmpOp::Neq => Some(lhs != rhs),
        // Ordering comparisons on booleans are not standard in TLA+
        _ => None,
    }
}

/// Recursively fold an expression, substituting constant LET bindings
/// from `env` and simplifying where possible.
fn fold_expr(
    expr: Spanned<TirExpr>,
    env: &mut FxHashMap<NameId, Spanned<TirExpr>>,
    stats: &mut ConstPropStats,
) -> Spanned<TirExpr> {
    let span = expr.span;
    let node = match expr.node {
        // --- Constant LET propagation: substitute Name refs from env ---
        TirExpr::Name(ref name_ref) => {
            if let Some(replacement) = env.get(&name_ref.name_id) {
                stats.let_propagations += 1;
                return replacement.clone();
            }
            return expr;
        }

        // --- Arithmetic binary ops ---
        TirExpr::ArithBinOp { left, op, right } => {
            let left = fold_expr(*left, env, stats);
            let right = fold_expr(*right, env, stats);
            if let (Some(l), Some(r)) = (as_const_int(&left.node), as_const_int(&right.node)) {
                if let Some(result) = eval_arith(op, l, r) {
                    stats.arith_folds += 1;
                    make_int(result)
                } else {
                    TirExpr::ArithBinOp {
                        left: Box::new(left),
                        op,
                        right: Box::new(right),
                    }
                }
            } else {
                TirExpr::ArithBinOp {
                    left: Box::new(left),
                    op,
                    right: Box::new(right),
                }
            }
        }

        // --- Arithmetic negation ---
        TirExpr::ArithNeg(inner) => {
            let inner = fold_expr(*inner, env, stats);
            if let Some(n) = as_const_int(&inner.node) {
                if let Some(result) = n.checked_neg() {
                    stats.arith_folds += 1;
                    make_int(result)
                } else {
                    TirExpr::ArithNeg(Box::new(inner))
                }
            } else {
                TirExpr::ArithNeg(Box::new(inner))
            }
        }

        // --- Boolean binary ops ---
        TirExpr::BoolBinOp { left, op, right } => {
            let left = fold_expr(*left, env, stats);
            let right = fold_expr(*right, env, stats);
            if let (Some(l), Some(r)) = (as_const_bool(&left.node), as_const_bool(&right.node)) {
                stats.bool_folds += 1;
                make_bool(eval_bool(op, l, r))
            } else {
                // Short-circuit simplifications with one constant operand
                match op {
                    TirBoolOp::And => {
                        if as_const_bool(&left.node) == Some(true) {
                            stats.bool_folds += 1;
                            return right;
                        }
                        if as_const_bool(&left.node) == Some(false) {
                            stats.bool_folds += 1;
                            return Spanned {
                                node: make_bool(false),
                                span,
                            };
                        }
                        if as_const_bool(&right.node) == Some(true) {
                            stats.bool_folds += 1;
                            return left;
                        }
                        if as_const_bool(&right.node) == Some(false) {
                            stats.bool_folds += 1;
                            return Spanned {
                                node: make_bool(false),
                                span,
                            };
                        }
                        TirExpr::BoolBinOp {
                            left: Box::new(left),
                            op,
                            right: Box::new(right),
                        }
                    }
                    TirBoolOp::Or => {
                        if as_const_bool(&left.node) == Some(true) {
                            stats.bool_folds += 1;
                            return Spanned {
                                node: make_bool(true),
                                span,
                            };
                        }
                        if as_const_bool(&left.node) == Some(false) {
                            stats.bool_folds += 1;
                            return right;
                        }
                        if as_const_bool(&right.node) == Some(true) {
                            stats.bool_folds += 1;
                            return Spanned {
                                node: make_bool(true),
                                span,
                            };
                        }
                        if as_const_bool(&right.node) == Some(false) {
                            stats.bool_folds += 1;
                            return left;
                        }
                        TirExpr::BoolBinOp {
                            left: Box::new(left),
                            op,
                            right: Box::new(right),
                        }
                    }
                    TirBoolOp::Implies => {
                        // FALSE => x is TRUE
                        if as_const_bool(&left.node) == Some(false) {
                            stats.bool_folds += 1;
                            return Spanned {
                                node: make_bool(true),
                                span,
                            };
                        }
                        // TRUE => x is x
                        if as_const_bool(&left.node) == Some(true) {
                            stats.bool_folds += 1;
                            return right;
                        }
                        TirExpr::BoolBinOp {
                            left: Box::new(left),
                            op,
                            right: Box::new(right),
                        }
                    }
                    TirBoolOp::Equiv => TirExpr::BoolBinOp {
                        left: Box::new(left),
                        op,
                        right: Box::new(right),
                    },
                }
            }
        }

        // --- Boolean negation ---
        TirExpr::BoolNot(inner) => {
            let inner = fold_expr(*inner, env, stats);
            if let Some(b) = as_const_bool(&inner.node) {
                stats.bool_folds += 1;
                make_bool(!b)
            } else {
                TirExpr::BoolNot(Box::new(inner))
            }
        }

        // --- Comparisons ---
        TirExpr::Cmp { left, op, right } => {
            let left = fold_expr(*left, env, stats);
            let right = fold_expr(*right, env, stats);
            // Try integer comparison
            if let (Some(l), Some(r)) = (as_const_int(&left.node), as_const_int(&right.node)) {
                stats.cmp_folds += 1;
                make_bool(eval_cmp_int(op, l, r))
            }
            // Try boolean comparison (only Eq/Neq)
            else if let (Some(l), Some(r)) =
                (as_const_bool(&left.node), as_const_bool(&right.node))
            {
                if let Some(result) = eval_cmp_bool(op, l, r) {
                    stats.cmp_folds += 1;
                    make_bool(result)
                } else {
                    TirExpr::Cmp {
                        left: Box::new(left),
                        op,
                        right: Box::new(right),
                    }
                }
            } else {
                TirExpr::Cmp {
                    left: Box::new(left),
                    op,
                    right: Box::new(right),
                }
            }
        }

        // --- IF/THEN/ELSE simplification ---
        TirExpr::If { cond, then_, else_ } => {
            let cond = fold_expr(*cond, env, stats);
            let then_ = fold_expr(*then_, env, stats);
            let else_ = fold_expr(*else_, env, stats);
            if let Some(b) = as_const_bool(&cond.node) {
                stats.if_simplifications += 1;
                if b {
                    return then_;
                } else {
                    return else_;
                }
            }
            TirExpr::If {
                cond: Box::new(cond),
                then_: Box::new(then_),
                else_: Box::new(else_),
            }
        }

        // --- LET: propagate constant defs into body ---
        TirExpr::Let { defs, body } => {
            let mut folded_defs: Vec<TirLetDef> = Vec::with_capacity(defs.len());
            let mut propagated_names: Vec<NameId> = Vec::new();

            for def in defs {
                let folded_body = fold_expr(def.body, env, stats);
                // Only propagate zero-arity constant defs
                if def.params.is_empty() && is_const(&folded_body.node) {
                    env.insert(def.name_id, folded_body.clone());
                    propagated_names.push(def.name_id);
                }
                folded_defs.push(TirLetDef {
                    name: def.name,
                    name_id: def.name_id,
                    params: def.params,
                    body: folded_body,
                });
            }

            let folded_body = fold_expr(*body, env, stats);

            // Clean up env entries we added
            for name_id in &propagated_names {
                env.remove(name_id);
            }

            // Remove defs whose bodies were propagated everywhere
            let remaining_defs: Vec<TirLetDef> = folded_defs
                .into_iter()
                .filter(|def| {
                    // Keep defs that have params (not propagated) or are not constant
                    !def.params.is_empty() || !propagated_names.contains(&def.name_id)
                })
                .collect();

            if remaining_defs.is_empty() {
                return folded_body;
            }

            TirExpr::Let {
                defs: remaining_defs,
                body: Box::new(folded_body),
            }
        }

        // --- CASE: fold guards and bodies ---
        TirExpr::Case { arms, other } => {
            let folded_arms: Vec<TirCaseArm> = arms
                .into_iter()
                .map(|arm| TirCaseArm {
                    guard: fold_expr(arm.guard, env, stats),
                    body: fold_expr(arm.body, env, stats),
                })
                .collect();
            let folded_other = other.map(|o| Box::new(fold_expr(*o, env, stats)));
            TirExpr::Case {
                arms: folded_arms,
                other: folded_other,
            }
        }

        // --- Label: transparent, just fold body ---
        TirExpr::Label { name, body } => {
            let folded = fold_expr(*body, env, stats);
            TirExpr::Label {
                name,
                body: Box::new(folded),
            }
        }

        // --- Binary children: recurse into both sides ---
        TirExpr::In { elem, set } => TirExpr::In {
            elem: Box::new(fold_expr(*elem, env, stats)),
            set: Box::new(fold_expr(*set, env, stats)),
        },
        TirExpr::Subseteq { left, right } => TirExpr::Subseteq {
            left: Box::new(fold_expr(*left, env, stats)),
            right: Box::new(fold_expr(*right, env, stats)),
        },
        TirExpr::SetBinOp { left, op, right } => TirExpr::SetBinOp {
            left: Box::new(fold_expr(*left, env, stats)),
            op,
            right: Box::new(fold_expr(*right, env, stats)),
        },
        TirExpr::FuncApply { func, arg } => TirExpr::FuncApply {
            func: Box::new(fold_expr(*func, env, stats)),
            arg: Box::new(fold_expr(*arg, env, stats)),
        },
        TirExpr::FuncSet { domain, range } => TirExpr::FuncSet {
            domain: Box::new(fold_expr(*domain, env, stats)),
            range: Box::new(fold_expr(*range, env, stats)),
        },
        TirExpr::Range { lo, hi } => TirExpr::Range {
            lo: Box::new(fold_expr(*lo, env, stats)),
            hi: Box::new(fold_expr(*hi, env, stats)),
        },
        TirExpr::KSubset { base, k } => TirExpr::KSubset {
            base: Box::new(fold_expr(*base, env, stats)),
            k: Box::new(fold_expr(*k, env, stats)),
        },
        TirExpr::LeadsTo { left, right } => TirExpr::LeadsTo {
            left: Box::new(fold_expr(*left, env, stats)),
            right: Box::new(fold_expr(*right, env, stats)),
        },

        // --- Unary children ---
        TirExpr::Unchanged(inner) => TirExpr::Unchanged(Box::new(fold_expr(*inner, env, stats))),
        TirExpr::Always(inner) => TirExpr::Always(Box::new(fold_expr(*inner, env, stats))),
        TirExpr::Eventually(inner) => TirExpr::Eventually(Box::new(fold_expr(*inner, env, stats))),
        TirExpr::Enabled(inner) => TirExpr::Enabled(Box::new(fold_expr(*inner, env, stats))),
        TirExpr::Powerset(inner) => TirExpr::Powerset(Box::new(fold_expr(*inner, env, stats))),
        TirExpr::BigUnion(inner) => TirExpr::BigUnion(Box::new(fold_expr(*inner, env, stats))),
        TirExpr::Domain(inner) => TirExpr::Domain(Box::new(fold_expr(*inner, env, stats))),
        TirExpr::Prime(inner) => TirExpr::Prime(Box::new(fold_expr(*inner, env, stats))),

        // --- Ternary ---
        TirExpr::ActionSubscript {
            kind,
            action,
            subscript,
        } => TirExpr::ActionSubscript {
            kind,
            action: Box::new(fold_expr(*action, env, stats)),
            subscript: Box::new(fold_expr(*subscript, env, stats)),
        },

        // --- Record access ---
        TirExpr::RecordAccess { record, field } => TirExpr::RecordAccess {
            record: Box::new(fold_expr(*record, env, stats)),
            field,
        },

        // --- Except ---
        TirExpr::Except { base, specs } => TirExpr::Except {
            base: Box::new(fold_expr(*base, env, stats)),
            specs: specs
                .into_iter()
                .map(|spec| fold_except_spec(spec, env, stats))
                .collect(),
        },

        // --- Quantifiers ---
        TirExpr::Forall { vars, body } => TirExpr::Forall {
            vars: fold_bound_vars(vars, env, stats),
            body: Box::new(fold_expr(*body, env, stats)),
        },
        TirExpr::Exists { vars, body } => TirExpr::Exists {
            vars: fold_bound_vars(vars, env, stats),
            body: Box::new(fold_expr(*body, env, stats)),
        },
        TirExpr::Choose { var, body } => TirExpr::Choose {
            var: fold_bound_var(var, env, stats),
            body: Box::new(fold_expr(*body, env, stats)),
        },

        // --- Sets ---
        TirExpr::SetEnum(elems) => TirExpr::SetEnum(
            elems
                .into_iter()
                .map(|e| fold_expr(e, env, stats))
                .collect(),
        ),
        TirExpr::SetFilter { var, body } => TirExpr::SetFilter {
            var: fold_bound_var(var, env, stats),
            body: Box::new(fold_expr(*body, env, stats)),
        },
        TirExpr::SetBuilder { body, vars } => TirExpr::SetBuilder {
            body: Box::new(fold_expr(*body, env, stats)),
            vars: fold_bound_vars(vars, env, stats),
        },

        // --- Functions ---
        TirExpr::FuncDef { vars, body } => TirExpr::FuncDef {
            vars: fold_bound_vars(vars, env, stats),
            body: Box::new(fold_expr(*body, env, stats)),
        },

        // --- Records/Tuples ---
        TirExpr::Record(fields) => TirExpr::Record(
            fields
                .into_iter()
                .map(|(f, e)| (f, fold_expr(e, env, stats)))
                .collect(),
        ),
        TirExpr::RecordSet(fields) => TirExpr::RecordSet(
            fields
                .into_iter()
                .map(|(f, e)| (f, fold_expr(e, env, stats)))
                .collect(),
        ),
        TirExpr::Tuple(elems) => TirExpr::Tuple(
            elems
                .into_iter()
                .map(|e| fold_expr(e, env, stats))
                .collect(),
        ),
        TirExpr::Times(elems) => TirExpr::Times(
            elems
                .into_iter()
                .map(|e| fold_expr(e, env, stats))
                .collect(),
        ),

        // --- Apply ---
        TirExpr::Apply { op, args } => TirExpr::Apply {
            op: Box::new(fold_expr(*op, env, stats)),
            args: args.into_iter().map(|a| fold_expr(a, env, stats)).collect(),
        },

        // --- Lambda ---
        TirExpr::Lambda {
            params,
            body,
            ast_body,
        } => TirExpr::Lambda {
            params,
            body: Box::new(fold_expr(*body, env, stats)),
            ast_body,
        },

        // --- Temporal ---
        TirExpr::WeakFair { vars, action } => TirExpr::WeakFair {
            vars: Box::new(fold_expr(*vars, env, stats)),
            action: Box::new(fold_expr(*action, env, stats)),
        },
        TirExpr::StrongFair { vars, action } => TirExpr::StrongFair {
            vars: Box::new(fold_expr(*vars, env, stats)),
            action: Box::new(fold_expr(*action, env, stats)),
        },

        // --- OperatorRef: fold argument subexpressions ---
        TirExpr::OperatorRef(op_ref) => TirExpr::OperatorRef(TirOperatorRef {
            path: op_ref
                .path
                .into_iter()
                .map(|seg| TirModuleRefSegment {
                    name: seg.name,
                    name_id: seg.name_id,
                    args: seg
                        .args
                        .into_iter()
                        .map(|a| fold_expr(a, env, stats))
                        .collect(),
                })
                .collect(),
            operator: op_ref.operator,
            operator_id: op_ref.operator_id,
            args: op_ref
                .args
                .into_iter()
                .map(|a| fold_expr(a, env, stats))
                .collect(),
        }),

        // --- Leaves: no children to fold ---
        TirExpr::Const { .. } | TirExpr::ExceptAt | TirExpr::OpRef(_) => {
            return expr;
        }
    };

    Spanned { node, span }
}

fn fold_bound_var(
    var: TirBoundVar,
    env: &mut FxHashMap<NameId, Spanned<TirExpr>>,
    stats: &mut ConstPropStats,
) -> TirBoundVar {
    TirBoundVar {
        name: var.name,
        name_id: var.name_id,
        domain: var.domain.map(|d| Box::new(fold_expr(*d, env, stats))),
        pattern: var.pattern,
    }
}

fn fold_bound_vars(
    vars: Vec<TirBoundVar>,
    env: &mut FxHashMap<NameId, Spanned<TirExpr>>,
    stats: &mut ConstPropStats,
) -> Vec<TirBoundVar> {
    vars.into_iter()
        .map(|v| fold_bound_var(v, env, stats))
        .collect()
}

fn fold_except_spec(
    spec: TirExceptSpec,
    env: &mut FxHashMap<NameId, Spanned<TirExpr>>,
    stats: &mut ConstPropStats,
) -> TirExceptSpec {
    TirExceptSpec {
        path: spec
            .path
            .into_iter()
            .map(|elem| match elem {
                TirExceptPathElement::Index(idx) => {
                    TirExceptPathElement::Index(Box::new(fold_expr(*idx, env, stats)))
                }
                TirExceptPathElement::Field(f) => TirExceptPathElement::Field(f),
            })
            .collect(),
        value: fold_expr(spec.value, env, stats),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nodes::*;
    use crate::types::TirType;
    use tla_core::intern_name;
    use tla_core::span::{FileId, Span};

    fn span() -> Span {
        Span::new(FileId(0), 0, 0)
    }

    fn spanned(expr: TirExpr) -> Spanned<TirExpr> {
        Spanned::new(expr, span())
    }

    fn int_const(n: i64) -> Spanned<TirExpr> {
        spanned(TirExpr::Const {
            value: Value::int(n),
            ty: TirType::Int,
        })
    }

    fn bool_const(b: bool) -> Spanned<TirExpr> {
        spanned(TirExpr::Const {
            value: Value::bool(b),
            ty: TirType::Bool,
        })
    }

    fn int_var(name: &str) -> Spanned<TirExpr> {
        spanned(TirExpr::Name(TirNameRef {
            name: name.to_string(),
            name_id: intern_name(name),
            kind: TirNameKind::StateVar { index: 0 },
            ty: TirType::Int,
        }))
    }

    fn bool_var(name: &str) -> Spanned<TirExpr> {
        spanned(TirExpr::Name(TirNameRef {
            name: name.to_string(),
            name_id: intern_name(name),
            kind: TirNameKind::StateVar { index: 1 },
            ty: TirType::Bool,
        }))
    }

    // =========================================================
    // Arithmetic folding
    // =========================================================

    #[test]
    fn test_fold_add() {
        // 3 + 4 -> 7
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_const(3)),
            op: TirArithOp::Add,
            right: Box::new(int_const(4)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(7));
        assert_eq!(stats.arith_folds, 1);
    }

    #[test]
    fn test_fold_sub() {
        // 10 - 3 -> 7
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_const(10)),
            op: TirArithOp::Sub,
            right: Box::new(int_const(3)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(7));
        assert_eq!(stats.arith_folds, 1);
    }

    #[test]
    fn test_fold_mul() {
        // 2 * 5 -> 10
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_const(2)),
            op: TirArithOp::Mul,
            right: Box::new(int_const(5)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(10));
        assert_eq!(stats.arith_folds, 1);
    }

    #[test]
    fn test_fold_int_div() {
        // 7 \div 2 -> 3 (Euclidean floor division)
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_const(7)),
            op: TirArithOp::IntDiv,
            right: Box::new(int_const(2)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(3));
        assert_eq!(stats.arith_folds, 1);
    }

    #[test]
    fn test_fold_mod() {
        // 7 % 3 -> 1
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_const(7)),
            op: TirArithOp::Mod,
            right: Box::new(int_const(3)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(1));
        assert_eq!(stats.arith_folds, 1);
    }

    #[test]
    fn test_fold_pow() {
        // 2 ^ 10 -> 1024
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_const(2)),
            op: TirArithOp::Pow,
            right: Box::new(int_const(10)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(1024));
        assert_eq!(stats.arith_folds, 1);
    }

    #[test]
    fn test_fold_div_exact() {
        // 10 / 5 -> 2 (exact division)
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_const(10)),
            op: TirArithOp::Div,
            right: Box::new(int_const(5)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(2));
        assert_eq!(stats.arith_folds, 1);
    }

    #[test]
    fn test_no_fold_div_inexact() {
        // 7 / 2 -> not folded (non-exact real division)
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_const(7)),
            op: TirArithOp::Div,
            right: Box::new(int_const(2)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert!(matches!(result.node, TirExpr::ArithBinOp { .. }));
        assert_eq!(stats.arith_folds, 0);
    }

    #[test]
    fn test_no_fold_div_by_zero() {
        // 5 / 0 -> not folded
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_const(5)),
            op: TirArithOp::Div,
            right: Box::new(int_const(0)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert!(matches!(result.node, TirExpr::ArithBinOp { .. }));
        assert_eq!(stats.arith_folds, 0);
    }

    #[test]
    fn test_fold_neg() {
        // -(5) -> -5
        let expr = spanned(TirExpr::ArithNeg(Box::new(int_const(5))));
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(-5));
        assert_eq!(stats.arith_folds, 1);
    }

    #[test]
    fn test_fold_nested_arith() {
        // (3 + 4) * 2 -> 14
        let inner = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_const(3)),
            op: TirArithOp::Add,
            right: Box::new(int_const(4)),
        });
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(inner),
            op: TirArithOp::Mul,
            right: Box::new(int_const(2)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(14));
        assert_eq!(stats.arith_folds, 2);
    }

    #[test]
    fn test_no_fold_arith_with_var() {
        // x + 4 -> not folded
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_var("x")),
            op: TirArithOp::Add,
            right: Box::new(int_const(4)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert!(matches!(result.node, TirExpr::ArithBinOp { .. }));
        assert_eq!(stats.arith_folds, 0);
    }

    // =========================================================
    // Boolean folding
    // =========================================================

    #[test]
    fn test_fold_and_both_const() {
        // TRUE /\ FALSE -> FALSE
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(bool_const(true)),
            op: TirBoolOp::And,
            right: Box::new(bool_const(false)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(false));
        assert_eq!(stats.bool_folds, 1);
    }

    #[test]
    fn test_fold_or_both_true() {
        // TRUE \/ TRUE -> TRUE
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(bool_const(true)),
            op: TirBoolOp::Or,
            right: Box::new(bool_const(true)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.bool_folds, 1);
    }

    #[test]
    fn test_fold_implies() {
        // FALSE => TRUE -> TRUE
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(bool_const(false)),
            op: TirBoolOp::Implies,
            right: Box::new(bool_const(true)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.bool_folds, 1);
    }

    #[test]
    fn test_fold_equiv() {
        // TRUE <=> TRUE -> TRUE
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(bool_const(true)),
            op: TirBoolOp::Equiv,
            right: Box::new(bool_const(true)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.bool_folds, 1);
    }

    #[test]
    fn test_fold_not() {
        // ~TRUE -> FALSE
        let expr = spanned(TirExpr::BoolNot(Box::new(bool_const(true))));
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(false));
        assert_eq!(stats.bool_folds, 1);
    }

    // --- Short-circuit simplifications ---

    #[test]
    fn test_and_true_x_simplifies_to_x() {
        // TRUE /\ x -> x
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(bool_const(true)),
            op: TirBoolOp::And,
            right: Box::new(bool_var("x")),
        });
        let (result, stats) = const_prop_expr(expr);
        assert!(matches!(result.node, TirExpr::Name(_)));
        assert_eq!(stats.bool_folds, 1);
    }

    #[test]
    fn test_and_false_x_simplifies_to_false() {
        // FALSE /\ x -> FALSE
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(bool_const(false)),
            op: TirBoolOp::And,
            right: Box::new(bool_var("x")),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(false));
        assert_eq!(stats.bool_folds, 1);
    }

    #[test]
    fn test_or_true_x_simplifies_to_true() {
        // TRUE \/ x -> TRUE
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(bool_const(true)),
            op: TirBoolOp::Or,
            right: Box::new(bool_var("x")),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.bool_folds, 1);
    }

    #[test]
    fn test_or_false_x_simplifies_to_x() {
        // FALSE \/ x -> x
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(bool_const(false)),
            op: TirBoolOp::Or,
            right: Box::new(bool_var("x")),
        });
        let (result, stats) = const_prop_expr(expr);
        assert!(matches!(result.node, TirExpr::Name(_)));
        assert_eq!(stats.bool_folds, 1);
    }

    #[test]
    fn test_implies_false_x_simplifies_to_true() {
        // FALSE => x -> TRUE
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(bool_const(false)),
            op: TirBoolOp::Implies,
            right: Box::new(bool_var("x")),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.bool_folds, 1);
    }

    #[test]
    fn test_implies_true_x_simplifies_to_x() {
        // TRUE => x -> x
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(bool_const(true)),
            op: TirBoolOp::Implies,
            right: Box::new(bool_var("x")),
        });
        let (result, stats) = const_prop_expr(expr);
        assert!(matches!(result.node, TirExpr::Name(_)));
        assert_eq!(stats.bool_folds, 1);
    }

    #[test]
    fn test_x_and_true_simplifies_to_x() {
        // x /\ TRUE -> x
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(bool_var("x")),
            op: TirBoolOp::And,
            right: Box::new(bool_const(true)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert!(matches!(result.node, TirExpr::Name(_)));
        assert_eq!(stats.bool_folds, 1);
    }

    #[test]
    fn test_x_or_false_simplifies_to_x() {
        // x \/ FALSE -> x
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(bool_var("x")),
            op: TirBoolOp::Or,
            right: Box::new(bool_const(false)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert!(matches!(result.node, TirExpr::Name(_)));
        assert_eq!(stats.bool_folds, 1);
    }

    // =========================================================
    // Comparison folding
    // =========================================================

    #[test]
    fn test_fold_cmp_lt_true() {
        // 3 < 5 -> TRUE
        let expr = spanned(TirExpr::Cmp {
            left: Box::new(int_const(3)),
            op: TirCmpOp::Lt,
            right: Box::new(int_const(5)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.cmp_folds, 1);
    }

    #[test]
    fn test_fold_cmp_lt_false() {
        // 5 < 3 -> FALSE
        let expr = spanned(TirExpr::Cmp {
            left: Box::new(int_const(5)),
            op: TirCmpOp::Lt,
            right: Box::new(int_const(3)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(false));
        assert_eq!(stats.cmp_folds, 1);
    }

    #[test]
    fn test_fold_cmp_eq() {
        // 5 = 5 -> TRUE
        let expr = spanned(TirExpr::Cmp {
            left: Box::new(int_const(5)),
            op: TirCmpOp::Eq,
            right: Box::new(int_const(5)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.cmp_folds, 1);
    }

    #[test]
    fn test_fold_cmp_neq() {
        // 3 /= 5 -> TRUE
        let expr = spanned(TirExpr::Cmp {
            left: Box::new(int_const(3)),
            op: TirCmpOp::Neq,
            right: Box::new(int_const(5)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.cmp_folds, 1);
    }

    #[test]
    fn test_fold_cmp_geq() {
        // 5 >= 5 -> TRUE
        let expr = spanned(TirExpr::Cmp {
            left: Box::new(int_const(5)),
            op: TirCmpOp::Geq,
            right: Box::new(int_const(5)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.cmp_folds, 1);
    }

    #[test]
    fn test_fold_cmp_leq() {
        // 3 <= 5 -> TRUE
        let expr = spanned(TirExpr::Cmp {
            left: Box::new(int_const(3)),
            op: TirCmpOp::Leq,
            right: Box::new(int_const(5)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.cmp_folds, 1);
    }

    #[test]
    fn test_fold_cmp_gt() {
        // 10 > 3 -> TRUE
        let expr = spanned(TirExpr::Cmp {
            left: Box::new(int_const(10)),
            op: TirCmpOp::Gt,
            right: Box::new(int_const(3)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.cmp_folds, 1);
    }

    #[test]
    fn test_fold_cmp_bool_eq() {
        // TRUE = TRUE -> TRUE
        let expr = spanned(TirExpr::Cmp {
            left: Box::new(bool_const(true)),
            op: TirCmpOp::Eq,
            right: Box::new(bool_const(true)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.cmp_folds, 1);
    }

    #[test]
    fn test_fold_cmp_bool_neq() {
        // TRUE /= FALSE -> TRUE
        let expr = spanned(TirExpr::Cmp {
            left: Box::new(bool_const(true)),
            op: TirCmpOp::Neq,
            right: Box::new(bool_const(false)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.cmp_folds, 1);
    }

    #[test]
    fn test_no_fold_cmp_with_var() {
        // x < 5 -> not folded
        let expr = spanned(TirExpr::Cmp {
            left: Box::new(int_var("x")),
            op: TirCmpOp::Lt,
            right: Box::new(int_const(5)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert!(matches!(result.node, TirExpr::Cmp { .. }));
        assert_eq!(stats.cmp_folds, 0);
    }

    // =========================================================
    // IF/THEN/ELSE simplification
    // =========================================================

    #[test]
    fn test_if_true_simplifies_to_then() {
        // IF TRUE THEN 1 ELSE 2 -> 1
        let expr = spanned(TirExpr::If {
            cond: Box::new(bool_const(true)),
            then_: Box::new(int_const(1)),
            else_: Box::new(int_const(2)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(1));
        assert_eq!(stats.if_simplifications, 1);
    }

    #[test]
    fn test_if_false_simplifies_to_else() {
        // IF FALSE THEN 1 ELSE 2 -> 2
        let expr = spanned(TirExpr::If {
            cond: Box::new(bool_const(false)),
            then_: Box::new(int_const(1)),
            else_: Box::new(int_const(2)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(2));
        assert_eq!(stats.if_simplifications, 1);
    }

    #[test]
    fn test_if_non_const_cond_not_simplified() {
        // IF x THEN 1 ELSE 2 -> not simplified
        let expr = spanned(TirExpr::If {
            cond: Box::new(bool_var("x")),
            then_: Box::new(int_const(1)),
            else_: Box::new(int_const(2)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert!(matches!(result.node, TirExpr::If { .. }));
        assert_eq!(stats.if_simplifications, 0);
    }

    #[test]
    fn test_if_folded_cond() {
        // IF 3 < 5 THEN 10 ELSE 20 -> 10
        let expr = spanned(TirExpr::If {
            cond: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(int_const(3)),
                op: TirCmpOp::Lt,
                right: Box::new(int_const(5)),
            })),
            then_: Box::new(int_const(10)),
            else_: Box::new(int_const(20)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(10));
        assert_eq!(stats.cmp_folds, 1);
        assert_eq!(stats.if_simplifications, 1);
    }

    // =========================================================
    // LET propagation
    // =========================================================

    #[test]
    fn test_let_const_propagation() {
        // LET N == 5 IN N + 3 -> 8
        let n_id = intern_name("N_let_test");
        let def = TirLetDef {
            name: "N_let_test".to_string(),
            name_id: n_id,
            params: vec![],
            body: int_const(5),
        };
        let body = spanned(TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Name(TirNameRef {
                name: "N_let_test".to_string(),
                name_id: n_id,
                kind: TirNameKind::Ident,
                ty: TirType::Int,
            }))),
            op: TirArithOp::Add,
            right: Box::new(int_const(3)),
        });
        let expr = spanned(TirExpr::Let {
            defs: vec![def],
            body: Box::new(body),
        });
        let (result, stats) = const_prop_expr(expr);
        // The LET was eliminated (all defs propagated) and the result folded
        assert_eq!(as_const_int(&result.node), Some(8));
        assert!(stats.let_propagations > 0);
        assert!(stats.arith_folds > 0);
    }

    #[test]
    fn test_let_non_const_not_propagated() {
        // LET N == x IN N + 3 -> LET N == x IN N + 3 (N is not constant)
        let n_id = intern_name("N_nc_test");
        let def = TirLetDef {
            name: "N_nc_test".to_string(),
            name_id: n_id,
            params: vec![],
            body: int_var("x"),
        };
        let body = spanned(TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Name(TirNameRef {
                name: "N_nc_test".to_string(),
                name_id: n_id,
                kind: TirNameKind::Ident,
                ty: TirType::Int,
            }))),
            op: TirArithOp::Add,
            right: Box::new(int_const(3)),
        });
        let expr = spanned(TirExpr::Let {
            defs: vec![def],
            body: Box::new(body),
        });
        let (result, stats) = const_prop_expr(expr);
        assert!(matches!(result.node, TirExpr::Let { .. }));
        assert_eq!(stats.let_propagations, 0);
    }

    #[test]
    fn test_let_with_params_not_propagated() {
        // LET F(x) == 5 IN ... -> F has params, not propagated
        let f_id = intern_name("F_param_test");
        let def = TirLetDef {
            name: "F_param_test".to_string(),
            name_id: f_id,
            params: vec!["x".to_string()],
            body: int_const(5),
        };
        let body = int_const(10);
        let expr = spanned(TirExpr::Let {
            defs: vec![def],
            body: Box::new(body),
        });
        let (result, stats) = const_prop_expr(expr);
        // The LET remains because the def has params
        assert!(matches!(result.node, TirExpr::Let { .. }));
        assert_eq!(stats.let_propagations, 0);
    }

    #[test]
    fn test_let_multiple_defs_partial_propagation() {
        // LET C == 10
        //     V == x
        // IN  C + V
        // -> LET V == x IN 10 + V
        let c_id = intern_name("C_partial");
        let v_id = intern_name("V_partial");
        let def_c = TirLetDef {
            name: "C_partial".to_string(),
            name_id: c_id,
            params: vec![],
            body: int_const(10),
        };
        let def_v = TirLetDef {
            name: "V_partial".to_string(),
            name_id: v_id,
            params: vec![],
            body: int_var("x"),
        };
        let body = spanned(TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::Name(TirNameRef {
                name: "C_partial".to_string(),
                name_id: c_id,
                kind: TirNameKind::Ident,
                ty: TirType::Int,
            }))),
            op: TirArithOp::Add,
            right: Box::new(spanned(TirExpr::Name(TirNameRef {
                name: "V_partial".to_string(),
                name_id: v_id,
                kind: TirNameKind::Ident,
                ty: TirType::Int,
            }))),
        });
        let expr = spanned(TirExpr::Let {
            defs: vec![def_c, def_v],
            body: Box::new(body),
        });
        let (result, stats) = const_prop_expr(expr);
        // C was propagated (constant), V was not
        assert!(stats.let_propagations > 0);
        // The result should still have a LET (for V)
        match &result.node {
            TirExpr::Let { defs, body } => {
                assert_eq!(defs.len(), 1);
                assert_eq!(defs[0].name, "V_partial");
                // Body should be ArithBinOp with left = Const(10)
                match &body.node {
                    TirExpr::ArithBinOp { left, .. } => {
                        assert_eq!(as_const_int(&left.node), Some(10));
                    }
                    _ => panic!("expected ArithBinOp body"),
                }
            }
            _ => panic!("expected Let, got {:?}", result.node),
        }
    }

    // =========================================================
    // Combined / cascading folding
    // =========================================================

    #[test]
    fn test_cascading_if_and_arith() {
        // IF 1 < 2 THEN 3 + 4 ELSE 5 * 6 -> 7
        let expr = spanned(TirExpr::If {
            cond: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(int_const(1)),
                op: TirCmpOp::Lt,
                right: Box::new(int_const(2)),
            })),
            then_: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(int_const(3)),
                op: TirArithOp::Add,
                right: Box::new(int_const(4)),
            })),
            else_: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(int_const(5)),
                op: TirArithOp::Mul,
                right: Box::new(int_const(6)),
            })),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(7));
        assert_eq!(stats.cmp_folds, 1);
        assert_eq!(stats.arith_folds, 2); // both branches folded before IF simplification
        assert_eq!(stats.if_simplifications, 1);
    }

    #[test]
    fn test_nested_bool_and_cmp() {
        // (3 < 5) /\ (10 > 2) -> TRUE /\ TRUE -> TRUE
        let expr = spanned(TirExpr::BoolBinOp {
            left: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(int_const(3)),
                op: TirCmpOp::Lt,
                right: Box::new(int_const(5)),
            })),
            op: TirBoolOp::And,
            right: Box::new(spanned(TirExpr::Cmp {
                left: Box::new(int_const(10)),
                op: TirCmpOp::Gt,
                right: Box::new(int_const(2)),
            })),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.cmp_folds, 2);
        assert_eq!(stats.bool_folds, 1);
    }

    // =========================================================
    // Edge cases
    // =========================================================

    #[test]
    fn test_const_unchanged() {
        // A bare constant is returned as-is
        let expr = int_const(42);
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(42));
        assert_eq!(stats, ConstPropStats::default());
    }

    #[test]
    fn test_label_transparent() {
        // LBL:: (3 + 4) -> LBL:: 7
        let inner = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_const(3)),
            op: TirArithOp::Add,
            right: Box::new(int_const(4)),
        });
        let expr = spanned(TirExpr::Label {
            name: "lbl".to_string(),
            body: Box::new(inner),
        });
        let (result, stats) = const_prop_expr(expr);
        match &result.node {
            TirExpr::Label { body, .. } => {
                assert_eq!(as_const_int(&body.node), Some(7));
            }
            _ => panic!("expected Label"),
        }
        assert_eq!(stats.arith_folds, 1);
    }

    #[test]
    fn test_fold_negative_mod_euclidean() {
        // (-7) % 3 -> 2 (Euclidean, always non-negative)
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(spanned(TirExpr::ArithNeg(Box::new(int_const(7))))),
            op: TirArithOp::Mod,
            right: Box::new(int_const(3)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(2));
        assert!(stats.arith_folds >= 2); // neg + mod
    }

    #[test]
    fn test_fold_pow_zero_exponent() {
        // 5 ^ 0 -> 1
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_const(5)),
            op: TirArithOp::Pow,
            right: Box::new(int_const(0)),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(1));
        assert_eq!(stats.arith_folds, 1);
    }

    #[test]
    fn test_no_fold_pow_negative_exponent() {
        // 2 ^ (-1) -> not folded
        let expr = spanned(TirExpr::ArithBinOp {
            left: Box::new(int_const(2)),
            op: TirArithOp::Pow,
            right: Box::new(spanned(TirExpr::ArithNeg(Box::new(int_const(1))))),
        });
        let (result, _stats) = const_prop_expr(expr);
        // The negation folds to -1, but 2^(-1) does not fold
        assert!(matches!(result.node, TirExpr::ArithBinOp { .. }));
    }

    #[test]
    fn test_stats_default() {
        let stats = ConstPropStats::default();
        assert_eq!(stats.arith_folds, 0);
        assert_eq!(stats.bool_folds, 0);
        assert_eq!(stats.cmp_folds, 0);
        assert_eq!(stats.if_simplifications, 0);
        assert_eq!(stats.let_propagations, 0);
    }

    #[test]
    fn test_fold_double_negation() {
        // ~(~TRUE) -> TRUE
        let expr = spanned(TirExpr::BoolNot(Box::new(spanned(TirExpr::BoolNot(
            Box::new(bool_const(true)),
        )))));
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert_eq!(stats.bool_folds, 2);
    }

    #[test]
    fn test_fold_arith_neg_of_neg() {
        // -(-(3)) -> 3
        let expr = spanned(TirExpr::ArithNeg(Box::new(spanned(TirExpr::ArithNeg(
            Box::new(int_const(3)),
        )))));
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_int(&result.node), Some(3));
        assert_eq!(stats.arith_folds, 2);
    }

    #[test]
    fn test_let_const_used_in_comparison() {
        // LET N == 10 IN N > 5 -> TRUE
        let n_id = intern_name("N_cmp_test");
        let def = TirLetDef {
            name: "N_cmp_test".to_string(),
            name_id: n_id,
            params: vec![],
            body: int_const(10),
        };
        let body = spanned(TirExpr::Cmp {
            left: Box::new(spanned(TirExpr::Name(TirNameRef {
                name: "N_cmp_test".to_string(),
                name_id: n_id,
                kind: TirNameKind::Ident,
                ty: TirType::Int,
            }))),
            op: TirCmpOp::Gt,
            right: Box::new(int_const(5)),
        });
        let expr = spanned(TirExpr::Let {
            defs: vec![def],
            body: Box::new(body),
        });
        let (result, stats) = const_prop_expr(expr);
        assert_eq!(as_const_bool(&result.node), Some(true));
        assert!(stats.let_propagations > 0);
        assert_eq!(stats.cmp_folds, 1);
    }

    #[test]
    fn test_set_enum_children_folded() {
        // {3 + 4, 2 * 5} -> {7, 10}
        let expr = spanned(TirExpr::SetEnum(vec![
            spanned(TirExpr::ArithBinOp {
                left: Box::new(int_const(3)),
                op: TirArithOp::Add,
                right: Box::new(int_const(4)),
            }),
            spanned(TirExpr::ArithBinOp {
                left: Box::new(int_const(2)),
                op: TirArithOp::Mul,
                right: Box::new(int_const(5)),
            }),
        ]));
        let (result, stats) = const_prop_expr(expr);
        match &result.node {
            TirExpr::SetEnum(elems) => {
                assert_eq!(elems.len(), 2);
                assert_eq!(as_const_int(&elems[0].node), Some(7));
                assert_eq!(as_const_int(&elems[1].node), Some(10));
            }
            _ => panic!("expected SetEnum"),
        }
        assert_eq!(stats.arith_folds, 2);
    }

    #[test]
    fn test_case_arms_folded() {
        // CASE 1 > 0 -> 3 + 4 [] OTHER -> 0
        let arm = TirCaseArm {
            guard: spanned(TirExpr::Cmp {
                left: Box::new(int_const(1)),
                op: TirCmpOp::Gt,
                right: Box::new(int_const(0)),
            }),
            body: spanned(TirExpr::ArithBinOp {
                left: Box::new(int_const(3)),
                op: TirArithOp::Add,
                right: Box::new(int_const(4)),
            }),
        };
        let expr = spanned(TirExpr::Case {
            arms: vec![arm],
            other: Some(Box::new(int_const(0))),
        });
        let (result, stats) = const_prop_expr(expr);
        match &result.node {
            TirExpr::Case { arms, .. } => {
                assert_eq!(as_const_bool(&arms[0].guard.node), Some(true));
                assert_eq!(as_const_int(&arms[0].body.node), Some(7));
            }
            _ => panic!("expected Case"),
        }
        assert_eq!(stats.cmp_folds, 1);
        assert_eq!(stats.arith_folds, 1);
    }

    #[test]
    fn test_range_children_folded() {
        // (1+2)..(3+4) -> 3..7
        let expr = spanned(TirExpr::Range {
            lo: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(int_const(1)),
                op: TirArithOp::Add,
                right: Box::new(int_const(2)),
            })),
            hi: Box::new(spanned(TirExpr::ArithBinOp {
                left: Box::new(int_const(3)),
                op: TirArithOp::Add,
                right: Box::new(int_const(4)),
            })),
        });
        let (result, stats) = const_prop_expr(expr);
        match &result.node {
            TirExpr::Range { lo, hi } => {
                assert_eq!(as_const_int(&lo.node), Some(3));
                assert_eq!(as_const_int(&hi.node), Some(7));
            }
            _ => panic!("expected Range"),
        }
        assert_eq!(stats.arith_folds, 2);
    }
}
