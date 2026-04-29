// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TIR preprocessing pipeline: normalize and optimize expressions before
//! model checking.
//!
//! Three passes are applied in order:
//!
//! 1. **NNF (Negation Normal Form):** Push negations inward so they only
//!    appear on atoms. De Morgan's laws, double-negation elimination, and
//!    implication negation.
//!
//! 2. **Keramelization:** Flatten nested conjunctions and disjunctions into
//!    flat n-ary lists, reducing tree depth and enabling better short-circuit
//!    evaluation.
//!
//! 3. **Constant folding:** Evaluate compile-time-known boolean/arithmetic
//!    identities (`TRUE /\ A` -> `A`, `FALSE \/ A` -> `A`, etc.).

#[cfg(test)]
mod tests;

use crate::nodes::{TirBoolOp, TirExpr};
use crate::types::TirType;
use tla_core::Spanned;
use tla_value::Value;

/// Preprocessing pipeline that applies normalization passes to TIR expressions.
///
/// Passes are applied in a fixed order: NNF -> keramelization -> constant
/// folding. Each pass produces a semantically equivalent expression tree.
pub struct PreprocessPipeline {
    /// Enable NNF normalization pass.
    pub nnf: bool,
    /// Enable keramelization (flattening) pass.
    pub keramelize: bool,
    /// Enable constant folding pass.
    pub constant_fold: bool,
}

impl Default for PreprocessPipeline {
    fn default() -> Self {
        Self {
            nnf: true,
            keramelize: true,
            constant_fold: true,
        }
    }
}

impl PreprocessPipeline {
    /// Create a pipeline with all passes enabled.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Run the preprocessing pipeline on a TIR expression tree.
    ///
    /// Returns the transformed expression. The input is consumed.
    #[must_use]
    pub fn run(&self, expr: Spanned<TirExpr>) -> Spanned<TirExpr> {
        let mut result = expr;
        if self.nnf {
            result = nnf_transform(result);
        }
        if self.keramelize {
            result = keramelize(result);
        }
        if self.constant_fold {
            result = constant_fold(result);
        }
        result
    }
}

// ---------------------------------------------------------------------------
// Pass 1: Negation Normal Form (NNF)
// ---------------------------------------------------------------------------

/// Push negations inward so they only appear on atoms.
///
/// - `~(A /\ B)` -> `~A \/ ~B`
/// - `~(A \/ B)` -> `~A /\ ~B`
/// - `~~A` -> `A`
/// - `~(A => B)` -> `A /\ ~B`
/// - `~(A <=> B)` -> `(A /\ ~B) \/ (~A /\ B)`
#[must_use]
pub(crate) fn nnf_transform(expr: Spanned<TirExpr>) -> Spanned<TirExpr> {
    let span = expr.span;
    let node = match expr.node {
        // Core NNF rule: push negation inward.
        TirExpr::BoolNot(inner) => {
            return nnf_negate(*inner);
        }

        // Recurse into binary boolean operators.
        TirExpr::BoolBinOp { left, op, right } => TirExpr::BoolBinOp {
            left: Box::new(nnf_transform(*left)),
            op,
            right: Box::new(nnf_transform(*right)),
        },

        // Recurse into If.
        TirExpr::If { cond, then_, else_ } => TirExpr::If {
            cond: Box::new(nnf_transform(*cond)),
            then_: Box::new(nnf_transform(*then_)),
            else_: Box::new(nnf_transform(*else_)),
        },

        // Recurse into quantifiers.
        TirExpr::Forall { vars, body } => TirExpr::Forall {
            vars,
            body: Box::new(nnf_transform(*body)),
        },
        TirExpr::Exists { vars, body } => TirExpr::Exists {
            vars,
            body: Box::new(nnf_transform(*body)),
        },

        // Everything else is returned as-is (atoms, arithmetic, sets, etc.).
        other => other,
    };
    Spanned { node, span }
}

/// Apply NNF transformation to the negation of an expression.
///
/// This is the core of NNF: given `~expr`, push the negation inward.
#[must_use]
fn nnf_negate(expr: Spanned<TirExpr>) -> Spanned<TirExpr> {
    let span = expr.span;
    let node = match expr.node {
        // ~~A -> A (double negation elimination)
        TirExpr::BoolNot(inner) => {
            return nnf_transform(*inner);
        }

        // ~(A /\ B) -> ~A \/ ~B (De Morgan)
        TirExpr::BoolBinOp {
            left,
            op: TirBoolOp::And,
            right,
        } => TirExpr::BoolBinOp {
            left: Box::new(nnf_negate(*left)),
            op: TirBoolOp::Or,
            right: Box::new(nnf_negate(*right)),
        },

        // ~(A \/ B) -> ~A /\ ~B (De Morgan)
        TirExpr::BoolBinOp {
            left,
            op: TirBoolOp::Or,
            right,
        } => TirExpr::BoolBinOp {
            left: Box::new(nnf_negate(*left)),
            op: TirBoolOp::And,
            right: Box::new(nnf_negate(*right)),
        },

        // ~(A => B) -> A /\ ~B
        TirExpr::BoolBinOp {
            left,
            op: TirBoolOp::Implies,
            right,
        } => TirExpr::BoolBinOp {
            left: Box::new(nnf_transform(*left)),
            op: TirBoolOp::And,
            right: Box::new(nnf_negate(*right)),
        },

        // ~(A <=> B) -> (A /\ ~B) \/ (~A /\ B)
        TirExpr::BoolBinOp {
            left,
            op: TirBoolOp::Equiv,
            right,
        } => {
            let left_clone = (*left).clone();
            let right_clone = (*right).clone();
            TirExpr::BoolBinOp {
                left: Box::new(Spanned {
                    node: TirExpr::BoolBinOp {
                        left: Box::new(nnf_transform(*left)),
                        op: TirBoolOp::And,
                        right: Box::new(nnf_negate(*right)),
                    },
                    span,
                }),
                op: TirBoolOp::Or,
                right: Box::new(Spanned {
                    node: TirExpr::BoolBinOp {
                        left: Box::new(nnf_negate(left_clone)),
                        op: TirBoolOp::And,
                        right: Box::new(nnf_transform(right_clone)),
                    },
                    span,
                }),
            }
        }

        // ~(\A x \in S : P) -> \E x \in S : ~P (quantifier duality)
        TirExpr::Forall { vars, body } => TirExpr::Exists {
            vars,
            body: Box::new(nnf_negate(*body)),
        },

        // ~(\E x \in S : P) -> \A x \in S : ~P (quantifier duality)
        TirExpr::Exists { vars, body } => TirExpr::Forall {
            vars,
            body: Box::new(nnf_negate(*body)),
        },

        // Constant: ~TRUE -> FALSE, ~FALSE -> TRUE
        TirExpr::Const {
            value: Value::Bool(b),
            ty,
        } => TirExpr::Const {
            value: Value::Bool(!b),
            ty,
        },

        // Atom: wrap with BoolNot (negation stays on atom)
        other => TirExpr::BoolNot(Box::new(Spanned {
            node: nnf_transform(Spanned { node: other, span }).node,
            span,
        })),
    };
    Spanned { node, span }
}

// ---------------------------------------------------------------------------
// Pass 2: Keramelization (flatten nested conjunctions/disjunctions)
// ---------------------------------------------------------------------------

/// Flatten nested conjunctions and disjunctions into right-associated chains.
///
/// `(A /\ B) /\ C` -> `A /\ (B /\ C)`.
#[must_use]
pub(crate) fn keramelize(expr: Spanned<TirExpr>) -> Spanned<TirExpr> {
    let span = expr.span;
    let node = match expr.node {
        TirExpr::BoolBinOp {
            left,
            op: op @ (TirBoolOp::And | TirBoolOp::Or),
            right,
        } => {
            let whole = Spanned {
                node: TirExpr::BoolBinOp { left, op, right },
                span,
            };
            let mut operands = Vec::new();
            collect_spanned_operands(&whole, op, &mut operands);

            let mut operands: Vec<Spanned<TirExpr>> =
                operands.into_iter().map(keramelize).collect();

            let last = operands.pop().expect("invariant: at least 2 operands");
            return operands
                .into_iter()
                .rev()
                .fold(last, |acc, operand| Spanned {
                    node: TirExpr::BoolBinOp {
                        left: Box::new(operand),
                        op,
                        right: Box::new(acc),
                    },
                    span,
                });
        }

        TirExpr::BoolBinOp { left, op, right } => TirExpr::BoolBinOp {
            left: Box::new(keramelize(*left)),
            op,
            right: Box::new(keramelize(*right)),
        },

        TirExpr::BoolNot(inner) => TirExpr::BoolNot(Box::new(keramelize(*inner))),

        TirExpr::If { cond, then_, else_ } => TirExpr::If {
            cond: Box::new(keramelize(*cond)),
            then_: Box::new(keramelize(*then_)),
            else_: Box::new(keramelize(*else_)),
        },

        TirExpr::Forall { vars, body } => TirExpr::Forall {
            vars,
            body: Box::new(keramelize(*body)),
        },
        TirExpr::Exists { vars, body } => TirExpr::Exists {
            vars,
            body: Box::new(keramelize(*body)),
        },

        other => other,
    };
    Spanned { node, span }
}

/// Collect all leaf operands from a chain of the given boolean operator.
fn collect_spanned_operands(
    expr: &Spanned<TirExpr>,
    target_op: TirBoolOp,
    out: &mut Vec<Spanned<TirExpr>>,
) {
    if let TirExpr::BoolBinOp { left, op, right } = &expr.node {
        if *op == target_op {
            collect_spanned_operands(left, target_op, out);
            collect_spanned_operands(right, target_op, out);
            return;
        }
    }
    out.push(expr.clone());
}

// ---------------------------------------------------------------------------
// Pass 3: Constant folding
// ---------------------------------------------------------------------------

/// Evaluate compile-time-known boolean identities.
///
/// - `TRUE /\ A` -> `A`, `FALSE /\ _` -> `FALSE`
/// - `FALSE \/ A` -> `A`, `TRUE \/ _` -> `TRUE`
/// - `~TRUE` -> `FALSE`, `~FALSE` -> `TRUE`, `~~A` -> `A`
/// - `IF TRUE THEN A ELSE B` -> `A`, `IF FALSE THEN A ELSE B` -> `B`
/// - `TRUE => A` -> `A`, `FALSE => _` -> `TRUE`
#[must_use]
pub(crate) fn constant_fold(expr: Spanned<TirExpr>) -> Spanned<TirExpr> {
    let span = expr.span;
    let node = match expr.node {
        TirExpr::BoolBinOp { left, op, right } => {
            let left = constant_fold(*left);
            let right = constant_fold(*right);

            match (is_bool_const(&left), op, is_bool_const(&right)) {
                (Some(true), TirBoolOp::And, _) => return right,
                (_, TirBoolOp::And, Some(true)) => return left,
                (Some(false), TirBoolOp::And, _) => return left,
                (_, TirBoolOp::And, Some(false)) => return right,

                (Some(false), TirBoolOp::Or, _) => return right,
                (_, TirBoolOp::Or, Some(false)) => return left,
                (Some(true), TirBoolOp::Or, _) => return left,
                (_, TirBoolOp::Or, Some(true)) => return right,

                (Some(true), TirBoolOp::Implies, _) => return right,
                (Some(false), TirBoolOp::Implies, _) => {
                    return Spanned {
                        node: TirExpr::Const {
                            value: Value::Bool(true),
                            ty: TirType::Bool,
                        },
                        span,
                    }
                }

                (Some(a), TirBoolOp::Equiv, Some(b)) => {
                    return Spanned {
                        node: TirExpr::Const {
                            value: Value::Bool(a == b),
                            ty: TirType::Bool,
                        },
                        span,
                    }
                }

                _ => {}
            }

            TirExpr::BoolBinOp {
                left: Box::new(left),
                op,
                right: Box::new(right),
            }
        }

        TirExpr::BoolNot(inner) => {
            let inner = constant_fold(*inner);
            match is_bool_const(&inner) {
                Some(b) => TirExpr::Const {
                    value: Value::Bool(!b),
                    ty: TirType::Bool,
                },
                None => {
                    if let TirExpr::BoolNot(inner2) = inner.node {
                        return *inner2;
                    }
                    TirExpr::BoolNot(Box::new(inner))
                }
            }
        }

        TirExpr::If { cond, then_, else_ } => {
            let cond = constant_fold(*cond);
            let then_ = constant_fold(*then_);
            let else_ = constant_fold(*else_);

            match is_bool_const(&cond) {
                Some(true) => return then_,
                Some(false) => return else_,
                None => TirExpr::If {
                    cond: Box::new(cond),
                    then_: Box::new(then_),
                    else_: Box::new(else_),
                },
            }
        }

        TirExpr::Forall { vars, body } => TirExpr::Forall {
            vars,
            body: Box::new(constant_fold(*body)),
        },
        TirExpr::Exists { vars, body } => TirExpr::Exists {
            vars,
            body: Box::new(constant_fold(*body)),
        },

        other => other,
    };
    Spanned { node, span }
}

/// Check if a `Spanned<TirExpr>` is a boolean constant, returning its value.
fn is_bool_const(expr: &Spanned<TirExpr>) -> Option<bool> {
    if let TirExpr::Const {
        value: Value::Bool(b),
        ..
    } = &expr.node
    {
        Some(*b)
    } else {
        None
    }
}
