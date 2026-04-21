// Author: Andrew Yates
// Copyright 2026 Andrew Yates. Apache-2.0.
//
// Expression utility functions: conjunct collection and substitution application.

use std::collections::HashMap;

use crate::ast::{Expr, Substitution};
use crate::fold::{SpanPolicy, SubstituteExpr};
use crate::{ExprFold, Spanned};

/// Flatten top-level conjunctions into a list of conjunct expressions.
pub fn collect_conjuncts_v(expr: &Spanned<Expr>) -> Vec<Spanned<Expr>> {
    let mut result = Vec::new();
    let mut stack = vec![expr.clone()];

    while let Some(current) = stack.pop() {
        match &current.node {
            Expr::And(left, right) => {
                stack.push((**right).clone());
                stack.push((**left).clone());
            }
            _ => result.push(current),
        }
    }

    result
}

/// Apply substitutions to an expression with capture-avoidance.
pub fn apply_substitutions_v(expr: &Spanned<Expr>, subs: &[Substitution]) -> Spanned<Expr> {
    if subs.is_empty() {
        return expr.clone();
    }
    let sub_map: HashMap<&str, &Spanned<Expr>> =
        subs.iter().map(|s| (s.from.node.as_str(), &s.to)).collect();
    let mut substitute = SubstituteExpr {
        subs: sub_map,
        span_policy: SpanPolicy::Preserve,
    };
    substitute.fold_expr(expr.clone())
}
