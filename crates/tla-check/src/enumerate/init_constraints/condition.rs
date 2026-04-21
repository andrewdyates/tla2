// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Condition constraint extraction for IF-THEN-ELSE handling and
//! conjunction remainder stripping.

use super::eval_helpers::{eval_for_init, init_domain_from_value};
use super::is_state_var;
use super::Constraint;
use super::EvalCtx;
use tla_core::ast::Expr;
use tla_core::Spanned;
use tla_eval::tir::TirProgram;

/// Prepend a constraint to all branches.
pub(super) fn prepend_constraint(
    branches: &[Vec<Constraint>],
    constraint: &Constraint,
) -> Vec<Vec<Constraint>> {
    branches
        .iter()
        .map(|branch| {
            let mut merged = vec![constraint.clone()];
            merged.extend(branch.iter().cloned());
            merged
        })
        .collect()
}

/// Extract a single constraint from a condition expression.
/// Used for IF-THEN-ELSE handling.
/// Part of #3194: uses TIR leaf eval when `tir` is `Some`.
pub(super) fn extract_constraint_from_condition(
    ctx: &EvalCtx,
    expr: &Expr,
    tir: Option<&TirProgram<'_>>,
) -> Option<Constraint> {
    match expr {
        // Equality: x = value
        // Part of #232: Handle both Ident and StateVar for variables
        Expr::Eq(lhs, rhs) => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &lhs.node {
                if is_state_var(name, ctx) {
                    if let Some(value) =
                        eval_for_init(ctx, rhs, "extract_constraint_from_condition", tir)
                    {
                        return Some(Constraint::Eq(name.clone(), value));
                    }
                }
            }
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &rhs.node {
                if is_state_var(name, ctx) {
                    if let Some(value) =
                        eval_for_init(ctx, lhs, "extract_constraint_from_condition", tir)
                    {
                        return Some(Constraint::Eq(name.clone(), value));
                    }
                }
            }
            None
        }
        // Inequality: x /= value
        // Part of #232: Handle both Ident and StateVar for variables
        Expr::Neq(lhs, rhs) => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &lhs.node {
                if is_state_var(name, ctx) {
                    if let Some(value) =
                        eval_for_init(ctx, rhs, "extract_constraint_from_condition", tir)
                    {
                        return Some(Constraint::NotEq(name.clone(), value));
                    }
                }
            }
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &rhs.node {
                if is_state_var(name, ctx) {
                    if let Some(value) =
                        eval_for_init(ctx, lhs, "extract_constraint_from_condition", tir)
                    {
                        return Some(Constraint::NotEq(name.clone(), value));
                    }
                }
            }
            None
        }
        // Membership: x \in S
        // Part of #232: Handle both Ident and StateVar for variables
        Expr::In(lhs, rhs) => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &lhs.node {
                if is_state_var(name, ctx) {
                    if let Some(set_val) =
                        eval_for_init(ctx, rhs, "extract_constraint_from_condition", tir)
                    {
                        if let Some(domain) = init_domain_from_value(
                            ctx,
                            set_val,
                            Some(rhs.span),
                            "extract_constraint_from_condition",
                        ) {
                            return Some(Constraint::In(name.clone(), domain));
                        }
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Negate a condition expression to produce a constraint.
/// For example, negating x = 0 produces x /= 0.
/// Part of #232: Handle both Ident and StateVar for variables.
/// Part of #3194: uses TIR leaf eval when `tir` is `Some`.
pub(super) fn negate_condition(
    ctx: &EvalCtx,
    expr: &Expr,
    tir: Option<&TirProgram<'_>>,
) -> Option<Constraint> {
    match expr {
        // Negation of x = value is x /= value
        Expr::Eq(lhs, rhs) => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &lhs.node {
                if is_state_var(name, ctx) {
                    if let Some(value) = eval_for_init(ctx, rhs, "negate_condition", tir) {
                        return Some(Constraint::NotEq(name.clone(), value));
                    }
                }
            }
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &rhs.node {
                if is_state_var(name, ctx) {
                    if let Some(value) = eval_for_init(ctx, lhs, "negate_condition", tir) {
                        return Some(Constraint::NotEq(name.clone(), value));
                    }
                }
            }
            None
        }
        // Negation of x /= value is x = value
        Expr::Neq(lhs, rhs) => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &lhs.node {
                if is_state_var(name, ctx) {
                    if let Some(value) = eval_for_init(ctx, rhs, "negate_condition", tir) {
                        return Some(Constraint::Eq(name.clone(), value));
                    }
                }
            }
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &rhs.node {
                if is_state_var(name, ctx) {
                    if let Some(value) = eval_for_init(ctx, lhs, "negate_condition", tir) {
                        return Some(Constraint::Eq(name.clone(), value));
                    }
                }
            }
            None
        }
        // Can't easily negate other constraints (like x \in S -> x \notin S)
        _ => None,
    }
}

/// Extract the "remainder" of a conjunction after removing the conjunct referencing a specific operator.
///
/// When Init = A /\ B and we're enumerating from A (e.g., TypeOK), we don't need to re-evaluate A
/// in the filter - we only need to evaluate B. This function extracts B given A's name.
///
/// Returns Some(remainder) if the named conjunct is found and removed.
/// Returns None if the named conjunct is not found as a top-level conjunct.
pub fn extract_conjunction_remainder(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    conjunct_name: &str,
) -> Option<Spanned<Expr>> {
    extract_remainder_rec(ctx, expr, conjunct_name)
}

fn extract_remainder_rec(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    conjunct_name: &str,
) -> Option<Spanned<Expr>> {
    match &expr.node {
        // If this is a direct reference to the conjunct name, the remainder is "true"
        // (i.e., nothing else to check)
        Expr::Ident(name, _) if name == conjunct_name => {
            // Return Bool(true) to indicate this conjunct is removed
            Some(Spanned {
                node: Expr::Bool(true),
                span: expr.span,
            })
        }

        // Conjunction: try to remove the named conjunct from either side
        Expr::And(a, b) => {
            // Try removing from left side
            if let Some(left_remainder) = extract_remainder_rec(ctx, a, conjunct_name) {
                // Left contained the conjunct - result is left_remainder /\ b
                if matches!(left_remainder.node, Expr::Bool(true)) {
                    // If left is just "true", return right only
                    return Some((**b).clone());
                }
                // Otherwise combine left_remainder with right
                return Some(Spanned {
                    node: Expr::And(Box::new(left_remainder), b.clone()),
                    span: expr.span,
                });
            }

            // Try removing from right side
            if let Some(right_remainder) = extract_remainder_rec(ctx, b, conjunct_name) {
                // Right contained the conjunct - result is a /\ right_remainder
                if matches!(right_remainder.node, Expr::Bool(true)) {
                    // If right is just "true", return left only
                    return Some((**a).clone());
                }
                // Otherwise combine left with right_remainder
                return Some(Spanned {
                    node: Expr::And(a.clone(), Box::new(right_remainder)),
                    span: expr.span,
                });
            }

            // Conjunct name not found in either side
            None
        }

        // Operator application: check if it's calling the conjunct operator
        Expr::Apply(op, args) => {
            // Check if this is a call to a user-defined operator that matches conjunct_name
            if let Expr::Ident(op_name, _) = &op.node {
                // First, try to expand the operator definition
                if let Some(def) = ctx.get_op(op_name) {
                    if def.params.is_empty() && args.is_empty() {
                        // No-arg operator - check if its body can have the conjunct removed
                        if let Some(remainder) =
                            extract_remainder_rec(ctx, &def.body, conjunct_name)
                        {
                            return Some(remainder);
                        }
                    }
                }
            }
            None
        }

        // Other expressions: conjunct not found at this level
        _ => None,
    }
}
