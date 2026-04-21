// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Classification helpers for primed variable detection in successor enumeration.
//!
//! Pure functions that classify TLA+ expressions as primed assignments.
//! Used by the unified enumerator to distinguish guard conditions from
//! state-variable assignments during conjunct processing.
//!
//! Extracted from unified.rs as part of #2360.

use tla_core::ast::Expr;

use crate::eval::EvalCtx;

/// TLC-style dynamic classification of primed assignments.
pub(super) fn get_primed_var<'a>(ctx: &'a EvalCtx, expr: &'a Expr) -> Option<&'a str> {
    match expr {
        Expr::Prime(inner) => match &inner.node {
            Expr::Ident(name, _) => Some(name.as_str()),
            Expr::StateVar(name, _, _) => Some(name.as_str()),
            _ => None,
        },
        Expr::Ident(name, _) => {
            if let Some(def) = ctx.get_op(name) {
                if def.params.is_empty() {
                    return get_primed_var(ctx, &def.body.node);
                }
            }
            None
        }
        Expr::Apply(op_expr, args) => {
            if args.is_empty() {
                if let Expr::Ident(op_name, _) = &op_expr.node {
                    if let Some(def) = ctx.get_op(op_name) {
                        if def.params.is_empty() {
                            return get_primed_var(ctx, &def.body.node);
                        }
                    }
                }
            }
            None
        }
        Expr::Label(label) => get_primed_var(ctx, &label.body.node),
        _ => None,
    }
}

/// Check if an expression is a primed assignment (x' = expr or expr = x').
pub(super) fn is_primed_assignment(ctx: &EvalCtx, expr: &Expr) -> bool {
    match expr {
        Expr::Eq(a, b) => {
            get_primed_var(ctx, &a.node).is_some() || get_primed_var(ctx, &b.node).is_some()
        }
        Expr::And(a, b) => is_primed_assignment(ctx, &a.node) || is_primed_assignment(ctx, &b.node),
        Expr::Label(label) => is_primed_assignment(ctx, &label.body.node),
        _ => false,
    }
}
