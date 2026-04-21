// Author: Andrew Yates
// Copyright 2026 Andrew Yates. Apache-2.0.
//
// Context-aware visitors that classify expressions by prime/action-level behavior.

use rustc_hash::FxHashSet;
use std::sync::Arc;

use tla_core::ast::Expr;
use tla_core::Spanned;

use super::super::visitors_simple::expr_contains_prime_v;
use super::super::{walk_expr, ExprVisitor};
use crate::eval::EvalCtx;

/// Checks if an expression contains primed variables, following operator
/// definitions via `EvalCtx`. Uses a `visited` set to prevent infinite
/// recursion on recursive operators.
/// Replaces `expr_contains_prime_ctx_inner` in enumerate/expr_analysis.rs.
pub(crate) struct ContainsPrimeCtx<'a> {
    ctx: &'a EvalCtx,
    visited: FxHashSet<Arc<str>>,
}

impl ExprVisitor for ContainsPrimeCtx<'_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Prime(_) | Expr::Unchanged(_) => Some(true),
            // ENABLED is state-level: primes inside are scoped (#1640).
            Expr::Enabled(_) => Some(false),
            Expr::Ident(name, _) => {
                // FIX #1473: resolve through op_replacements before lookup
                let resolved = self.ctx.resolve_op_name(name.as_str());
                if let Some(def) = self.ctx.get_op(resolved) {
                    if def.params.is_empty() {
                        let op_key = Arc::from(resolved);
                        if self.visited.contains(&op_key) {
                            return Some(false);
                        }
                        self.visited.insert(op_key);
                        return Some(walk_expr(self, &def.body.node));
                    }
                }
                Some(false)
            }
            _ => None,
        }
    }

    fn visit_apply(&mut self, op_expr: &Spanned<Expr>, args: &[Spanned<Expr>]) -> Option<bool> {
        if let Expr::Ident(op_name, _) = &op_expr.node {
            // FIX #1473: resolve through op_replacements before lookup
            let resolved = self.ctx.resolve_op_name(op_name.as_str());
            if let Some(def) = self.ctx.get_op(resolved) {
                let op_key = Arc::from(resolved);
                if self.visited.contains(&op_key) {
                    let args_result = args.iter().any(|a| walk_expr(self, &a.node));
                    return Some(args_result);
                }
                self.visited.insert(op_key);
                if walk_expr(self, &def.body.node) {
                    return Some(true);
                }
            }
        }
        None
    }
}

/// Check if an expression contains primed variables, following operator
/// definitions via `EvalCtx`.
pub(crate) fn expr_contains_prime_ctx_v(ctx: &EvalCtx, expr: &Expr) -> bool {
    walk_expr(
        &mut ContainsPrimeCtx {
            ctx,
            visited: FxHashSet::default(),
        },
        expr,
    )
}

// Part of #3354 Slice 4: ContainsPrimeWithCtxMetadata and expr_contains_prime_with_ctx_v
// removed — only consumed by compiled_guard module.

/// Checks if an expression is action-level (contains Prime/Unchanged),
/// following zero-param operator definitions via `EvalCtx`.
/// Replaces `expr_is_action_level` in enumerate/expr_analysis.rs.
pub(crate) struct IsActionLevel<'a> {
    ctx: &'a EvalCtx,
}

impl ExprVisitor for IsActionLevel<'_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Prime(_) | Expr::Unchanged(_) => Some(true),
            // ENABLED is state-level: primes inside are scoped (#1640).
            Expr::Enabled(_) => Some(false),
            Expr::Ident(name, _) => {
                // FIX #1473: resolve through op_replacements before lookup
                let resolved = self.ctx.resolve_op_name(name.as_str());
                if let Some(def) = self.ctx.get_op(resolved) {
                    if def.params.is_empty() {
                        return Some(expr_contains_prime_v(&def.body.node));
                    }
                }
                Some(false)
            }
            _ => None,
        }
    }

    fn visit_apply(&mut self, op_expr: &Spanned<Expr>, args: &[Spanned<Expr>]) -> Option<bool> {
        if args.iter().any(|a| walk_expr(self, &a.node)) {
            return Some(true);
        }
        if let Expr::Ident(op_name, _) = &op_expr.node {
            // FIX #1473: resolve through op_replacements before lookup
            let resolved = self.ctx.resolve_op_name(op_name.as_str());
            if let Some(def) = self.ctx.get_op(resolved) {
                return Some(expr_contains_prime_v(&def.body.node));
            }
        }
        Some(false)
    }
}

/// Check if an expression is action-level, following operator definitions.
pub(crate) fn expr_is_action_level_v(ctx: &EvalCtx, expr: &Expr) -> bool {
    walk_expr(&mut IsActionLevel { ctx }, expr)
}

/// Checks if an expression contains an OR (disjunction) with primed variables
/// in either branch, following operator calls.
/// Replaces `expr_contains_or_with_primed_ctx_inner` in enumerate/expr_analysis.rs.
/// No production callers — retained for test coverage of the visitor pattern.
#[cfg(test)]
pub(crate) struct ContainsOrWithPrimedCtx<'a> {
    ctx: &'a EvalCtx,
    visited: FxHashSet<Arc<str>>,
}

#[cfg(test)]
impl ExprVisitor for ContainsOrWithPrimedCtx<'_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Or(a, b) => {
                let has_primed_or = expr_contains_prime_ctx_v(self.ctx, &a.node)
                    || expr_contains_prime_ctx_v(self.ctx, &b.node);
                if has_primed_or {
                    return Some(true);
                }
                let result = walk_expr(self, &a.node) || walk_expr(self, &b.node);
                Some(result)
            }
            Expr::Ident(name, _) => {
                // FIX #1473: resolve through op_replacements before lookup
                let resolved = self.ctx.resolve_op_name(name.as_str());
                if let Some(def) = self.ctx.get_op(resolved) {
                    if def.params.is_empty() {
                        let op_key = Arc::from(resolved);
                        if self.visited.contains(&op_key) {
                            return Some(false);
                        }
                        self.visited.insert(op_key);
                        return Some(walk_expr(self, &def.body.node));
                    }
                }
                Some(false)
            }
            _ => None,
        }
    }

    fn visit_apply(&mut self, op_expr: &Spanned<Expr>, _args: &[Spanned<Expr>]) -> Option<bool> {
        if let Expr::Ident(op_name, _) = &op_expr.node {
            // FIX #1473: resolve through op_replacements before lookup
            let resolved = self.ctx.resolve_op_name(op_name.as_str());
            if let Some(def) = self.ctx.get_op(resolved) {
                let op_key = Arc::from(resolved);
                if self.visited.contains(&op_key) {
                    return Some(false);
                }
                self.visited.insert(op_key);
                return Some(walk_expr(self, &def.body.node));
            }
        }
        Some(false)
    }
}

/// Check if an expression contains an OR with primed variables, following
/// operator definitions.
/// No production callers — retained for test coverage of the visitor pattern.
#[cfg(test)]
pub(crate) fn expr_contains_or_with_primed_ctx_v(ctx: &EvalCtx, expr: &Expr) -> bool {
    walk_expr(
        &mut ContainsOrWithPrimedCtx {
            ctx,
            visited: FxHashSet::default(),
        },
        expr,
    )
}
