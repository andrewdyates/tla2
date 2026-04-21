// Author: Andrew Yates
// Copyright 2026 Andrew Yates. Apache-2.0.
//
// Context-aware visitors that collect/query primed variable references.

use rustc_hash::FxHashSet;
use std::sync::Arc;

use tla_core::ast::Expr;
use tla_core::Spanned;

use super::super::{walk_expr, ExprVisitor};
use crate::eval::EvalCtx;

/// Collect state-variable references inside an expression already under `Prime(...)`.
///
/// Preserves legacy behavior from enumerate/expr_analysis.rs:
/// - Follow zero-arg `Ident` operator bodies.
/// - Follow `Apply(Ident(...), args)` operator bodies and argument expressions.
/// - Do not recurse into `ModuleRef`, `InstanceExpr`, `Lambda`, `RecordAccess`,
///   `LeadsTo`, `WeakFair`, or `StrongFair`.
struct CollectStateVarRefsUnderPrimeCtx<'a, 'b> {
    ctx: &'a EvalCtx,
    refs: &'b mut FxHashSet<Arc<str>>,
    visited_ops: &'b mut FxHashSet<String>,
}

impl ExprVisitor for CollectStateVarRefsUnderPrimeCtx<'_, '_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::StateVar(name, _, _) => {
                self.refs.insert(Arc::from(name.as_str()));
                Some(false)
            }
            Expr::Ident(name, _) => {
                // FIX #1473: resolve through op_replacements before lookup
                let resolved = self.ctx.resolve_op_name(name.as_str());
                if let Some(def) = self.ctx.get_op(resolved) {
                    if def.params.is_empty() && self.visited_ops.insert(resolved.to_string()) {
                        let _ = walk_expr(self, &def.body.node);
                    }
                }
                Some(false)
            }
            Expr::ModuleRef(_, _, _)
            | Expr::InstanceExpr(_, _)
            | Expr::Lambda(_, _)
            | Expr::RecordAccess(_, _)
            | Expr::LeadsTo(_, _)
            | Expr::WeakFair(_, _)
            | Expr::StrongFair(_, _) => Some(false),
            _ => None,
        }
    }

    fn visit_apply(&mut self, op_expr: &Spanned<Expr>, args: &[Spanned<Expr>]) -> Option<bool> {
        if let Expr::Ident(op_name, _) = &op_expr.node {
            // FIX #1473: resolve through op_replacements before lookup
            let resolved = self.ctx.resolve_op_name(op_name.as_str());
            if let Some(def) = self.ctx.get_op(resolved) {
                if self.visited_ops.insert(resolved.to_string()) {
                    let _ = walk_expr(self, &def.body.node);
                }
            }
        }
        for arg in args {
            let _ = walk_expr(self, &arg.node);
        }
        Some(false)
    }

    fn should_short_circuit(&self, _partial: &bool) -> bool {
        false
    }
}

/// Collects primed variable references while following operator definitions via `EvalCtx`.
///
/// This extends simple `get_primed_var_refs_v` behavior by resolving operator references and
/// by collecting implicit primed dependencies from complex expressions under `Prime(...)`.
pub(crate) struct CollectPrimedVarRefsWithCtx<'a> {
    ctx: &'a EvalCtx,
    refs: FxHashSet<Arc<str>>,
    visited_ops: FxHashSet<String>,
}

impl ExprVisitor for CollectPrimedVarRefsWithCtx<'_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Prime(inner) => {
                if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &inner.node {
                    self.refs.insert(Arc::from(name.as_str()));
                } else {
                    let mut under_prime = CollectStateVarRefsUnderPrimeCtx {
                        ctx: self.ctx,
                        refs: &mut self.refs,
                        visited_ops: &mut self.visited_ops,
                    };
                    let _ = walk_expr(&mut under_prime, &inner.node);
                }
                None
            }
            // ENABLED is state-level: primes inside are scoped (#1654).
            Expr::Enabled(_) => Some(false),
            Expr::Ident(name, _) => {
                // FIX #1473: resolve through op_replacements before lookup
                let resolved = self.ctx.resolve_op_name(name.as_str());
                if let Some(def) = self.ctx.get_op(resolved) {
                    if def.params.is_empty() && self.visited_ops.insert(resolved.to_string()) {
                        let _ = walk_expr(self, &def.body.node);
                    }
                }
                Some(false)
            }
            Expr::OpRef(name) => {
                // FIX #1473: resolve through op_replacements before lookup
                let resolved = self.ctx.resolve_op_name(name.as_str());
                if let Some(def) = self.ctx.get_op(resolved) {
                    if self.visited_ops.insert(resolved.to_string()) {
                        let _ = walk_expr(self, &def.body.node);
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
                if self.visited_ops.insert(resolved.to_string()) {
                    let _ = walk_expr(self, &def.body.node);
                }
            }
        }
        for arg in args {
            let _ = walk_expr(self, &arg.node);
        }
        Some(false)
    }

    fn should_short_circuit(&self, _partial: &bool) -> bool {
        false
    }
}

/// Context-aware version of `get_primed_var_refs_v` that follows operator references.
pub(crate) fn get_primed_var_refs_with_ctx_v(ctx: &EvalCtx, expr: &Expr) -> FxHashSet<Arc<str>> {
    let mut visitor = CollectPrimedVarRefsWithCtx {
        ctx,
        refs: FxHashSet::default(),
        visited_ops: FxHashSet::default(),
    };
    let _ = walk_expr(&mut visitor, expr);
    visitor.refs
}

/// Checks if an expression references any primed variables from a given set,
/// following operator definitions via `EvalCtx`. Also detects implicit primed
/// dependencies from complex expressions under `Prime(...)`.
///
/// Replaces hand-written `expr_references_primed_vars` (and helper
/// `expr_under_prime_references_vars`) in enumerate/expr_analysis.rs.
/// Part of #1192 Wave 2.
pub(crate) struct ExprReferencesPrimedVars<'a> {
    ctx: &'a EvalCtx,
    vars: &'a FxHashSet<Arc<str>>,
    visited_ops: FxHashSet<String>,
}

impl ExprVisitor for ExprReferencesPrimedVars<'_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Prime(inner_expr) => {
                // Check if the primed variable is in our set
                if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &inner_expr.node {
                    // Part of #1564: O(1) FxHashSet lookup instead of O(n) linear scan
                    if self.vars.contains(name.as_str()) {
                        return Some(true);
                    }
                } else {
                    // Complex expression under Prime: state variables inside are
                    // read from the next state, making them implicit primed references.
                    let mut under_prime = CollectStateVarRefsUnderPrimeForVarsCtx {
                        ctx: self.ctx,
                        vars: self.vars,
                        visited_ops: &mut self.visited_ops,
                    };
                    if walk_expr(&mut under_prime, &inner_expr.node) {
                        return Some(true);
                    }
                }
                // Continue recursion for complex primed expressions
                None
            }

            // ENABLED is state-level: primes inside are scoped (#1654).
            Expr::Enabled(_) => Some(false),

            // Expand operator references to check their bodies
            Expr::Ident(name, _) => {
                // FIX #1473: resolve through op_replacements before lookup
                let resolved = self.ctx.resolve_op_name(name.as_str());
                if let Some(def) = self.ctx.get_op(resolved) {
                    if !self.visited_ops.insert(resolved.to_string()) {
                        return Some(false);
                    }
                    Some(walk_expr(self, &def.body.node))
                } else {
                    Some(false)
                }
            }

            Expr::OpRef(name) => {
                // FIX #1473: resolve through op_replacements before lookup
                let resolved = self.ctx.resolve_op_name(name.as_str());
                if let Some(def) = self.ctx.get_op(resolved) {
                    if !self.visited_ops.insert(resolved.to_string()) {
                        return Some(false);
                    }
                    Some(walk_expr(self, &def.body.node))
                } else {
                    Some(false)
                }
            }

            // Leaf expressions
            Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::StateVar(_, _, _) => Some(false),

            // InstanceExpr - ignore
            Expr::InstanceExpr(_, _) => Some(false),

            _ => None, // default traversal
        }
    }

    fn visit_apply(&mut self, op_expr: &Spanned<Expr>, args: &[Spanned<Expr>]) -> Option<bool> {
        // Check operator body
        if let Expr::Ident(name, _) = &op_expr.node {
            // FIX #1473: resolve through op_replacements before lookup
            let resolved = self.ctx.resolve_op_name(name.as_str());
            if let Some(def) = self.ctx.get_op(resolved) {
                if self.visited_ops.insert(resolved.to_string()) && walk_expr(self, &def.body.node)
                {
                    return Some(true);
                }
            }
        }
        // Check arguments
        Some(args.iter().any(|a| walk_expr(self, &a.node)))
    }
}

/// Helper visitor: check if state variables from `vars` appear inside an
/// expression that is under `Prime(...)`. Used to detect implicit primed deps
/// like `neutral(p)'` -> `Prime(And(Not(active[p]), ...))` where `active` is
/// read from the next state.
struct CollectStateVarRefsUnderPrimeForVarsCtx<'a, 'b> {
    ctx: &'a EvalCtx,
    vars: &'a FxHashSet<Arc<str>>,
    visited_ops: &'b mut FxHashSet<String>,
}

impl ExprVisitor for CollectStateVarRefsUnderPrimeForVarsCtx<'_, '_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::StateVar(name, _, _) => {
                // Part of #1564: O(1) FxHashSet lookup instead of O(n) linear scan
                Some(self.vars.contains(name.as_str()))
            }
            Expr::Ident(name, _) => {
                // FIX #1473: resolve through op_replacements before lookup
                let resolved = self.ctx.resolve_op_name(name.as_str());
                if let Some(def) = self.ctx.get_op(resolved) {
                    if def.params.is_empty() && self.visited_ops.insert(resolved.to_string()) {
                        return Some(walk_expr(self, &def.body.node));
                    }
                }
                Some(false)
            }
            _ => None,
        }
    }

    fn visit_apply(&mut self, op_expr: &Spanned<Expr>, args: &[Spanned<Expr>]) -> Option<bool> {
        if let Expr::Ident(name, _) = &op_expr.node {
            // FIX #1473: resolve through op_replacements before lookup
            let resolved = self.ctx.resolve_op_name(name.as_str());
            if let Some(def) = self.ctx.get_op(resolved) {
                if self.visited_ops.insert(resolved.to_string()) && walk_expr(self, &def.body.node)
                {
                    return Some(true);
                }
            }
        }
        Some(args.iter().any(|a| walk_expr(self, &a.node)))
    }
}

/// Check if an expression references any primed variables from the given set.
pub(crate) fn expr_references_primed_vars_v(
    ctx: &EvalCtx,
    expr: &Expr,
    vars: &FxHashSet<Arc<str>>,
) -> bool {
    if vars.is_empty() {
        return false;
    }
    walk_expr(
        &mut ExprReferencesPrimedVars {
            ctx,
            vars,
            visited_ops: FxHashSet::default(),
        },
        expr,
    )
}
