// Author: Andrew Yates
// Copyright 2026 Andrew Yates. Apache-2.0.
//
// Context-aware visitors used by guard/prime-binding analysis.

use tla_core::ast::{Expr, ModuleTarget};
use tla_core::Spanned;

use super::super::visitors_simple::{expr_contains_prime_v, is_simple_prime_var};
use super::super::{walk_expr, ExprVisitor};
use crate::eval::EvalCtx;

/// Checks if an expression might need prime bindings because it references
/// operators that contain primed variables (based on `contains_prime` and
/// `guards_depend_on_prime` fields computed during semantic analysis).
///
/// Special cases:
/// - `Eq(a, b)`: if LHS is `x'`, only check RHS (assignment, not predicate)
/// - `In(a, b)`: if LHS is `x'`, only check RHS (membership assignment)
/// - `ModuleRef`: conservative true
/// - `Ident`/`Apply`: check operator metadata (skipped when `skip_prime_validation`)
///
/// Replaces hand-written `might_need_prime_binding` in enumerate/expr_analysis.rs.
/// Part of #1192 Wave 2.
pub(crate) struct MightNeedPrimeBinding<'a> {
    ctx: &'a EvalCtx,
}

impl ExprVisitor for MightNeedPrimeBinding<'_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Prime(_) => Some(true),

            // ENABLED is state-level: primes inside are scoped (#1654).
            Expr::Enabled(_) => Some(false),

            Expr::Ident(name, _) => {
                if self.ctx.skip_prime_validation() {
                    Some(false)
                } else {
                    // FIX #1473: resolve through op_replacements before lookup
                    let resolved = self.ctx.resolve_op_name(name.as_str());
                    Some(
                        self.ctx
                            .get_op(resolved)
                            .is_some_and(|def| def.guards_depend_on_prime || def.contains_prime),
                    )
                }
            }

            Expr::ModuleRef(_, _, _) => Some(true),

            // Assignment: x' = expr — skip LHS prime, only check RHS
            Expr::Eq(a, b) => {
                let lhs_is_simple_prime = is_simple_prime_var(&a.node);
                let rhs_is_simple_prime = is_simple_prime_var(&b.node);
                if lhs_is_simple_prime {
                    Some(walk_expr(self, &b.node))
                } else if rhs_is_simple_prime {
                    Some(walk_expr(self, &a.node))
                } else {
                    None // default traversal
                }
            }

            // Membership assignment: x' \in S — skip LHS prime, only check RHS
            Expr::In(a, b) => {
                let lhs_is_simple_prime = is_simple_prime_var(&a.node);
                if lhs_is_simple_prime {
                    Some(walk_expr(self, &b.node))
                } else {
                    None // default traversal
                }
            }

            // Literals and simple values - no prime binding needed
            Expr::Bool(_)
            | Expr::Int(_)
            | Expr::String(_)
            | Expr::OpRef(_)
            | Expr::StateVar(_, _, _)
            | Expr::InstanceExpr(_, _) => Some(false),

            _ => None, // default traversal for all other compound expressions
        }
    }

    fn visit_apply(&mut self, op_expr: &Spanned<Expr>, args: &[Spanned<Expr>]) -> Option<bool> {
        let op_guards_depend = if self.ctx.skip_prime_validation() {
            false
        } else if let Expr::Ident(op_name, _) = &op_expr.node {
            // FIX #1473: resolve through op_replacements before lookup
            let resolved = self.ctx.resolve_op_name(op_name.as_str());
            self.ctx
                .get_op(resolved)
                .is_some_and(|def| def.guards_depend_on_prime || def.contains_prime)
        } else {
            walk_expr(self, &op_expr.node)
        };
        if op_guards_depend {
            return Some(true);
        }
        Some(args.iter().any(|arg| walk_expr(self, &arg.node)))
    }
}

/// Check if an expression might need prime bindings.
pub(crate) fn might_need_prime_binding_v(ctx: &EvalCtx, expr: &Expr) -> bool {
    walk_expr(&mut MightNeedPrimeBinding { ctx }, expr)
}

/// Checks if an expression contains an operator reference that could hide
/// action-level content, making it unsafe to evaluate during guard short-circuiting.
///
/// Key behaviors:
/// - `ModuleRef`: resolves instance, checks if operator contains primes
/// - `Ident`: resolves op, checks `contains_prime || expr_contains_prime(body)`
/// - `Apply`: checks op + recurses into args
/// - All compound expressions: standard recursion
///
/// Replaces hand-written `is_operator_reference_guard_unsafe` in enumerate/expr_analysis.rs.
/// Part of #1192 Wave 2.
pub(crate) struct IsOperatorReferenceGuardUnsafe<'a> {
    ctx: &'a EvalCtx,
}

impl ExprVisitor for IsOperatorReferenceGuardUnsafe<'_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::ModuleRef(target, op_name, args) => {
                // Check arguments first
                if args.iter().any(|arg| walk_expr(self, &arg.node)) {
                    return Some(true);
                }

                let instance_name = target.name();

                // Handle chained references conservatively
                if matches!(target, ModuleTarget::Chained(_)) {
                    return Some(true);
                }

                // Try to resolve the module name for this instance
                let module_name: Option<String> =
                    if let Some(info) = self.ctx.get_instance(instance_name) {
                        Some(info.module_name.clone())
                    } else if let Some(def) = self.ctx.get_op(instance_name) {
                        if let Expr::InstanceExpr(module, _) = &def.body.node {
                            Some(module.clone())
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                // Look up the operator in the module and check for primes
                if let Some(mod_name) = module_name {
                    if let Some(op_def) = self.ctx.get_instance_op(&mod_name, op_name) {
                        return Some(
                            op_def.contains_prime || expr_contains_prime_v(&op_def.body.node),
                        );
                    }
                }

                // Can't resolve - be conservative
                Some(true)
            }

            Expr::Ident(name, _) => {
                let resolved = self.ctx.resolve_op_name(name.as_str());
                Some(
                    self.ctx.get_op(resolved).is_some_and(|def| {
                        def.contains_prime || expr_contains_prime_v(&def.body.node)
                    }),
                )
            }

            // Simple terminals
            Expr::Bool(_)
            | Expr::Int(_)
            | Expr::String(_)
            | Expr::OpRef(_)
            | Expr::StateVar(_, _, _)
            | Expr::InstanceExpr(_, _)
            | Expr::Prime(_)
            | Expr::Unchanged(_)
            | Expr::Enabled(_) => Some(false),

            _ => None, // default traversal for compound expressions
        }
    }

    fn visit_apply(&mut self, op_expr: &Spanned<Expr>, args: &[Spanned<Expr>]) -> Option<bool> {
        // Check operator itself
        let op_unsafe = match &op_expr.node {
            Expr::Ident(op_name, _) => {
                let resolved = self.ctx.resolve_op_name(op_name.as_str());
                self.ctx
                    .get_op(resolved)
                    .is_some_and(|def| def.contains_prime || expr_contains_prime_v(&def.body.node))
            }
            _ => walk_expr(self, &op_expr.node),
        };
        if op_unsafe {
            return Some(true);
        }
        // Check arguments recursively
        Some(args.iter().any(|arg| walk_expr(self, &arg.node)))
    }
}

/// Check if an expression contains an operator reference that could hide action-level content.
pub(crate) fn is_operator_reference_guard_unsafe_v(ctx: &EvalCtx, expr: &Expr) -> bool {
    walk_expr(&mut IsOperatorReferenceGuardUnsafe { ctx }, expr)
}
