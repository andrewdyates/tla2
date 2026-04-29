// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Dropbox Apache-2.0.
//
// Simple boolean containment and guard visitors for expression analysis.

use crate::ast::Expr;
use crate::visit::{walk_expr, ExprVisitor};

/// Checks if an expression contains `Prime` and optionally `Unchanged`.
pub(crate) struct ContainsPrime {
    pub(crate) include_unchanged: bool,
}

impl ExprVisitor for ContainsPrime {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Prime(_) => Some(true),
            Expr::Unchanged(_) if self.include_unchanged => Some(true),
            // ENABLED is a state-level operator: primes inside are scoped to
            // the ENABLED and do not escape to the enclosing expression.
            // Without this, `Inner == ENABLED(x' = x + 1)` would be
            // classified as action-level, breaking OR short-circuit in the
            // enumeration (see #1640).
            Expr::Enabled(_) => Some(false),
            _ => None,
        }
    }
}

/// Checks for Prime OR Unchanged.
pub fn expr_contains_prime_v(expr: &Expr) -> bool {
    walk_expr(
        &mut ContainsPrime {
            include_unchanged: true,
        },
        expr,
    )
}

/// Checks for Prime only (not Unchanged).
pub fn expr_contains_any_prime_v(expr: &Expr) -> bool {
    walk_expr(
        &mut ContainsPrime {
            include_unchanged: false,
        },
        expr,
    )
}

/// Checks for Prime/Unchanged while preserving legacy helper behavior:
/// `InstanceExpr` substitutions are not traversed.
pub(crate) struct ContainsAnyPrimeLegacy;

impl ExprVisitor for ContainsAnyPrimeLegacy {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Prime(_) | Expr::Unchanged(_) => Some(true),
            Expr::InstanceExpr(_, _) => Some(false),
            _ => None,
        }
    }
}

/// Legacy prime detection with `InstanceExpr` short-circuit.
pub fn expr_has_any_prime_legacy_v(expr: &Expr) -> bool {
    walk_expr(&mut ContainsAnyPrimeLegacy, expr)
}

/// Checks if an expression contains temporal operators (`Always`, `Eventually`,
/// `LeadsTo`, `WeakFair`, `StrongFair`).
///
/// Used for config-time validation: TLC rejects invariants and constraints that
/// use temporal operators (level >= 2) because they cannot be evaluated in a
/// single-state or action context.
///
/// Part of #2573: TLC `SpecProcessor.java:1017-1027` level check.
pub(crate) struct ContainsTemporal;

impl ExprVisitor for ContainsTemporal {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Always(_)
            | Expr::Eventually(_)
            | Expr::LeadsTo(_, _)
            | Expr::WeakFair(_, _)
            | Expr::StrongFair(_, _) => Some(true),
            _ => None,
        }
    }
}

/// Check if an expression contains temporal operators.
pub fn expr_contains_temporal_v(expr: &Expr) -> bool {
    walk_expr(&mut ContainsTemporal, expr)
}

/// Checks whether an expression contains the `@` identifier (EXCEPT self-reference).
pub(crate) struct ContainsAt;

impl ExprVisitor for ContainsAt {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Ident(name, _) if name == "@" => Some(true),
            Expr::ModuleRef(_, _, _) | Expr::InstanceExpr(_, _) => Some(false),
            _ => None,
        }
    }
}

/// Check if an expression contains `@` (EXCEPT self-reference).
pub fn expr_contains_at_v(expr: &Expr) -> bool {
    walk_expr(&mut ContainsAt, expr)
}

/// Checks if an expression contains an `Exists` quantifier.
pub(crate) struct ContainsExists;

impl ExprVisitor for ContainsExists {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Exists(_, _) => Some(true),
            _ => None,
        }
    }
}

/// `expr_contains_exists` replacement.
pub fn expr_contains_exists_v(expr: &Expr) -> bool {
    walk_expr(&mut ContainsExists, expr)
}

/// Checks if an expression contains ENABLED at any nesting level.
pub(crate) struct ContainsEnabled;

impl ExprVisitor for ContainsEnabled {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Enabled(_) => Some(true),
            _ => None,
        }
    }
}

/// Check if an expression contains ENABLED at any nesting level.
pub fn expr_contains_enabled_v(expr: &Expr) -> bool {
    walk_expr(&mut ContainsEnabled, expr)
}

/// Checks if an expression contains an operator application.
pub(crate) struct ContainsOperatorApplication;

impl ExprVisitor for ContainsOperatorApplication {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Apply(_, _) => Some(true),
            _ => None,
        }
    }
}

/// `expr_contains_operator_application` replacement.
pub fn expr_contains_operator_application_v(expr: &Expr) -> bool {
    walk_expr(&mut ContainsOperatorApplication, expr)
}

/// Checks if an expression is a guard (contains no Prime or Unchanged).
pub(crate) struct IsGuardExpression;

impl ExprVisitor for IsGuardExpression {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Prime(_) | Expr::Unchanged(_) => Some(true),
            Expr::Let(_, body) => Some(walk_expr(self, &body.node)),
            _ => None,
        }
    }
}

/// Returns true if the expression contains no Prime or Unchanged nodes.
pub fn is_guard_expression_v(expr: &Expr) -> bool {
    !walk_expr(&mut IsGuardExpression, expr)
}
