// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Dropbox Apache-2.0.
//
// Name/identifier visitors for expression analysis.

use std::collections::HashSet;
use std::sync::Arc;

use crate::ast::Expr;
use crate::visit::{walk_expr, walk_spanned_expr, ExprVisitor};
use crate::Spanned;

/// Checks if an expression contains a specific identifier (Ident or StateVar only).
pub(crate) struct ContainsIdent<'a> {
    pub(crate) name: &'a str,
}

impl ExprVisitor for ContainsIdent<'_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Ident(n, _) if n == self.name => Some(true),
            Expr::StateVar(n, _, _) if n == self.name => Some(true),
            _ => None,
        }
    }
}

/// Check if an expression mentions a name as `Ident` or `StateVar`.
pub fn expr_mentions_name_v(expr: &Expr, name: &str) -> bool {
    walk_expr(&mut ContainsIdent { name }, expr)
}

/// Spanned variant of `expr_mentions_name_v`.
pub fn expr_mentions_name_spanned_v(expr: &Spanned<Expr>, name: &str) -> bool {
    walk_spanned_expr(&mut ContainsIdent { name }, expr)
}

/// Also checks bound variable names, LET definitions, and Lambda params.
pub(crate) struct ContainsIdentIncludingBindings<'a> {
    pub(crate) name: &'a str,
}

impl ExprVisitor for ContainsIdentIncludingBindings<'_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Ident(n, _) if n == self.name => Some(true),
            Expr::StateVar(n, _, _) if n == self.name => Some(true),
            Expr::Forall(bounds, _)
            | Expr::Exists(bounds, _)
            | Expr::SetBuilder(_, bounds)
            | Expr::FuncDef(bounds, _) => {
                if bounds.iter().any(|bv| bv.name.node == self.name) {
                    return Some(true);
                }
                None
            }
            Expr::Choose(bv, _) | Expr::SetFilter(bv, _) => {
                if bv.name.node == self.name {
                    return Some(true);
                }
                None
            }
            Expr::Let(defs, _) => {
                for def in defs {
                    if def.name.node == self.name {
                        return Some(true);
                    }
                    if def.params.iter().any(|p| p.name.node == self.name) {
                        return Some(true);
                    }
                }
                None
            }
            Expr::Lambda(params, _) => {
                if params.iter().any(|p| p.node == self.name) {
                    return Some(true);
                }
                None
            }
            Expr::InstanceExpr(_, _) => Some(false),
            _ => None,
        }
    }
}

/// `expr_contains_ident` replacement.
pub fn expr_contains_ident_v(expr: &Expr, name: &str) -> bool {
    walk_expr(&mut ContainsIdentIncludingBindings { name }, expr)
}

/// Checks if a free variable from `var_set` appears in an expression.
pub(crate) struct ContainsFreeVarInSet<'a, 'b> {
    pub(crate) var_set: &'a HashSet<&'b str>,
}

impl ExprVisitor for ContainsFreeVarInSet<'_, '_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
                Some(self.var_set.contains(name.as_str()))
            }
            Expr::Forall(_, _)
            | Expr::Exists(_, _)
            | Expr::Choose(_, _)
            | Expr::SetBuilder(_, _)
            | Expr::SetFilter(_, _)
            | Expr::FuncDef(_, _)
            | Expr::Let(_, _)
            | Expr::Lambda(_, _) => Some(true),
            Expr::InstanceExpr(_, _) => Some(false),
            _ => None,
        }
    }
}

/// `expr_has_free_var_in_set` replacement.
pub fn expr_has_free_var_in_set_v(expr: &Expr, var_set: &HashSet<&str>) -> bool {
    walk_expr(&mut ContainsFreeVarInSet { var_set }, expr)
}

/// Checks if any identifier appears in the given name set.
pub(crate) struct ArgHasNameInSet<'a> {
    pub(crate) names: &'a HashSet<String>,
}

impl ExprVisitor for ArgHasNameInSet<'_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
                Some(self.names.contains(name.as_str()))
            }
            Expr::OpRef(name) => Some(self.names.contains(name.as_str())),
            _ => None,
        }
    }
}

/// `arg_has_name_in_set` replacement.
pub fn arg_has_name_in_set_v(expr: &Expr, names: &HashSet<String>) -> bool {
    walk_expr(&mut ArgHasNameInSet { names }, expr)
}

/// Checks if an expression references state variables from a given list.
pub(crate) struct ReferencesStateVars<'a> {
    pub(crate) vars: &'a [Arc<str>],
}

impl ExprVisitor for ReferencesStateVars<'_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
                if self.vars.iter().any(|v| v.as_ref() == name.as_str()) {
                    Some(true)
                } else {
                    Some(false)
                }
            }
            Expr::Prime(_) => Some(false),
            _ => None,
        }
    }
}

/// `expr_references_state_vars` replacement.
pub fn expr_references_state_vars_v(expr: &Expr, vars: &[Arc<str>]) -> bool {
    walk_expr(&mut ReferencesStateVars { vars }, expr)
}
