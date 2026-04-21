// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates Apache-2.0.
//
// Binding-aware ExprVisitor implementations.
// These visitors need to track variable shadowing through binding constructs
// (Forall, Exists, Let, Choose, SetFilter, FuncDef, SetBuilder).

use std::collections::HashSet;
use std::sync::Arc;

use crate::ast::{BoundPattern, BoundVar, Expr};
use crate::visit::{walk_expr, ExprVisitor};
use crate::Spanned;

use super::expr_contains_any_prime_v;

// ============================================================
// Binding scope helpers
// ============================================================

/// Check binding domains for matches, then check body only if param is not shadowed.
/// Returns `Some(result)` with the combined domain + body check.
fn check_multi_bound_scope<V: ExprVisitor<Output = bool>>(
    visitor: &mut V,
    bounds: &[BoundVar],
    body: &Spanned<Expr>,
    shadowed_name: &str,
) -> Option<bool> {
    let mut result = false;
    for bound in bounds {
        if let Some(domain) = &bound.domain {
            result = result || walk_expr(visitor, &domain.node);
            if result {
                return Some(true);
            }
        }
    }
    if bounds.iter().any(|b| b.name.node == shadowed_name) {
        Some(result)
    } else {
        Some(result || walk_expr(visitor, &body.node))
    }
}

/// Check single-bound scope (Choose, SetFilter).
fn check_single_bound_scope<V: ExprVisitor<Output = bool>>(
    visitor: &mut V,
    bound: &BoundVar,
    body: &Spanned<Expr>,
    shadowed_name: &str,
) -> Option<bool> {
    let mut result = false;
    if let Some(domain) = &bound.domain {
        result = walk_expr(visitor, &domain.node);
        if result {
            return Some(true);
        }
    }
    if bound.name.node == shadowed_name {
        Some(result)
    } else {
        Some(result || walk_expr(visitor, &body.node))
    }
}

// ============================================================
// ContainsPrimedParam
// ============================================================

/// Checks whether an expression contains `param_name'`, preserving legacy
/// shadowing behavior from `eval::helpers::expr_has_primed_param`.
pub(crate) struct ContainsPrimedParam<'a> {
    pub(crate) param_name: &'a str,
}

impl ExprVisitor for ContainsPrimedParam<'_> {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Prime(inner) => {
                if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &inner.node {
                    if name == self.param_name {
                        return Some(true);
                    }
                }
                None
            }
            Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
                check_multi_bound_scope(self, bounds, body, self.param_name)
            }
            Expr::SetBuilder(elem, bounds) => {
                check_multi_bound_scope(self, bounds, elem, self.param_name)
            }
            Expr::FuncDef(bounds, body) => {
                check_multi_bound_scope(self, bounds, body, self.param_name)
            }
            Expr::Choose(bound, pred) => {
                check_single_bound_scope(self, bound, pred, self.param_name)
            }
            Expr::SetFilter(bound, pred) => {
                check_single_bound_scope(self, bound, pred, self.param_name)
            }
            Expr::Let(defs, body) => {
                let mut result = false;
                for def in defs {
                    result = result || walk_expr(self, &def.body.node);
                    if result {
                        return Some(true);
                    }
                }
                if defs.iter().any(|d| d.name.node == self.param_name) {
                    Some(result)
                } else {
                    Some(result || walk_expr(self, &body.node))
                }
            }
            Expr::InstanceExpr(_, _) => Some(false),
            _ => None,
        }
    }
}

/// `eval::helpers::expr_has_primed_param` replacement.
pub fn expr_contains_primed_param_v(expr: &Expr, param_name: &str) -> bool {
    walk_expr(&mut ContainsPrimedParam { param_name }, expr)
}

// ============================================================
// CollectBoundNames
// ============================================================

/// Collects all bound variable names from binding constructs.
pub(crate) struct CollectBoundNames {
    pub(crate) names: HashSet<String>,
}

impl ExprVisitor for CollectBoundNames {
    type Output = HashSet<String>;

    fn visit_node(&mut self, expr: &Expr) -> Option<HashSet<String>> {
        match expr {
            Expr::Forall(bounds, _)
            | Expr::Exists(bounds, _)
            | Expr::SetBuilder(_, bounds)
            | Expr::FuncDef(bounds, _) => {
                for bv in bounds {
                    self.names.insert(bv.name.node.clone());
                }
                None
            }
            Expr::Choose(bv, _) | Expr::SetFilter(bv, _) => {
                self.names.insert(bv.name.node.clone());
                None
            }
            Expr::Let(defs, _) => {
                for def in defs {
                    self.names.insert(def.name.node.clone());
                    for p in &def.params {
                        self.names.insert(p.name.node.clone());
                    }
                }
                None
            }
            Expr::Lambda(params, _) => {
                for p in params {
                    self.names.insert(p.node.clone());
                }
                None
            }
            _ => None,
        }
    }
}

/// `collect_bound_names` replacement.
pub fn collect_bound_names_v(expr: &Expr) -> HashSet<String> {
    let mut visitor = CollectBoundNames {
        names: HashSet::new(),
    };
    let _ = walk_expr(&mut visitor, expr);
    visitor.names
}

// ============================================================
// CollectPrimedVarRefs
// ============================================================

/// Collects primed variable names referenced in an expression.
pub(crate) struct CollectPrimedVarRefs {
    pub(crate) refs: HashSet<Arc<str>>,
}

impl ExprVisitor for CollectPrimedVarRefs {
    type Output = HashSet<Arc<str>>;

    fn visit_node(&mut self, expr: &Expr) -> Option<HashSet<Arc<str>>> {
        if let Expr::Prime(inner) = expr {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &inner.node {
                self.refs.insert(Arc::from(name.as_str()));
            }
            None
        } else {
            None
        }
    }
}

/// `get_primed_var_refs` replacement.
pub fn get_primed_var_refs_v(expr: &Expr) -> HashSet<Arc<str>> {
    let mut visitor = CollectPrimedVarRefs {
        refs: HashSet::new(),
    };
    let _ = walk_expr(&mut visitor, expr);
    visitor.refs
}

// ============================================================
// ContainsPrimeNotAssignment
// ============================================================

/// Returns true if `lhs` is a simple primed variable: `x'` where x is Ident or StateVar.
pub fn is_simple_prime_var(lhs: &Expr) -> bool {
    matches!(
        lhs,
        Expr::Prime(inner) if matches!(&inner.node, Expr::Ident(_, _) | Expr::StateVar(_, _, _))
    )
}

/// Checks for Prime nodes, but skips simple prime assignments.
pub(crate) struct ContainsPrimeNotAssignment;

impl ExprVisitor for ContainsPrimeNotAssignment {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Prime(_) => Some(true),
            Expr::InstanceExpr(_, _) => Some(false),
            Expr::Eq(lhs, rhs) | Expr::In(lhs, rhs) => {
                let lhs_result = if is_simple_prime_var(&lhs.node) {
                    false
                } else {
                    walk_expr(self, &lhs.node)
                };
                Some(lhs_result || walk_expr(self, &rhs.node))
            }
            Expr::Implies(a, b) => {
                Some(expr_contains_any_prime_v(&a.node) || walk_expr(self, &b.node))
            }
            Expr::Except(base, specs) => {
                let mut result = walk_expr(self, &base.node);
                if result {
                    return Some(true);
                }
                for spec in specs {
                    result = result || walk_expr(self, &spec.value.node);
                    if result {
                        return Some(true);
                    }
                }
                Some(result)
            }
            _ => None,
        }
    }
}

/// `expr_contains_prime_not_assignment` replacement.
pub fn expr_contains_prime_not_assignment_v(expr: &Expr) -> bool {
    walk_expr(&mut ContainsPrimeNotAssignment, expr)
}

// ============================================================
// ReferencesAnyFreeName
// ============================================================

/// Checks whether an expression references any name from a given set as a free
/// variable — i.e., not shadowed by an intervening binding construct (Forall,
/// Exists, Choose, SetFilter, SetBuilder, FuncDef, Let, Lambda).
///
/// Unlike `ContainsFreeVarInSet` (which conservatively returns `true` for any
/// binding construct), this visitor precisely tracks shadowing by temporarily
/// narrowing the target set at each binding boundary.
///
/// Part of #3128: Used by quantifier subexpression hoisting to determine which
/// body subtrees are bound-variable-invariant and can be cached across iterations.
pub(crate) struct ReferencesAnyFreeName {
    pub(crate) names: HashSet<String>,
}

impl ExprVisitor for ReferencesAnyFreeName {
    type Output = bool;

    fn visit_node(&mut self, expr: &Expr) -> Option<bool> {
        match expr {
            Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
                Some(self.names.contains(name.as_str()))
            }
            Expr::Forall(bounds, body)
            | Expr::Exists(bounds, body)
            | Expr::SetBuilder(body, bounds)
            | Expr::FuncDef(bounds, body) => {
                let mut result = false;
                for b in bounds {
                    if let Some(domain) = &b.domain {
                        result = result || walk_expr(self, &domain.node);
                        if result {
                            return Some(true);
                        }
                    }
                }
                let removed = self.remove_bound_names_multi(bounds);
                if !self.names.is_empty() {
                    result = result || walk_expr(self, &body.node);
                }
                self.restore_names(&removed);
                Some(result)
            }
            Expr::Choose(bound, pred) | Expr::SetFilter(bound, pred) => {
                let mut result = false;
                if let Some(domain) = &bound.domain {
                    result = walk_expr(self, &domain.node);
                    if result {
                        return Some(true);
                    }
                }
                let removed = self.remove_bound_names_single(bound);
                if !self.names.is_empty() {
                    result = result || walk_expr(self, &pred.node);
                }
                self.restore_names(&removed);
                Some(result)
            }
            Expr::Let(defs, body) => Some(self.check_let_scope(defs, body)),
            Expr::Lambda(params, body) => Some(self.check_lambda_scope(params, body)),
            Expr::InstanceExpr(_, _) => Some(false),
            _ => None,
        }
    }
}

impl ReferencesAnyFreeName {
    /// Check LET scope: def params shadow within def bodies, def names shadow in body.
    fn check_let_scope(&mut self, defs: &[crate::ast::OperatorDef], body: &Spanned<Expr>) -> bool {
        let mut result = false;
        for def in defs {
            let param_removed = self.remove_op_param_names(&def.params);
            result = result || walk_expr(self, &def.body.node);
            self.restore_names(&param_removed);
            if result {
                return true;
            }
        }
        let removed = self.remove_def_names(defs);
        if !self.names.is_empty() {
            result = result || walk_expr(self, &body.node);
        }
        self.restore_names(&removed);
        result
    }

    /// Check Lambda scope: params shadow in body.
    fn check_lambda_scope(&mut self, params: &[Spanned<String>], body: &Spanned<Expr>) -> bool {
        let removed = self.remove_spanned_names(params);
        let result = if !self.names.is_empty() {
            walk_expr(self, &body.node)
        } else {
            false
        };
        self.restore_names(&removed);
        result
    }

    /// Remove bound variable names from the target set, returning the removed
    /// names for later restoration.
    fn remove_bound_names_multi(&mut self, bounds: &[BoundVar]) -> Vec<String> {
        let mut removed = Vec::new();
        for b in bounds {
            if self.names.remove(&b.name.node) {
                removed.push(b.name.node.clone());
            }
            if let Some(BoundPattern::Tuple(vars)) = &b.pattern {
                for v in vars {
                    if self.names.remove(&v.node) {
                        removed.push(v.node.clone());
                    }
                }
            } else if let Some(BoundPattern::Var(v)) = &b.pattern {
                if self.names.remove(&v.node) {
                    removed.push(v.node.clone());
                }
            }
        }
        removed
    }

    fn remove_bound_names_single(&mut self, bound: &BoundVar) -> Vec<String> {
        let mut removed = Vec::new();
        if self.names.remove(&bound.name.node) {
            removed.push(bound.name.node.clone());
        }
        if let Some(BoundPattern::Tuple(vars)) = &bound.pattern {
            for v in vars {
                if self.names.remove(&v.node) {
                    removed.push(v.node.clone());
                }
            }
        } else if let Some(BoundPattern::Var(v)) = &bound.pattern {
            if self.names.remove(&v.node) {
                removed.push(v.node.clone());
            }
        }
        removed
    }

    fn remove_op_param_names(&mut self, params: &[crate::ast::OpParam]) -> Vec<String> {
        let mut removed = Vec::new();
        for p in params {
            if self.names.remove(&p.name.node) {
                removed.push(p.name.node.clone());
            }
        }
        removed
    }

    fn remove_def_names(&mut self, defs: &[crate::ast::OperatorDef]) -> Vec<String> {
        let mut removed = Vec::new();
        for d in defs {
            if self.names.remove(&d.name.node) {
                removed.push(d.name.node.clone());
            }
        }
        removed
    }

    fn remove_spanned_names(&mut self, names: &[Spanned<String>]) -> Vec<String> {
        let mut removed = Vec::new();
        for n in names {
            if self.names.remove(&n.node) {
                removed.push(n.node.clone());
            }
        }
        removed
    }

    fn restore_names(&mut self, removed: &[String]) {
        for name in removed {
            self.names.insert(name.clone());
        }
    }
}

/// Check if an expression references any name from the given set as a free
/// variable, correctly handling binding scope (shadowing).
///
/// Short-circuits on first match (O(n) in AST size, early exit).
/// Part of #3128: Precise alternative to `expr_has_free_var_in_set_v`.
pub fn expr_references_any_free_name_v(expr: &Expr, names: &HashSet<&str>) -> bool {
    if names.is_empty() {
        return false;
    }
    let owned: HashSet<String> = names.iter().map(|s| (*s).to_string()).collect();
    walk_expr(&mut ReferencesAnyFreeName { names: owned }, expr)
}
