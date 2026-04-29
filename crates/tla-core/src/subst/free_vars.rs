// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Free variable collection for TLA+ expressions.
//!
//! Provides utilities for extracting bound variable names and computing
//! the set of free variables in an expression via AST traversal.

use crate::ast::{BoundPattern, BoundVar, Expr};
use crate::visit::{walk_expr, ExprVisitor};
use std::collections::HashSet;

use super::BoundNameStack;

/// Extract all bound names from a BoundVar (including pattern names).
///
/// A BoundVar can introduce multiple names when it has a tuple pattern:
/// - `x \in S` introduces just `x`
/// - `<<a, b>> \in S` introduces `a` and `b` (via pattern)
/// - `x = <<a, b>> \in S` introduces `x`, `a`, and `b`
pub(super) fn bound_names_from_bound_var(bound: &BoundVar) -> Vec<String> {
    let mut names = vec![bound.name.node.clone()];
    if let Some(pattern) = &bound.pattern {
        match pattern {
            BoundPattern::Var(v) => names.push(v.node.clone()),
            BoundPattern::Tuple(vs) => names.extend(vs.iter().map(|v| v.node.clone())),
        }
    }
    names
}

/// Collect free variables from an expression into a set.
///
/// This is the workhorse function that traverses the AST tracking bound
/// variables and collecting any identifiers that are not in scope.
fn collect_free_vars(expr: &Expr, bound: &mut BoundNameStack, free: &mut HashSet<String>) {
    let mut collector = FreeVarCollector { bound, free };
    walk_expr(&mut collector, expr);
}

struct FreeVarCollector<'a, 'b> {
    bound: &'a mut BoundNameStack,
    free: &'b mut HashSet<String>,
}

impl FreeVarCollector<'_, '_> {
    fn walk_quantifier_body(&mut self, bounds: &[BoundVar], body: &Expr) {
        for bound in bounds {
            if let Some(domain) = &bound.domain {
                walk_expr(self, &domain.node);
            }
        }
        let mark = self.bound.mark();
        self.bound
            .push_names(bounds.iter().flat_map(bound_names_from_bound_var));
        walk_expr(self, body);
        self.bound.pop_to(mark);
    }

    fn walk_single_bound_body(&mut self, bound_var: &BoundVar, body: &Expr) {
        if let Some(domain) = &bound_var.domain {
            walk_expr(self, &domain.node);
        }
        let mark = self.bound.mark();
        self.bound.push_names(bound_names_from_bound_var(bound_var));
        walk_expr(self, body);
        self.bound.pop_to(mark);
    }

    fn walk_let_body(&mut self, defs: &[crate::ast::OperatorDef], body: &Expr) {
        let mark = self.bound.mark();
        self.bound
            .push_names(defs.iter().map(|def| def.name.node.clone()));
        for def in defs {
            let def_mark = self.bound.mark();
            self.bound
                .push_names(def.params.iter().map(|param| param.name.node.clone()));
            walk_expr(self, &def.body.node);
            self.bound.pop_to(def_mark);
        }
        walk_expr(self, body);
        self.bound.pop_to(mark);
    }
}

impl ExprVisitor for FreeVarCollector<'_, '_> {
    type Output = ();

    fn visit_node(&mut self, expr: &Expr) -> Option<Self::Output> {
        match expr {
            Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
                if !self.bound.contains(name.as_str()) {
                    self.free.insert(name.clone());
                }
                Some(())
            }
            Expr::Forall(bounds, body)
            | Expr::Exists(bounds, body)
            | Expr::FuncDef(bounds, body) => {
                self.walk_quantifier_body(bounds, &body.node);
                Some(())
            }
            Expr::Choose(bound_var, body) | Expr::SetFilter(bound_var, body) => {
                self.walk_single_bound_body(bound_var, &body.node);
                Some(())
            }
            Expr::SetBuilder(body, bounds) => {
                self.walk_quantifier_body(bounds, &body.node);
                Some(())
            }
            Expr::Lambda(params, body) => {
                let mark = self.bound.mark();
                self.bound
                    .push_names(params.iter().map(|param| param.node.clone()));
                walk_expr(self, &body.node);
                self.bound.pop_to(mark);
                Some(())
            }
            Expr::Let(defs, body) => {
                self.walk_let_body(defs, &body.node);
                Some(())
            }
            _ => None,
        }
    }
}

/// Compute the set of free variables in an expression.
///
/// Returns all identifiers that appear unbound in the expression.
pub fn free_vars(expr: &Expr) -> HashSet<String> {
    let mut free = HashSet::new();
    let mut bound = BoundNameStack::default();
    collect_free_vars(expr, &mut bound, &mut free);
    free
}
