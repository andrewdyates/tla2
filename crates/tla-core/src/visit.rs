// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Generic read-only expression visitor for TLA+ AST.
//!
//! `ExprVisitor` provides a default recursive traversal over all `Expr`
//! variants while letting callers intercept nodes (`visit_node`) or `Apply`
//! dispatch (`visit_apply`), and control lexical scope entry/exit.

use crate::ast::{BoundPattern, BoundVar, ExceptPathElement, Expr, ModuleTarget, OperatorDef};
use crate::span::Spanned;
use std::collections::HashSet;

/// Trait for combining visitor results across child nodes.
pub trait VisitorOutput: Default + Clone {
    fn combine(self, other: Self) -> Self;

    fn is_terminal(&self) -> bool {
        false
    }
}

impl VisitorOutput for () {
    fn combine(self, _other: Self) -> Self {}
}

impl VisitorOutput for bool {
    fn combine(self, other: Self) -> Self {
        self || other
    }

    fn is_terminal(&self) -> bool {
        *self
    }
}

impl<T: Eq + std::hash::Hash + Clone> VisitorOutput for HashSet<T> {
    fn combine(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

/// A generic expression visitor.
///
/// Override `visit_node` to intercept specific nodes before recursion. Return
/// `Some(result)` to short-circuit (skip children), or `None` to continue
/// default traversal.
pub trait ExprVisitor {
    type Output: VisitorOutput;

    /// Called on every node before recursion. Return `Some(result)` to
    /// short-circuit. Return `None` to recurse into children.
    fn visit_node(&mut self, _expr: &Expr) -> Option<Self::Output> {
        None
    }

    /// Called for `Apply` nodes. Override to follow operator definitions.
    /// Return `Some(result)` to replace default traversal, `None` for default.
    fn visit_apply(
        &mut self,
        _op_expr: &Spanned<Expr>,
        _args: &[Spanned<Expr>],
    ) -> Option<Self::Output> {
        None
    }

    /// Called when entering a binding scope (LET, quantifier, lambda).
    fn enter_scope(&mut self, _names: &[String]) {}

    /// Called when exiting a binding scope.
    fn exit_scope(&mut self, _names: &[String]) {}

    /// Whether a partial result means we can stop early.
    fn should_short_circuit(&self, partial: &Self::Output) -> bool {
        partial.is_terminal()
    }

    /// Default traversal over an expression tree.
    fn walk_expr(&mut self, expr: &Expr) -> Self::Output {
        // Pre-recursion interception
        if let Some(result) = self.visit_node(expr) {
            return result;
        }

        // Apply: check visitor override, then default traversal
        if let Expr::Apply(op, args) = expr {
            if let Some(result) = self.visit_apply(op, args) {
                return result;
            }
            let mut result = self.walk_expr(&op.node);
            for arg in args {
                if self.should_short_circuit(&result) {
                    return result;
                }
                result = result.combine(self.walk_expr(&arg.node));
            }
            return result;
        }

        match expr {
            // --- Terminals ---
            Expr::Ident(_, _)
            | Expr::StateVar(..)
            | Expr::Bool(_)
            | Expr::Int(_)
            | Expr::String(_)
            | Expr::OpRef(_) => Self::Output::default(),

            // --- Binary ---
            Expr::And(a, b)
            | Expr::Or(a, b)
            | Expr::Implies(a, b)
            | Expr::Equiv(a, b)
            | Expr::Eq(a, b)
            | Expr::Neq(a, b)
            | Expr::Lt(a, b)
            | Expr::Gt(a, b)
            | Expr::Leq(a, b)
            | Expr::Geq(a, b)
            | Expr::In(a, b)
            | Expr::NotIn(a, b)
            | Expr::Subseteq(a, b)
            | Expr::SetMinus(a, b)
            | Expr::Union(a, b)
            | Expr::Intersect(a, b)
            | Expr::Add(a, b)
            | Expr::Sub(a, b)
            | Expr::Mul(a, b)
            | Expr::Div(a, b)
            | Expr::IntDiv(a, b)
            | Expr::Mod(a, b)
            | Expr::Pow(a, b)
            | Expr::Range(a, b)
            | Expr::FuncApply(a, b)
            | Expr::FuncSet(a, b)
            | Expr::LeadsTo(a, b)
            | Expr::WeakFair(a, b)
            | Expr::StrongFair(a, b) => {
                let r1 = self.walk_expr(&a.node);
                if self.should_short_circuit(&r1) {
                    return r1;
                }
                r1.combine(self.walk_expr(&b.node))
            }

            // --- Unary ---
            Expr::Not(a)
            | Expr::Neg(a)
            | Expr::Prime(a)
            | Expr::Unchanged(a)
            | Expr::Enabled(a)
            | Expr::Always(a)
            | Expr::Eventually(a)
            | Expr::Domain(a)
            | Expr::Powerset(a)
            | Expr::BigUnion(a) => self.walk_expr(&a.node),

            // --- If-then-else ---
            Expr::If(c, t, e) => {
                let r1 = self.walk_expr(&c.node);
                if self.should_short_circuit(&r1) {
                    return r1;
                }
                let r2 = r1.combine(self.walk_expr(&t.node));
                if self.should_short_circuit(&r2) {
                    return r2;
                }
                r2.combine(self.walk_expr(&e.node))
            }

            // --- LET ... IN ... ---
            Expr::Let(defs, body) => {
                let names = let_def_names(defs);
                self.enter_scope(&names);
                let mut result = Self::Output::default();
                for def in defs {
                    result = result.combine(self.walk_expr(&def.body.node));
                    if self.should_short_circuit(&result) {
                        self.exit_scope(&names);
                        return result;
                    }
                }
                result = result.combine(self.walk_expr(&body.node));
                self.exit_scope(&names);
                result
            }

            // --- Forall/Exists ---
            // Domain expressions are walked BEFORE enter_scope so bound
            // variable names are not visible in their own domains (#2765).
            Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
                let names = bound_var_names(bounds);
                let mut result = Self::Output::default();
                for bv in bounds {
                    if let Some(dom) = &bv.domain {
                        result = result.combine(self.walk_expr(&dom.node));
                        if self.should_short_circuit(&result) {
                            return result;
                        }
                    }
                }
                self.enter_scope(&names);
                result = result.combine(self.walk_expr(&body.node));
                self.exit_scope(&names);
                result
            }

            // --- Choose ---
            Expr::Choose(bv, body) => {
                let names = single_bound_var_names(bv);
                let mut result = Self::Output::default();
                if let Some(dom) = &bv.domain {
                    result = self.walk_expr(&dom.node);
                    if self.should_short_circuit(&result) {
                        return result;
                    }
                }
                self.enter_scope(&names);
                result = result.combine(self.walk_expr(&body.node));
                self.exit_scope(&names);
                result
            }

            // --- Collections ---
            Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
                self.walk_children(elems)
            }

            // --- Set builders with scope ---
            Expr::SetBuilder(expr, bounds) => {
                let names = bound_var_names(bounds);
                let mut result = Self::Output::default();
                for bv in bounds {
                    if let Some(dom) = &bv.domain {
                        result = result.combine(self.walk_expr(&dom.node));
                        if self.should_short_circuit(&result) {
                            return result;
                        }
                    }
                }
                self.enter_scope(&names);
                result = result.combine(self.walk_expr(&expr.node));
                self.exit_scope(&names);
                result
            }

            Expr::FuncDef(bounds, expr) => {
                let names = bound_var_names(bounds);
                let mut result = Self::Output::default();
                for bv in bounds {
                    if let Some(dom) = &bv.domain {
                        result = result.combine(self.walk_expr(&dom.node));
                        if self.should_short_circuit(&result) {
                            return result;
                        }
                    }
                }
                self.enter_scope(&names);
                result = result.combine(self.walk_expr(&expr.node));
                self.exit_scope(&names);
                result
            }

            Expr::SetFilter(bv, body) => {
                let names = single_bound_var_names(bv);
                let mut result = Self::Output::default();
                if let Some(dom) = &bv.domain {
                    result = self.walk_expr(&dom.node);
                    if self.should_short_circuit(&result) {
                        return result;
                    }
                }
                self.enter_scope(&names);
                result = result.combine(self.walk_expr(&body.node));
                self.exit_scope(&names);
                result
            }

            // --- Records ---
            Expr::Record(fields) | Expr::RecordSet(fields) => {
                let mut result = Self::Output::default();
                for (_, val) in fields {
                    result = result.combine(self.walk_expr(&val.node));
                    if self.should_short_circuit(&result) {
                        return result;
                    }
                }
                result
            }

            Expr::RecordAccess(expr, _field) => self.walk_expr(&expr.node),

            // --- Except ---
            Expr::Except(base, specs) => {
                let mut result = self.walk_expr(&base.node);
                if self.should_short_circuit(&result) {
                    return result;
                }
                for spec in specs {
                    for path_elem in &spec.path {
                        if let ExceptPathElement::Index(idx) = path_elem {
                            result = result.combine(self.walk_expr(&idx.node));
                            if self.should_short_circuit(&result) {
                                return result;
                            }
                        }
                    }
                    result = result.combine(self.walk_expr(&spec.value.node));
                    if self.should_short_circuit(&result) {
                        return result;
                    }
                }
                result
            }

            // --- Case ---
            Expr::Case(arms, other) => {
                let mut result = Self::Output::default();
                for arm in arms {
                    result = result.combine(self.walk_expr(&arm.guard.node));
                    if self.should_short_circuit(&result) {
                        return result;
                    }
                    result = result.combine(self.walk_expr(&arm.body.node));
                    if self.should_short_circuit(&result) {
                        return result;
                    }
                }
                if let Some(other_expr) = other {
                    result = result.combine(self.walk_expr(&other_expr.node));
                }
                result
            }
            Expr::Label(label) => self.walk_expr(&label.body.node),

            // --- Module references ---
            Expr::ModuleRef(target, _name, args) => {
                let mut result = match target {
                    ModuleTarget::Parameterized(_, params) => {
                        let mut r = Self::Output::default();
                        for p in params {
                            r = r.combine(self.walk_expr(&p.node));
                            if self.should_short_circuit(&r) {
                                return r;
                            }
                        }
                        r
                    }
                    ModuleTarget::Chained(base) => self.walk_expr(&base.node),
                    ModuleTarget::Named(_) => Self::Output::default(),
                };
                if !self.should_short_circuit(&result) {
                    result = result.combine(self.walk_children(args));
                }
                result
            }
            Expr::InstanceExpr(_name, subs) => {
                let mut result = Self::Output::default();
                for sub in subs {
                    result = result.combine(self.walk_expr(&sub.to.node));
                    if self.should_short_circuit(&result) {
                        return result;
                    }
                }
                result
            }
            Expr::SubstIn(subs, body) => {
                let mut result = Self::Output::default();
                for sub in subs {
                    result = result.combine(self.walk_expr(&sub.to.node));
                    if self.should_short_circuit(&result) {
                        return result;
                    }
                }
                result.combine(self.walk_expr(&body.node))
            }

            // --- Lambda ---
            Expr::Lambda(params, body) => {
                let names: Vec<String> = params.iter().map(|p| p.node.clone()).collect();
                self.enter_scope(&names);
                let r = self.walk_expr(&body.node);
                self.exit_scope(&names);
                r
            }

            Expr::Apply(..) => unreachable!(), // handled above
        }
    }

    /// Traverse a sequence of child expressions and combine their outputs.
    fn walk_children(&mut self, elems: &[Spanned<Expr>]) -> Self::Output {
        let mut result = Self::Output::default();
        for e in elems {
            result = result.combine(self.walk_expr(&e.node));
            if self.should_short_circuit(&result) {
                return result;
            }
        }
        result
    }
}

/// Walk an expression tree with the given visitor.
pub fn walk_expr<V: ExprVisitor>(visitor: &mut V, expr: &Expr) -> V::Output {
    visitor.walk_expr(expr)
}

/// Convenience: walk a `Spanned<Expr>`.
pub fn walk_spanned_expr<V: ExprVisitor>(visitor: &mut V, expr: &Spanned<Expr>) -> V::Output {
    visitor.walk_expr(&expr.node)
}

/// Extract all names introduced by a slice of `BoundVar`s.
pub(crate) fn bound_var_names(bounds: &[BoundVar]) -> Vec<String> {
    bounds.iter().flat_map(single_bound_var_names).collect()
}

/// Extract names from a single `BoundVar`.
pub fn single_bound_var_names(bv: &BoundVar) -> Vec<String> {
    match &bv.pattern {
        Some(BoundPattern::Tuple(names)) => names.iter().map(|n| n.node.clone()).collect(),
        Some(BoundPattern::Var(name)) => vec![name.node.clone()],
        None => vec![bv.name.node.clone()],
    }
}

/// Extract definition names from LET bindings.
fn let_def_names(defs: &[OperatorDef]) -> Vec<String> {
    defs.iter().map(|d| d.name.node.clone()).collect()
}
