// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recursive operator detection for TLA+ AST (#2944).
//!
//! Sets `is_recursive = true` on operators declared with `RECURSIVE`, enabling
//! cache bypass optimizations where cache hits are structurally impossible
//! within a recursion chain (#3008).

use crate::ast::{Expr, Module, Unit};
use crate::name_intern::NameId;
use crate::ExprVisitor;

/// Compute `is_recursive` for all operators in a module (#2944).
///
/// Collects names from `Unit::Recursive` forward declarations, then sets
/// `is_recursive = true` on matching `OperatorDef`s. Also handles RECURSIVE
/// inside LET expressions by checking if any LET-bound def references itself.
///
/// Must be called after lowering.
pub fn compute_is_recursive(module: &mut Module) {
    use std::collections::HashSet;

    // Collect all RECURSIVE forward declaration names at module level
    let mut recursive_names: HashSet<String> = HashSet::new();
    for unit in &module.units {
        if let Unit::Recursive(decls) = &unit.node {
            for decl in decls {
                recursive_names.insert(decl.name.node.clone());
            }
        }
    }

    // Set is_recursive and self_call_count on matching operator definitions
    for unit in &mut module.units {
        if let Unit::Operator(def) = &mut unit.node {
            if recursive_names.contains(&def.name.node) {
                def.is_recursive = true;
                def.self_call_count = count_self_references(&def.body.node, &def.name.node);
            }
            // Also handle RECURSIVE inside LET expressions
            mark_recursive_in_expr(&mut def.body.node);
        }
    }
}

/// Count how many times an expression references a given identifier name (#3008).
/// Used to distinguish single-recursion (count=1, bypass cache) from double-recursion
/// (count>1, keep cache for O(2^n)→O(n) memoization).
fn count_self_references(expr: &Expr, name: &str) -> u32 {
    struct CountRefs<'a> {
        name: &'a str,
        count: u32,
    }
    impl ExprVisitor for CountRefs<'_> {
        type Output = ();
        fn visit_node(&mut self, expr: &Expr) -> Option<()> {
            match expr {
                Expr::Ident(n, NameId::INVALID) | Expr::StateVar(n, _, _) if n == self.name => {
                    self.count += 1;
                    None // continue walking (don't short-circuit)
                }
                _ => None,
            }
        }
    }
    let mut counter = CountRefs { name, count: 0 };
    counter.walk_expr(expr);
    counter.count
}

/// Walk expression tree, marking LET-bound operators that reference their own name.
/// Delegates child traversal to `for_each_child_expr_mut`.
fn mark_recursive_in_expr(expr: &mut Expr) {
    if let Expr::Let(defs, body) = expr {
        for def in defs.iter_mut() {
            let count = count_self_references(&def.body.node, &def.name.node);
            if count > 0 {
                def.is_recursive = true;
                def.self_call_count = count;
            }
            mark_recursive_in_expr(&mut def.body.node);
        }
        mark_recursive_in_expr(&mut body.node);
    } else {
        for_each_child_expr_mut(expr, mark_recursive_in_expr);
    }
}

/// Apply a function to each direct child expression (one level deep).
/// Compact format to stay within function size limits.
#[rustfmt::skip]
fn for_each_child_expr_mut(expr: &mut Expr, mut f: impl FnMut(&mut Expr)) {
    match expr {
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b) | Expr::Equiv(a, b)
        | Expr::Eq(a, b) | Expr::Neq(a, b) | Expr::Lt(a, b) | Expr::Leq(a, b)
        | Expr::Gt(a, b) | Expr::Geq(a, b) | Expr::Add(a, b) | Expr::Sub(a, b)
        | Expr::Mul(a, b) | Expr::Div(a, b) | Expr::IntDiv(a, b) | Expr::Mod(a, b)
        | Expr::Pow(a, b) | Expr::In(a, b) | Expr::NotIn(a, b) | Expr::Subseteq(a, b)
        | Expr::Union(a, b) | Expr::Intersect(a, b) | Expr::SetMinus(a, b)
        | Expr::Range(a, b) | Expr::LeadsTo(a, b) | Expr::FuncSet(a, b)
        | Expr::WeakFair(a, b) | Expr::StrongFair(a, b) | Expr::FuncApply(a, b) => {
            f(&mut a.node); f(&mut b.node);
        }
        Expr::Not(e) | Expr::Neg(e) | Expr::Domain(e) | Expr::Powerset(e)
        | Expr::BigUnion(e) | Expr::Always(e) | Expr::Eventually(e)
        | Expr::Unchanged(e) | Expr::Enabled(e) | Expr::Prime(e) => f(&mut e.node),
        Expr::If(c, t, e) => { f(&mut c.node); f(&mut t.node); f(&mut e.node); }
        Expr::Apply(op, args) => {
            f(&mut op.node);
            for a in args { f(&mut a.node); }
        }
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body)
        | Expr::FuncDef(bounds, body) | Expr::SetBuilder(body, bounds) => {
            for b in bounds { if let Some(d) = &mut b.domain { f(&mut d.node); } }
            f(&mut body.node);
        }
        Expr::Choose(bound, body) | Expr::SetFilter(bound, body) => {
            if let Some(d) = &mut bound.domain { f(&mut d.node); }
            f(&mut body.node);
        }
        Expr::SetEnum(es) | Expr::Tuple(es) | Expr::Times(es) => {
            for e in es { f(&mut e.node); }
        }
        Expr::RecordAccess(r, _) => f(&mut r.node),
        Expr::Record(fs) | Expr::RecordSet(fs) => {
            for (_, e) in fs { f(&mut e.node); }
        }
        Expr::Except(base, specs) => {
            f(&mut base.node);
            for spec in specs {
                for elem in &mut spec.path {
                    if let crate::ast::ExceptPathElement::Index(e) = elem { f(&mut e.node); }
                }
                f(&mut spec.value.node);
            }
        }
        Expr::Case(arms, default) => {
            for arm in arms { f(&mut arm.guard.node); f(&mut arm.body.node); }
            if let Some(d) = default { f(&mut d.node); }
        }
        Expr::Let(defs, body) => {
            for d in defs { f(&mut d.body.node); }
            f(&mut body.node);
        }
        Expr::Lambda(_, body) => f(&mut body.node),
        Expr::Label(label) => f(&mut label.body.node),
        Expr::InstanceExpr(_, subs) => { for s in subs { f(&mut s.to.node); } }
        Expr::SubstIn(subs, body) => {
            for s in subs { f(&mut s.to.node); }
            f(&mut body.node);
        }
        Expr::ModuleRef(_, _, args) => { for a in args { f(&mut a.node); } }
        Expr::Ident(..) | Expr::StateVar(..) | Expr::Bool(_) | Expr::Int(_)
        | Expr::String(_) | Expr::OpRef(_) => {}
    }
}
