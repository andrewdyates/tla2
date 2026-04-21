// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::core::AstToLive;
use tla_core::ast::{Expr, ModuleTarget};

impl AstToLive {
    /// Check if an expression references a given identifier name.
    /// Used to detect recursive LET bindings.
    pub(super) fn expr_references_name(expr: &Expr, name: &str) -> bool {
        match expr {
            Expr::Ident(n, _) => n == name,
            // StateVar is pre-resolved, doesn't reference names by lookup.
            Expr::StateVar(_, _, _) => false,
            Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::OpRef(_) => false,
            Expr::Not(e)
            | Expr::Prime(e)
            | Expr::Enabled(e)
            | Expr::Always(e)
            | Expr::Eventually(e)
            | Expr::Unchanged(e)
            | Expr::Neg(e)
            | Expr::Powerset(e)
            | Expr::BigUnion(e)
            | Expr::Domain(e) => Self::expr_references_name(&e.node, name),
            Expr::And(a, b)
            | Expr::Or(a, b)
            | Expr::Implies(a, b)
            | Expr::Equiv(a, b)
            | Expr::Eq(a, b)
            | Expr::Neq(a, b)
            | Expr::Lt(a, b)
            | Expr::Leq(a, b)
            | Expr::Gt(a, b)
            | Expr::Geq(a, b)
            | Expr::Add(a, b)
            | Expr::Sub(a, b)
            | Expr::Mul(a, b)
            | Expr::Div(a, b)
            | Expr::Mod(a, b)
            | Expr::IntDiv(a, b)
            | Expr::Pow(a, b)
            | Expr::In(a, b)
            | Expr::NotIn(a, b)
            | Expr::Subseteq(a, b)
            | Expr::Union(a, b)
            | Expr::Intersect(a, b)
            | Expr::SetMinus(a, b)
            | Expr::Range(a, b)
            | Expr::FuncSet(a, b)
            | Expr::LeadsTo(a, b)
            | Expr::WeakFair(a, b)
            | Expr::StrongFair(a, b) => {
                Self::expr_references_name(&a.node, name)
                    || Self::expr_references_name(&b.node, name)
            }
            Expr::If(c, t, e) => {
                Self::expr_references_name(&c.node, name)
                    || Self::expr_references_name(&t.node, name)
                    || Self::expr_references_name(&e.node, name)
            }
            Expr::Apply(op, args) => {
                Self::expr_references_name(&op.node, name)
                    || args
                        .iter()
                        .any(|a| Self::expr_references_name(&a.node, name))
            }
            Expr::FuncApply(f, a) => {
                Self::expr_references_name(&f.node, name)
                    || Self::expr_references_name(&a.node, name)
            }
            Expr::Tuple(elems) | Expr::SetEnum(elems) => elems
                .iter()
                .any(|e| Self::expr_references_name(&e.node, name)),
            Expr::Record(fields) => fields
                .iter()
                .any(|(_, v)| Self::expr_references_name(&v.node, name)),
            Expr::RecordAccess(r, _) => Self::expr_references_name(&r.node, name),
            Expr::Let(defs, body) => {
                // Check if name is shadowed by a LET def.
                if defs.iter().any(|d| d.name.node == name) {
                    return false;
                }
                defs.iter()
                    .any(|d| Self::expr_references_name(&d.body.node, name))
                    || Self::expr_references_name(&body.node, name)
            }
            Expr::Forall(bounds, body)
            | Expr::Exists(bounds, body)
            | Expr::SetBuilder(body, bounds) => {
                // Check if name is bound.
                if bounds.iter().any(|b| b.name.node == name) {
                    return false;
                }
                bounds.iter().any(|b| {
                    b.domain
                        .as_ref()
                        .is_some_and(|d| Self::expr_references_name(&d.node, name))
                }) || Self::expr_references_name(&body.node, name)
            }
            Expr::Choose(bound, body) => {
                if bound.name.node == name {
                    return false;
                }
                bound
                    .domain
                    .as_ref()
                    .is_some_and(|d| Self::expr_references_name(&d.node, name))
                    || Self::expr_references_name(&body.node, name)
            }
            Expr::FuncDef(bounds, body) => {
                if bounds.iter().any(|b| b.name.node == name) {
                    return false;
                }
                bounds.iter().any(|b| {
                    b.domain
                        .as_ref()
                        .is_some_and(|d| Self::expr_references_name(&d.node, name))
                }) || Self::expr_references_name(&body.node, name)
            }
            Expr::Except(base, specs) => {
                Self::expr_references_name(&base.node, name)
                    || specs.iter().any(|s| {
                        Self::expr_references_name(&s.value.node, name)
                            || s.path.iter().any(|p| match p {
                                tla_core::ast::ExceptPathElement::Index(idx) => {
                                    Self::expr_references_name(&idx.node, name)
                                }
                                tla_core::ast::ExceptPathElement::Field(_) => false,
                            })
                    })
            }
            Expr::Case(arms, other) => {
                arms.iter().any(|arm| {
                    Self::expr_references_name(&arm.guard.node, name)
                        || Self::expr_references_name(&arm.body.node, name)
                }) || other
                    .as_ref()
                    .is_some_and(|o| Self::expr_references_name(&o.node, name))
            }
            Expr::Lambda(params, body) => {
                // Check if name is bound by lambda params.
                if params.iter().any(|p| p.node == name) {
                    return false;
                }
                Self::expr_references_name(&body.node, name)
            }
            Expr::SetFilter(bound, pred) => {
                if bound.name.node == name {
                    return false;
                }
                bound
                    .domain
                    .as_ref()
                    .is_some_and(|d| Self::expr_references_name(&d.node, name))
                    || Self::expr_references_name(&pred.node, name)
            }
            Expr::Times(elems) => elems
                .iter()
                .any(|e| Self::expr_references_name(&e.node, name)),
            Expr::RecordSet(fields) => fields
                .iter()
                .any(|(_, v)| Self::expr_references_name(&v.node, name)),
            Expr::ModuleRef(target, _, args) => {
                let target_has = match target {
                    ModuleTarget::Parameterized(_, params) => params
                        .iter()
                        .any(|p| Self::expr_references_name(&p.node, name)),
                    ModuleTarget::Chained(base) => Self::expr_references_name(&base.node, name),
                    ModuleTarget::Named(n) => n == name,
                };
                target_has
                    || args
                        .iter()
                        .any(|a| Self::expr_references_name(&a.node, name))
            }
            Expr::InstanceExpr(_, subs) => subs
                .iter()
                .any(|s| Self::expr_references_name(&s.to.node, name)),
            Expr::SubstIn(subs, body) => {
                subs.iter()
                    .any(|s| Self::expr_references_name(&s.to.node, name))
                    || Self::expr_references_name(&body.node, name)
            }
            Expr::Label(label) => Self::expr_references_name(&label.body.node, name),
        }
    }
}
