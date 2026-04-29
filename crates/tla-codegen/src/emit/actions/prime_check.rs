// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::{Expr, HashSet, RustEmitter};

impl<'a> RustEmitter<'a> {
    pub(in crate::emit) fn is_next_supported_prime_uses(
        expr: &Expr,
        vars: &HashSet<String>,
    ) -> bool {
        match expr {
            Expr::Prime(inner) => match &inner.node {
                Expr::Ident(name, _) => vars.contains(name),
                _ => false,
            },
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
            | Expr::IntDiv(a, b)
            | Expr::Mod(a, b)
            | Expr::Pow(a, b)
            | Expr::In(a, b)
            | Expr::NotIn(a, b)
            | Expr::Subseteq(a, b)
            | Expr::Union(a, b)
            | Expr::Intersect(a, b)
            | Expr::SetMinus(a, b)
            | Expr::FuncApply(a, b)
            | Expr::FuncSet(a, b)
            | Expr::Range(a, b) => {
                Self::is_next_supported_prime_uses(&a.node, vars)
                    && Self::is_next_supported_prime_uses(&b.node, vars)
            }
            Expr::Not(a)
            | Expr::Neg(a)
            | Expr::Domain(a)
            | Expr::Powerset(a)
            | Expr::BigUnion(a) => Self::is_next_supported_prime_uses(&a.node, vars),
            Expr::Tuple(elems) | Expr::SetEnum(elems) | Expr::Times(elems) => elems
                .iter()
                .all(|e| Self::is_next_supported_prime_uses(&e.node, vars)),
            Expr::Apply(op, args) => {
                Self::is_next_supported_prime_uses(&op.node, vars)
                    && args
                        .iter()
                        .all(|a| Self::is_next_supported_prime_uses(&a.node, vars))
            }
            Expr::ModuleRef(_target, _name, args) => args
                .iter()
                .all(|a| Self::is_next_supported_prime_uses(&a.node, vars)),
            Expr::If(c, t, e) => {
                Self::is_next_supported_prime_uses(&c.node, vars)
                    && Self::is_next_supported_prime_uses(&t.node, vars)
                    && Self::is_next_supported_prime_uses(&e.node, vars)
            }
            Expr::FuncDef(bounds, body) => {
                bounds.iter().all(|b| {
                    b.domain
                        .as_ref()
                        .map_or(true, |d| Self::is_next_supported_prime_uses(&d.node, vars))
                }) && Self::is_next_supported_prime_uses(&body.node, vars)
            }
            Expr::Except(func, specs) => {
                if !Self::is_next_supported_prime_uses(&func.node, vars) {
                    return false;
                }
                specs.iter().all(|spec| {
                    spec.path.iter().all(|p| match p {
                        tla_core::ast::ExceptPathElement::Index(idx) => {
                            Self::is_next_supported_prime_uses(&idx.node, vars)
                        }
                        tla_core::ast::ExceptPathElement::Field(_f) => true,
                    }) && Self::is_next_supported_prime_uses(&spec.value.node, vars)
                })
            }
            Expr::Record(fields) | Expr::RecordSet(fields) => fields
                .iter()
                .all(|(_k, v)| Self::is_next_supported_prime_uses(&v.node, vars)),
            Expr::RecordAccess(r, _field) => Self::is_next_supported_prime_uses(&r.node, vars),
            Expr::SetBuilder(body, bounds) => {
                bounds.iter().all(|b| {
                    b.domain
                        .as_ref()
                        .map_or(true, |d| Self::is_next_supported_prime_uses(&d.node, vars))
                }) && Self::is_next_supported_prime_uses(&body.node, vars)
            }
            Expr::SetFilter(boundvar, pred) => {
                boundvar
                    .domain
                    .as_ref()
                    .map_or(true, |d| Self::is_next_supported_prime_uses(&d.node, vars))
                    && Self::is_next_supported_prime_uses(&pred.node, vars)
            }
            Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
                bounds.iter().all(|b| {
                    b.domain
                        .as_ref()
                        .map_or(true, |d| Self::is_next_supported_prime_uses(&d.node, vars))
                }) && Self::is_next_supported_prime_uses(&body.node, vars)
            }
            Expr::Choose(boundvar, body) => {
                boundvar
                    .domain
                    .as_ref()
                    .map_or(true, |d| Self::is_next_supported_prime_uses(&d.node, vars))
                    && Self::is_next_supported_prime_uses(&body.node, vars)
            }
            Expr::Let(defs, body) => {
                defs.iter()
                    .all(|d| Self::is_next_supported_prime_uses(&d.body.node, vars))
                    && Self::is_next_supported_prime_uses(&body.node, vars)
            }
            Expr::Lambda(_params, body) => Self::is_next_supported_prime_uses(&body.node, vars),
            Expr::Label(label) => Self::is_next_supported_prime_uses(&label.body.node, vars),

            Expr::Unchanged(vars2) => Self::is_next_supported_prime_uses(&vars2.node, vars),

            Expr::Bool(_)
            | Expr::Int(_)
            | Expr::String(_)
            | Expr::Ident(_, _)
            | Expr::StateVar(..)
            | Expr::OpRef(_)
            | Expr::InstanceExpr(..) => true,
            Expr::SubstIn(subs, body) => {
                subs.iter()
                    .all(|s| Self::is_next_supported_prime_uses(&s.to.node, vars))
                    && Self::is_next_supported_prime_uses(&body.node, vars)
            }

            Expr::Case(arms, other) => {
                arms.iter().all(|arm| {
                    Self::is_next_supported_prime_uses(&arm.guard.node, vars)
                        && Self::is_next_supported_prime_uses(&arm.body.node, vars)
                }) && other
                    .as_ref()
                    .map_or(true, |o| Self::is_next_supported_prime_uses(&o.node, vars))
            }

            Expr::Always(..)
            | Expr::Eventually(..)
            | Expr::Enabled(..)
            | Expr::LeadsTo(..)
            | Expr::WeakFair(..)
            | Expr::StrongFair(..) => false,
        }
    }
}
