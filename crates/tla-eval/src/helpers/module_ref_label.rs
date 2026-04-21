// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Named subexpression-label selection for `Def!Label`.

use tla_core::ast::{
    BoundVar, CaseArm, ExceptPathElement, ExceptSpec, Expr, ModuleTarget, OperatorDef, Substitution,
};
use tla_core::Spanned;

pub(super) fn select_named_label(def: &OperatorDef, name: &str) -> Option<Spanned<Expr>> {
    select_named_label_in_expr(&def.body, name)
}

pub(super) fn select_named_label_expr(expr: &Spanned<Expr>, name: &str) -> Option<Spanned<Expr>> {
    select_named_label_in_expr(expr, name)
}

fn select_named_label_in_expr(expr: &Spanned<Expr>, name: &str) -> Option<Spanned<Expr>> {
    match &expr.node {
        Expr::Label(label) => (label.name.node == name).then(|| (*label.body).clone()),
        Expr::SubstIn(subs, body) => select_named_label_in_expr(body, name)
            .map(|selected| wrap_substin(expr, subs, selected)),
        Expr::Let(defs, body) => {
            select_named_label_in_expr(body, name).map(|selected| wrap_let(expr, defs, selected))
        }
        _ => select_named_label_in_transparent_expr(expr, name),
    }
}

fn select_named_label_in_transparent_expr(
    expr: &Spanned<Expr>,
    name: &str,
) -> Option<Spanned<Expr>> {
    match &expr.node {
        Expr::Apply(op, args) => {
            select_named_label_in_expr(op, name).or_else(|| select_named_label_in_slice(args, name))
        }
        Expr::ModuleRef(target, _, args) => select_named_label_in_target(target, name)
            .or_else(|| select_named_label_in_slice(args, name)),
        Expr::InstanceExpr(_, subs) => select_named_label_in_substitutions(subs, name),
        Expr::Lambda(_, body)
        | Expr::Not(body)
        | Expr::Prime(body)
        | Expr::Always(body)
        | Expr::Eventually(body)
        | Expr::Enabled(body)
        | Expr::Unchanged(body)
        | Expr::Powerset(body)
        | Expr::BigUnion(body)
        | Expr::Domain(body)
        | Expr::Neg(body)
        | Expr::RecordAccess(body, _) => select_named_label_in_expr(body, name),
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Subseteq(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::FuncApply(a, b)
        | Expr::FuncSet(a, b)
        | Expr::LeadsTo(a, b)
        | Expr::WeakFair(a, b)
        | Expr::StrongFair(a, b)
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
        | Expr::Range(a, b) => {
            select_named_label_in_expr(a, name).or_else(|| select_named_label_in_expr(b, name))
        }
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) | Expr::FuncDef(bounds, body) => {
            select_named_label_in_bound_body(bounds, body, name)
        }
        Expr::Choose(bound, body) | Expr::SetFilter(bound, body) => {
            select_named_label_in_single_bound_body(bound, body, name)
        }
        Expr::SetBuilder(body, bounds) => select_named_label_in_bound_body(bounds, body, name),
        Expr::SetEnum(exprs) | Expr::Tuple(exprs) | Expr::Times(exprs) => {
            select_named_label_in_slice(exprs, name)
        }
        Expr::Except(base, specs) => select_named_label_in_expr(base, name)
            .or_else(|| select_named_label_in_except_specs(specs, name)),
        Expr::Record(fields) | Expr::RecordSet(fields) => fields
            .iter()
            .find_map(|(_, field_expr)| select_named_label_in_expr(field_expr, name)),
        Expr::If(cond, then_, else_) => select_named_label_in_if(cond, then_, else_, name),
        Expr::Case(arms, other) => {
            select_named_label_in_case(arms, other.as_ref().map(|expr| &**expr), name)
        }
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _)
        | Expr::OpRef(_)
        | Expr::Label(_)
        | Expr::SubstIn(_, _)
        | Expr::Let(_, _) => None,
    }
}

fn wrap_substin(
    expr: &Spanned<Expr>,
    subs: &[Substitution],
    selected: Spanned<Expr>,
) -> Spanned<Expr> {
    Spanned::new(Expr::SubstIn(subs.to_vec(), Box::new(selected)), expr.span)
}

fn wrap_let(expr: &Spanned<Expr>, defs: &[OperatorDef], selected: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::new(Expr::Let(defs.to_vec(), Box::new(selected)), expr.span)
}

fn select_named_label_in_slice(exprs: &[Spanned<Expr>], name: &str) -> Option<Spanned<Expr>> {
    exprs
        .iter()
        .find_map(|expr| select_named_label_in_expr(expr, name))
}

fn select_named_label_in_target(target: &ModuleTarget, name: &str) -> Option<Spanned<Expr>> {
    match target {
        ModuleTarget::Named(_) => None,
        ModuleTarget::Parameterized(_, params) => select_named_label_in_slice(params, name),
        ModuleTarget::Chained(base) => select_named_label_in_expr(base, name),
    }
}

fn select_named_label_in_substitutions(subs: &[Substitution], name: &str) -> Option<Spanned<Expr>> {
    subs.iter()
        .find_map(|sub| select_named_label_in_expr(&sub.to, name))
}

fn select_named_label_in_bounds(bounds: &[BoundVar], name: &str) -> Option<Spanned<Expr>> {
    bounds
        .iter()
        .find_map(|bound| select_named_label_in_bound(bound, name))
}

fn select_named_label_in_bound(bound: &BoundVar, name: &str) -> Option<Spanned<Expr>> {
    bound
        .domain
        .as_ref()
        .and_then(|domain| select_named_label_in_expr(domain, name))
}

fn select_named_label_in_bound_body(
    bounds: &[BoundVar],
    body: &Spanned<Expr>,
    name: &str,
) -> Option<Spanned<Expr>> {
    select_named_label_in_bounds(bounds, name).or_else(|| select_named_label_in_expr(body, name))
}

fn select_named_label_in_single_bound_body(
    bound: &BoundVar,
    body: &Spanned<Expr>,
    name: &str,
) -> Option<Spanned<Expr>> {
    select_named_label_in_bound(bound, name).or_else(|| select_named_label_in_expr(body, name))
}

fn select_named_label_in_except_specs(specs: &[ExceptSpec], name: &str) -> Option<Spanned<Expr>> {
    specs.iter().find_map(|spec| {
        spec.path
            .iter()
            .find_map(|elem| match elem {
                ExceptPathElement::Index(index) => select_named_label_in_expr(index, name),
                ExceptPathElement::Field(_) => None,
            })
            .or_else(|| select_named_label_in_expr(&spec.value, name))
    })
}

fn select_named_label_in_if(
    cond: &Spanned<Expr>,
    then_: &Spanned<Expr>,
    else_: &Spanned<Expr>,
    name: &str,
) -> Option<Spanned<Expr>> {
    select_named_label_in_expr(cond, name)
        .or_else(|| select_named_label_in_expr(then_, name))
        .or_else(|| select_named_label_in_expr(else_, name))
}

fn select_named_label_in_case(
    arms: &[CaseArm],
    other: Option<&Spanned<Expr>>,
    name: &str,
) -> Option<Spanned<Expr>> {
    select_named_label_in_case_arms(arms, name)
        .or_else(|| other.and_then(|expr| select_named_label_in_expr(expr, name)))
}

fn select_named_label_in_case_arms(arms: &[CaseArm], name: &str) -> Option<Spanned<Expr>> {
    arms.iter().find_map(|arm| {
        select_named_label_in_expr(&arm.guard, name)
            .or_else(|| select_named_label_in_expr(&arm.body, name))
    })
}
