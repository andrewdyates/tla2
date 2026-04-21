// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::span::Spanned;

pub(crate) fn bound_names_for_substitution(bound: &BoundVar) -> Vec<&str> {
    let mut names = vec![bound.name.node.as_str()];
    if let Some(pattern) = &bound.pattern {
        match pattern {
            BoundPattern::Var(v) => names.push(v.node.as_str()),
            BoundPattern::Tuple(vars) => names.extend(vars.iter().map(|v| v.node.as_str())),
        }
    }
    names
}

pub(super) fn filter_substitutions_capture_avoiding<'a>(
    subs: &HashMap<&'a str, &'a Spanned<Expr>>,
    bound_names: &HashSet<&str>,
) -> HashMap<&'a str, &'a Spanned<Expr>> {
    subs.iter()
        .filter(|(name, replacement)| {
            !bound_names.contains(*name)
                && !expr_has_free_var_in_set_for_substitution(&replacement.node, bound_names)
        })
        .map(|(&k, &v)| (k, v))
        .collect()
}

/// Check if any bound variable domain contains a free variable from `var_set`.
fn bounds_domains_have_free_var(bounds: &[BoundVar], var_set: &HashSet<&str>) -> bool {
    bounds.iter().any(|b| {
        b.domain
            .as_ref()
            .is_some_and(|d| expr_has_free_var_in_set_for_substitution(&d.node, var_set))
    })
}

/// Remove bound variable names (including pattern variables) from a var_set.
fn filter_var_set_by_bounds<'a>(
    var_set: &HashSet<&'a str>,
    bounds: &[BoundVar],
) -> HashSet<&'a str> {
    let mut filtered = var_set.clone();
    for b in bounds {
        for name in bound_names_for_substitution(b) {
            filtered.remove(name);
        }
    }
    filtered
}

// Check whether an expression contains any free variable whose name is in `var_set`.
// Used for capture avoidance during substitution: if a replacement expression has a
// free variable that would be captured by a binding form, the substitution is skipped.
//
// Properly recurses into binding forms (Forall, Exists, Choose, SetBuilder, SetFilter,
// FuncDef, Let), excluding bound variable names before checking the body. The previous
// conservative approach (returning `true` for all binding forms) over-filtered
// substitutions, causing LET expansion failures when replacement expressions contained
// binding forms unrelated to the enclosing scope (#2452).
pub(super) fn expr_has_free_var_in_set_for_substitution(
    expr: &Expr,
    var_set: &HashSet<&str>,
) -> bool {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => var_set.contains(name.as_str()),
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            bounds_domains_have_free_var(bounds, var_set) || {
                let filtered = filter_var_set_by_bounds(var_set, bounds);
                expr_has_free_var_in_set_for_substitution(&body.node, &filtered)
            }
        }
        Expr::Choose(bound, body) => {
            bound
                .domain
                .as_ref()
                .is_some_and(|d| expr_has_free_var_in_set_for_substitution(&d.node, var_set))
                || {
                    let mut filtered = var_set.clone();
                    for name in bound_names_for_substitution(bound) {
                        filtered.remove(name);
                    }
                    expr_has_free_var_in_set_for_substitution(&body.node, &filtered)
                }
        }
        Expr::SetBuilder(body, bounds) => {
            bounds_domains_have_free_var(bounds, var_set) || {
                let filtered = filter_var_set_by_bounds(var_set, bounds);
                expr_has_free_var_in_set_for_substitution(&body.node, &filtered)
            }
        }
        Expr::SetFilter(bound, pred) => {
            bound
                .domain
                .as_ref()
                .is_some_and(|d| expr_has_free_var_in_set_for_substitution(&d.node, var_set))
                || {
                    let mut filtered = var_set.clone();
                    for name in bound_names_for_substitution(bound) {
                        filtered.remove(name);
                    }
                    expr_has_free_var_in_set_for_substitution(&pred.node, &filtered)
                }
        }
        Expr::FuncDef(bounds, body) => {
            bounds_domains_have_free_var(bounds, var_set) || {
                let filtered = filter_var_set_by_bounds(var_set, bounds);
                expr_has_free_var_in_set_for_substitution(&body.node, &filtered)
            }
        }
        Expr::Let(defs, body) => {
            let def_names: HashSet<&str> = defs.iter().map(|d| d.name.node.as_str()).collect();
            // Check def bodies (with own params excluded but def_names still visible)
            defs.iter().any(|d| {
                let mut body_filter = var_set.clone();
                for p in &d.params {
                    body_filter.remove(p.name.node.as_str());
                }
                expr_has_free_var_in_set_for_substitution(&d.body.node, &body_filter)
            }) || {
                // Check LET body with def names excluded
                let mut filtered = var_set.clone();
                for name in &def_names {
                    filtered.remove(name);
                }
                expr_has_free_var_in_set_for_substitution(&body.node, &filtered)
            }
        }
        Expr::Lambda(params, body) => {
            // For lambda replacements, only free variables matter for capture.
            // Bound lambda parameters do not contribute to capture risk.
            let mut filtered = var_set.clone();
            for param in params {
                filtered.remove(param.node.as_str());
            }
            expr_has_free_var_in_set_for_substitution(&body.node, &filtered)
        }
        Expr::InstanceExpr(_, _) => false,
        Expr::SubstIn(subs, body) => {
            subs.iter()
                .any(|s| expr_has_free_var_in_set_for_substitution(&s.to.node, var_set))
                || expr_has_free_var_in_set_for_substitution(&body.node, var_set)
        }

        Expr::Apply(op, args) => {
            expr_has_free_var_in_set_for_substitution(&op.node, var_set)
                || args
                    .iter()
                    .any(|arg| expr_has_free_var_in_set_for_substitution(&arg.node, var_set))
        }
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
            expr_has_free_var_in_set_for_substitution(&a.node, var_set)
                || expr_has_free_var_in_set_for_substitution(&b.node, var_set)
        }
        Expr::Not(a)
        | Expr::Powerset(a)
        | Expr::BigUnion(a)
        | Expr::Domain(a)
        | Expr::Prime(a)
        | Expr::Always(a)
        | Expr::Eventually(a)
        | Expr::Enabled(a)
        | Expr::Unchanged(a)
        | Expr::Neg(a) => expr_has_free_var_in_set_for_substitution(&a.node, var_set),
        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => elems
            .iter()
            .any(|elem| expr_has_free_var_in_set_for_substitution(&elem.node, var_set)),
        Expr::ModuleRef(target, _, args) => {
            let target_has_match = match target {
                ModuleTarget::Named(_) => false,
                ModuleTarget::Parameterized(_, params) => params
                    .iter()
                    .any(|param| expr_has_free_var_in_set_for_substitution(&param.node, var_set)),
                ModuleTarget::Chained(base) => {
                    expr_has_free_var_in_set_for_substitution(&base.node, var_set)
                }
            };
            target_has_match
                || args
                    .iter()
                    .any(|arg| expr_has_free_var_in_set_for_substitution(&arg.node, var_set))
        }
        Expr::Record(fields) | Expr::RecordSet(fields) => fields
            .iter()
            .any(|(_, value)| expr_has_free_var_in_set_for_substitution(&value.node, var_set)),
        Expr::RecordAccess(record, _) => {
            expr_has_free_var_in_set_for_substitution(&record.node, var_set)
        }
        Expr::Except(base, specs) => {
            expr_has_free_var_in_set_for_substitution(&base.node, var_set)
                || specs.iter().any(|spec| {
                    spec.path.iter().any(|path_elem| match path_elem {
                        ExceptPathElement::Index(idx) => {
                            expr_has_free_var_in_set_for_substitution(&idx.node, var_set)
                        }
                        ExceptPathElement::Field(_) => false,
                    }) || expr_has_free_var_in_set_for_substitution(&spec.value.node, var_set)
                })
        }
        Expr::If(cond, then_expr, else_expr) => {
            expr_has_free_var_in_set_for_substitution(&cond.node, var_set)
                || expr_has_free_var_in_set_for_substitution(&then_expr.node, var_set)
                || expr_has_free_var_in_set_for_substitution(&else_expr.node, var_set)
        }
        Expr::Case(arms, default) => {
            arms.iter().any(|arm| {
                expr_has_free_var_in_set_for_substitution(&arm.guard.node, var_set)
                    || expr_has_free_var_in_set_for_substitution(&arm.body.node, var_set)
            }) || default
                .as_ref()
                .is_some_and(|expr| expr_has_free_var_in_set_for_substitution(&expr.node, var_set))
        }
        Expr::Label(label) => expr_has_free_var_in_set_for_substitution(&label.body.node, var_set),
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::OpRef(_) => false,
    }
}
