// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structural AST-walking delegation and scope-narrowing helpers for
//! hoistability analysis.
//!
//! Extracted from mark_hoistable.rs as part of #3442. Contains the structural
//! dispatch (`mark_hoistable_structural`) and all binding-construct walkers
//! (Except, Case, multi-bound, single-bound, Let, Lambda).
//!
//! Mutual sibling reference: this module calls `mark_hoistable_rec` from
//! `super::mark_hoistable`, and `mark_hoistable_rec` calls
//! `mark_hoistable_structural` from this module.

use super::mark_hoistable::mark_hoistable_rec;
use rustc_hash::FxHashSet;
use tla_core::ast::{BoundPattern, BoundVar, Expr};
use tla_core::free_vars;
use tla_core::Spanned;

/// Structural and binding expressions (If, Apply, Except, Case, quantifiers, etc.).
pub(super) fn mark_hoistable_structural(
    expr: &Expr,
    bound_names: &FxHashSet<&str>,
    hoistable: &mut FxHashSet<usize>,
) -> bool {
    match expr {
        Expr::If(cond, then_b, else_b) => {
            mark_hoistable_rec(&cond.node, bound_names, hoistable)
                | mark_hoistable_rec(&then_b.node, bound_names, hoistable)
                | mark_hoistable_rec(&else_b.node, bound_names, hoistable)
        }
        Expr::Tuple(elems) | Expr::SetEnum(elems) | Expr::Times(elems) => {
            mark_children_vec(elems, bound_names, hoistable)
        }
        Expr::Record(fields) | Expr::RecordSet(fields) => {
            let mut refs = false;
            for (_, v) in fields {
                refs |= mark_hoistable_rec(&v.node, bound_names, hoistable);
            }
            refs
        }
        Expr::RecordAccess(rec, _) => mark_hoistable_rec(&rec.node, bound_names, hoistable),
        Expr::Apply(op, args) => {
            let mut refs = mark_hoistable_rec(&op.node, bound_names, hoistable);
            for a in args {
                refs |= mark_hoistable_rec(&a.node, bound_names, hoistable);
            }
            refs
        }
        Expr::ModuleRef(_, _, args) => mark_children_vec(args, bound_names, hoistable),
        Expr::Except(base, specs) => mark_hoistable_except(base, specs, bound_names, hoistable),
        Expr::Case(arms, other) => mark_hoistable_case(arms, other, bound_names, hoistable),
        Expr::Label(label) => mark_hoistable_rec(&label.body.node, bound_names, hoistable),

        // Binding constructs with scope narrowing
        Expr::Forall(bounds, body)
        | Expr::Exists(bounds, body)
        | Expr::SetBuilder(body, bounds)
        | Expr::FuncDef(bounds, body) => {
            mark_hoistable_multi_bound(bounds, body, bound_names, hoistable)
        }
        Expr::Choose(bound, pred) | Expr::SetFilter(bound, pred) => {
            mark_hoistable_single_bound(bound, pred, bound_names, hoistable)
        }
        Expr::Let(defs, body) => mark_hoistable_let(defs, body, bound_names, hoistable),
        Expr::Lambda(params, body) => {
            let narrowed = narrow_lambda(bound_names, params);
            if !narrowed.is_empty() {
                mark_hoistable_rec(&body.node, &narrowed, hoistable)
            } else {
                false
            }
        }
        Expr::SubstIn(_, _) | Expr::InstanceExpr(_, _) => true,
        _ => false,
    }
}

fn mark_hoistable_except(
    base: &Spanned<Expr>,
    specs: &[tla_core::ast::ExceptSpec],
    bound_names: &FxHashSet<&str>,
    hoistable: &mut FxHashSet<usize>,
) -> bool {
    let mut refs = mark_hoistable_rec(&base.node, bound_names, hoistable);
    for spec in specs {
        for key in &spec.path {
            if let tla_core::ast::ExceptPathElement::Index(idx) = key {
                refs |= mark_hoistable_rec(&idx.node, bound_names, hoistable);
            }
        }
        refs |= mark_hoistable_rec(&spec.value.node, bound_names, hoistable);
    }
    refs
}

fn mark_hoistable_case(
    arms: &[tla_core::ast::CaseArm],
    other: &Option<Box<Spanned<Expr>>>,
    bound_names: &FxHashSet<&str>,
    hoistable: &mut FxHashSet<usize>,
) -> bool {
    let mut refs = false;
    for arm in arms {
        refs |= mark_hoistable_rec(&arm.guard.node, bound_names, hoistable);
        refs |= mark_hoistable_rec(&arm.body.node, bound_names, hoistable);
    }
    if let Some(o) = other {
        refs |= mark_hoistable_rec(&o.node, bound_names, hoistable);
    }
    refs
}

fn mark_hoistable_multi_bound(
    bounds: &[BoundVar],
    body: &Spanned<Expr>,
    bound_names: &FxHashSet<&str>,
    hoistable: &mut FxHashSet<usize>,
) -> bool {
    let mut refs = false;
    // Domain expressions are evaluated in the outer quantifier scope,
    // so they can safely be added to the outer hoistable set.
    for b in bounds {
        if let Some(d) = &b.domain {
            refs |= mark_hoistable_rec(&d.node, bound_names, hoistable);
        }
    }
    // Part of #3128: Body expressions are evaluated inside the binding
    // construct's iteration loop, where the construct's bound variables
    // change each iteration. Marking them as hoistable in the outer
    // quantifier's set would cause stale cache hits because the hoist
    // frame is shared across binding-construct iterations. Use a
    // throwaway set so body expressions are not added to the outer set.
    let narrowed = narrow_multi(bound_names, bounds);
    if !narrowed.is_empty() {
        let mut body_hoistable = FxHashSet::default();
        refs |= mark_hoistable_rec(&body.node, &narrowed, &mut body_hoistable);
    }
    refs
}

fn mark_hoistable_single_bound(
    bound: &BoundVar,
    pred: &Spanned<Expr>,
    bound_names: &FxHashSet<&str>,
    hoistable: &mut FxHashSet<usize>,
) -> bool {
    let mut refs = false;
    // Domain is evaluated in the outer scope — safe to add to outer hoistable set.
    if let Some(d) = &bound.domain {
        refs |= mark_hoistable_rec(&d.node, bound_names, hoistable);
    }
    // Part of #3128: Predicate is evaluated inside the binding construct's
    // iteration loop — use throwaway set (see mark_hoistable_multi_bound).
    let narrowed = narrow_single(bound_names, bound);
    if !narrowed.is_empty() {
        let mut body_hoistable = FxHashSet::default();
        refs |= mark_hoistable_rec(&pred.node, &narrowed, &mut body_hoistable);
    }
    refs
}

fn mark_hoistable_let(
    defs: &[tla_core::ast::OperatorDef],
    body: &Spanned<Expr>,
    bound_names: &FxHashSet<&str>,
    hoistable: &mut FxHashSet<usize>,
) -> bool {
    let capturing_defs = capturing_let_defs(defs, bound_names);
    let let_bound_names = extend_names(
        &narrow_let_names(bound_names, defs),
        capturing_defs.iter().copied(),
    );
    let mut refs = false;
    for def in defs {
        let def_bound_names = extend_names(
            &let_bound_names,
            def.params.iter().map(|param| param.name.node.as_str()),
        );
        refs |= mark_hoistable_rec(&def.body.node, &def_bound_names, hoistable);
    }
    if !let_bound_names.is_empty() {
        refs |= mark_hoistable_rec(&body.node, &let_bound_names, hoistable);
    }
    refs
}

fn capturing_let_defs<'a>(
    defs: &'a [tla_core::ast::OperatorDef],
    bound_names: &FxHashSet<&'a str>,
) -> FxHashSet<&'a str> {
    let mut capturing = FxHashSet::default();
    loop {
        let known_names = extend_names(bound_names, capturing.iter().copied());
        let mut changed = false;
        for def in defs {
            let def_name = def.name.node.as_str();
            if capturing.contains(def_name) {
                continue;
            }
            if def_captures_names(def, &known_names) {
                capturing.insert(def_name);
                changed = true;
            }
        }
        if !changed {
            return capturing;
        }
    }
}

fn def_captures_names(def: &tla_core::ast::OperatorDef, names: &FxHashSet<&str>) -> bool {
    if names.is_empty() {
        return false;
    }
    let free = free_vars(&def.body.node);
    free.iter().any(|name| {
        names.contains(name.as_str())
            && !def
                .params
                .iter()
                .any(|param| param.name.node.as_str() == name.as_str())
    })
}

fn mark_children_vec(
    children: &[Spanned<Expr>],
    bound_names: &FxHashSet<&str>,
    hoistable: &mut FxHashSet<usize>,
) -> bool {
    let mut refs = false;
    for c in children {
        refs |= mark_hoistable_rec(&c.node, bound_names, hoistable);
    }
    refs
}

fn extend_names<'a, I>(names: &FxHashSet<&'a str>, extra: I) -> FxHashSet<&'a str>
where
    I: IntoIterator<Item = &'a str>,
{
    let mut extended = names.iter().copied().collect::<FxHashSet<_>>();
    extended.extend(extra);
    extended
}

fn narrow_let_names<'a>(
    names: &FxHashSet<&'a str>,
    defs: &'a [tla_core::ast::OperatorDef],
) -> FxHashSet<&'a str> {
    names
        .iter()
        .filter(|n| !defs.iter().any(|d| d.name.node.as_str() == **n))
        .copied()
        .collect()
}

fn narrow_multi<'a>(names: &FxHashSet<&'a str>, bounds: &[BoundVar]) -> FxHashSet<&'a str> {
    names
        .iter()
        .filter(|n| {
            !bounds.iter().any(|b| {
                b.name.node.as_str() == **n
                    || matches!(&b.pattern, Some(BoundPattern::Tuple(vars)) if vars.iter().any(|v| v.node.as_str() == **n))
                    || matches!(&b.pattern, Some(BoundPattern::Var(v)) if v.node.as_str() == **n)
            })
        })
        .copied()
        .collect()
}

fn narrow_single<'a>(names: &FxHashSet<&'a str>, bound: &BoundVar) -> FxHashSet<&'a str> {
    names
        .iter()
        .filter(|n| {
            bound.name.node.as_str() != **n
                && !matches!(&bound.pattern, Some(BoundPattern::Tuple(vars)) if vars.iter().any(|v| v.node.as_str() == **n))
                && !matches!(&bound.pattern, Some(BoundPattern::Var(v)) if v.node.as_str() == **n)
        })
        .copied()
        .collect()
}

fn narrow_lambda<'a>(names: &FxHashSet<&'a str>, params: &[Spanned<String>]) -> FxHashSet<&'a str> {
    names
        .iter()
        .filter(|n| !params.iter().any(|p| p.node.as_str() == **n))
        .copied()
        .collect()
}
