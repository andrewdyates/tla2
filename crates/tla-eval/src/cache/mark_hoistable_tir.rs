// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! TIR-specific hoistable analysis for quantifier subexpression caching.
//!
//! Mirrors `mark_hoistable.rs` for AST expressions. Walks TIR body trees
//! bottom-up to identify subexpressions that are invariant with respect to
//! the current quantifier's bound variables. These can be cached across
//! loop iterations using the shared `HOIST_STACK`.
//!
//! Part of #3392: Closes the hoist-cache gap between AST and TIR evaluation.

use rustc_hash::FxHashSet;
use std::rc::Rc;
use tla_core::Spanned;
use tla_tir::nodes::TirExpr;
use tla_tir::nodes::{TirBoundPattern, TirBoundVar};

use super::quantifier_hoist::{
    enter_quantifier_hoist_scope, mark_hoistable_cache_get, mark_hoistable_cache_insert,
    QuantifierHoistScopeGuard,
};
use crate::helpers::quantifiers::HOIST_ENABLED;

/// Compute and enter a TIR quantifier hoist scope for the given body and
/// bound variables. Returns the scope guard (if any hoistable expressions
/// were found). Analogous to `enter_hoist_scope` for AST expressions.
///
/// The cache key uses `(body_ptr, vars_ptr)` so different quantifier nesting
/// levels get distinct cache entries for the same body expression.
pub(crate) fn enter_tir_hoist_scope(
    body: &Spanned<TirExpr>,
    vars: &[TirBoundVar],
) -> Option<QuantifierHoistScopeGuard> {
    if !HOIST_ENABLED {
        return None;
    }
    let bound_names = collect_tir_bound_names(vars);
    let cache_key = (
        &body.node as *const TirExpr as usize,
        vars.as_ptr() as usize,
    );
    let hoistable = mark_hoistable_tir(&body.node, &bound_names, cache_key);
    enter_quantifier_hoist_scope(hoistable)
}

/// Single-bound-variable variant for CHOOSE and SetFilter.
pub(crate) fn enter_tir_hoist_scope_single(
    body: &Spanned<TirExpr>,
    var: &TirBoundVar,
) -> Option<QuantifierHoistScopeGuard> {
    if !HOIST_ENABLED {
        return None;
    }
    let bound_names = collect_tir_bound_names(std::slice::from_ref(var));
    let cache_key = (
        &body.node as *const TirExpr as usize,
        var as *const TirBoundVar as usize,
    );
    let hoistable = mark_hoistable_tir(&body.node, &bound_names, cache_key);
    enter_quantifier_hoist_scope(hoistable)
}

/// Walk a TIR body bottom-up. For each compound subexpression whose subtree
/// does NOT reference any bound name, add its pointer (as `usize`) to the
/// hoistable set.
///
/// Part of #3962 Wave 25: Uses consolidated mark_hoistable_cache in HOIST_STATE
/// (was standalone MARK_HOISTABLE_CACHE thread_local). Keyed on (body_ptr, bounds_ptr).
/// TIR pointers occupy different address space from AST pointers, so no
/// collision is possible.
pub(crate) fn mark_hoistable_tir(
    body: &TirExpr,
    bound_names: &FxHashSet<&str>,
    cache_key: (usize, usize),
) -> Rc<FxHashSet<usize>> {
    if let Some(result) = mark_hoistable_cache_get(&cache_key) {
        return result;
    }
    let mut hoistable = FxHashSet::default();
    mark_hoistable_tir_rec(body, bound_names, &mut hoistable);
    let rc = Rc::new(hoistable);
    mark_hoistable_cache_insert(cache_key, Rc::clone(&rc));
    rc
}

/// Returns `true` if the subtree references any name in `bound_names`.
/// As a side effect, adds non-referencing compound subtrees to `hoistable`.
fn mark_hoistable_tir_rec(
    expr: &TirExpr,
    bound_names: &FxHashSet<&str>,
    hoistable: &mut FxHashSet<usize>,
) -> bool {
    let refs = match expr {
        // Leaves
        TirExpr::Name(name_ref) => return bound_names.contains(name_ref.name.as_str()),
        TirExpr::Const { .. } | TirExpr::ExceptAt | TirExpr::OpRef(_) => return false,

        // Unary
        TirExpr::BoolNot(a)
        | TirExpr::ArithNeg(a)
        | TirExpr::Prime(a)
        | TirExpr::Domain(a)
        | TirExpr::Powerset(a)
        | TirExpr::BigUnion(a)
        | TirExpr::Unchanged(a) => mark_hoistable_tir_rec(&a.node, bound_names, hoistable),

        TirExpr::KSubset { base, k } => {
            mark_hoistable_tir_rec(&base.node, bound_names, hoistable)
                | mark_hoistable_tir_rec(&k.node, bound_names, hoistable)
        }

        // Binary arithmetic/boolean/comparison (two-level TIR dispatch)
        TirExpr::ArithBinOp { left, right, .. }
        | TirExpr::BoolBinOp { left, right, .. }
        | TirExpr::Cmp { left, right, .. } => {
            mark_hoistable_tir_rec(&left.node, bound_names, hoistable)
                | mark_hoistable_tir_rec(&right.node, bound_names, hoistable)
        }

        // Binary value/set ops
        TirExpr::In { elem, set } => {
            mark_hoistable_tir_rec(&elem.node, bound_names, hoistable)
                | mark_hoistable_tir_rec(&set.node, bound_names, hoistable)
        }
        TirExpr::Subseteq { left, right }
        | TirExpr::SetBinOp { left, right, .. }
        | TirExpr::FuncSet {
            domain: left,
            range: right,
        } => {
            mark_hoistable_tir_rec(&left.node, bound_names, hoistable)
                | mark_hoistable_tir_rec(&right.node, bound_names, hoistable)
        }
        TirExpr::Range { lo, hi } => {
            mark_hoistable_tir_rec(&lo.node, bound_names, hoistable)
                | mark_hoistable_tir_rec(&hi.node, bound_names, hoistable)
        }
        TirExpr::FuncApply { func, arg } => {
            mark_hoistable_tir_rec(&func.node, bound_names, hoistable)
                | mark_hoistable_tir_rec(&arg.node, bound_names, hoistable)
        }

        // If-then-else
        TirExpr::If { cond, then_, else_ } => {
            mark_hoistable_tir_rec(&cond.node, bound_names, hoistable)
                | mark_hoistable_tir_rec(&then_.node, bound_names, hoistable)
                | mark_hoistable_tir_rec(&else_.node, bound_names, hoistable)
        }

        // Structured value constructors
        TirExpr::Tuple(elems) | TirExpr::SetEnum(elems) | TirExpr::Times(elems) => {
            mark_children_vec(elems, bound_names, hoistable)
        }
        TirExpr::Record(fields) | TirExpr::RecordSet(fields) => {
            let mut refs = false;
            for (_, v) in fields {
                refs |= mark_hoistable_tir_rec(&v.node, bound_names, hoistable);
            }
            refs
        }
        TirExpr::RecordAccess { record, .. } => {
            mark_hoistable_tir_rec(&record.node, bound_names, hoistable)
        }

        // Apply (operator calls) — NOT stage-1 hoistable, but recurse for children
        TirExpr::Apply { op, args } => {
            let mut refs = mark_hoistable_tir_rec(&op.node, bound_names, hoistable);
            for a in args {
                refs |= mark_hoistable_tir_rec(&a.node, bound_names, hoistable);
            }
            refs
        }

        // Except
        TirExpr::Except { base, specs } => {
            let mut refs = mark_hoistable_tir_rec(&base.node, bound_names, hoistable);
            for spec in specs {
                for path_elem in &spec.path {
                    match path_elem {
                        tla_tir::nodes::TirExceptPathElement::Index(idx) => {
                            refs |= mark_hoistable_tir_rec(&idx.node, bound_names, hoistable);
                        }
                        tla_tir::nodes::TirExceptPathElement::Field(_) => {}
                    }
                }
                refs |= mark_hoistable_tir_rec(&spec.value.node, bound_names, hoistable);
            }
            refs
        }

        // Case
        TirExpr::Case { arms, other } => {
            let mut refs = false;
            for arm in arms {
                refs |= mark_hoistable_tir_rec(&arm.guard.node, bound_names, hoistable);
                refs |= mark_hoistable_tir_rec(&arm.body.node, bound_names, hoistable);
            }
            if let Some(o) = other {
                refs |= mark_hoistable_tir_rec(&o.node, bound_names, hoistable);
            }
            refs
        }

        // Label (pass through to body)
        TirExpr::Label { body, .. } => mark_hoistable_tir_rec(&body.node, bound_names, hoistable),

        // Binding constructs — recurse with narrowed bound names
        TirExpr::Forall { vars, body } | TirExpr::Exists { vars, body } => {
            mark_hoistable_tir_multi_bound(vars, body, bound_names, hoistable)
        }
        TirExpr::SetBuilder { body, vars } => {
            mark_hoistable_tir_multi_bound(vars, body, bound_names, hoistable)
        }
        TirExpr::FuncDef { vars, body } => {
            mark_hoistable_tir_multi_bound(vars, body, bound_names, hoistable)
        }
        TirExpr::Choose { var, body } | TirExpr::SetFilter { var, body } => {
            mark_hoistable_tir_single_bound(var, body, bound_names, hoistable)
        }

        // Let bindings
        TirExpr::Let { defs, body } => mark_hoistable_tir_let(defs, body, bound_names, hoistable),

        // Lambda — narrow by param names
        TirExpr::Lambda { params, body, .. } => {
            let narrowed = narrow_lambda_tir(bound_names, params);
            if !narrowed.is_empty() {
                mark_hoistable_tir_rec(&body.node, &narrowed, hoistable)
            } else {
                false
            }
        }

        // OperatorRef — may carry implicit dependencies, poison conservatively
        TirExpr::OperatorRef(op_ref) => {
            let mut refs = false;
            for a in &op_ref.args {
                refs |= mark_hoistable_tir_rec(&a.node, bound_names, hoistable);
            }
            refs
        }

        // Temporal operators — not evaluated by TIR, return false
        TirExpr::ActionSubscript { .. }
        | TirExpr::Always(_)
        | TirExpr::Eventually(_)
        | TirExpr::Enabled(_)
        | TirExpr::LeadsTo { .. }
        | TirExpr::WeakFair { .. }
        | TirExpr::StrongFair { .. } => false,
    };

    if !refs && is_tir_hoist_cacheable(expr) {
        hoistable.insert(expr as *const TirExpr as usize);
    }
    // Poison parent if this is an unsafe (non-analyzed) compound form with refs=false
    if !refs && !is_tir_hoist_safe(expr) {
        return true;
    }
    refs
}

/// Stage-1 TIR hoist allowlist. Mirrors `is_stage1_hoistable` for AST.
/// Only pure structural expressions with no internal binding/evaluation scopes.
pub(crate) fn is_tir_hoist_cacheable(expr: &TirExpr) -> bool {
    matches!(
        expr,
        // Unary pure
        TirExpr::BoolNot(_)
        | TirExpr::ArithNeg(_)
        | TirExpr::Domain(_)
        | TirExpr::Powerset(_)
        | TirExpr::BigUnion(_)
        | TirExpr::KSubset { .. }
        // Binary pure
        | TirExpr::ArithBinOp { .. }
        | TirExpr::BoolBinOp { .. }
        | TirExpr::Cmp { .. }
        | TirExpr::In { .. }
        | TirExpr::Subseteq { .. }
        | TirExpr::SetBinOp { .. }
        | TirExpr::FuncSet { .. }
        | TirExpr::Range { .. }
        // Pure value constructors
        | TirExpr::If { .. }
        | TirExpr::Tuple(_)
        | TirExpr::SetEnum(_)
        | TirExpr::Times(_)
        | TirExpr::Record(_)
        | TirExpr::RecordSet(_)
        | TirExpr::RecordAccess { .. }
        | TirExpr::Case { .. }
        | TirExpr::Except { .. }
    )
}

/// Non-poisoning binding constructs for TIR (Stage-2 equivalent).
/// Label is included because it is a transparent wrapper with no runtime effect
/// in eval_tir — excluding it would conservatively poison labeled parents.
fn is_nonpoisoning_tir_binding(expr: &TirExpr) -> bool {
    matches!(
        expr,
        TirExpr::SetBuilder { .. } | TirExpr::SetFilter { .. } | TirExpr::Label { .. }
    )
}

/// Is this TIR expression safe to appear inside a hoistable parent?
fn is_tir_hoist_safe(expr: &TirExpr) -> bool {
    is_tir_hoist_cacheable(expr) || is_nonpoisoning_tir_binding(expr)
}

fn mark_hoistable_tir_multi_bound(
    vars: &[TirBoundVar],
    body: &Spanned<TirExpr>,
    bound_names: &FxHashSet<&str>,
    hoistable: &mut FxHashSet<usize>,
) -> bool {
    let mut refs = false;
    // Domain expressions are in the outer scope — safe to add to outer hoistable set
    for v in vars {
        if let Some(d) = &v.domain {
            refs |= mark_hoistable_tir_rec(&d.node, bound_names, hoistable);
        }
    }
    // Body is inside the binding — use throwaway set
    let narrowed = narrow_tir_multi(bound_names, vars);
    if !narrowed.is_empty() {
        let mut body_hoistable = FxHashSet::default();
        refs |= mark_hoistable_tir_rec(&body.node, &narrowed, &mut body_hoistable);
    }
    refs
}

fn mark_hoistable_tir_single_bound(
    var: &TirBoundVar,
    body: &Spanned<TirExpr>,
    bound_names: &FxHashSet<&str>,
    hoistable: &mut FxHashSet<usize>,
) -> bool {
    let mut refs = false;
    if let Some(d) = &var.domain {
        refs |= mark_hoistable_tir_rec(&d.node, bound_names, hoistable);
    }
    let narrowed = narrow_tir_single(bound_names, var);
    if !narrowed.is_empty() {
        let mut body_hoistable = FxHashSet::default();
        refs |= mark_hoistable_tir_rec(&body.node, &narrowed, &mut body_hoistable);
    }
    refs
}

fn mark_hoistable_tir_let(
    defs: &[tla_tir::nodes::TirLetDef],
    body: &Spanned<TirExpr>,
    bound_names: &FxHashSet<&str>,
    hoistable: &mut FxHashSet<usize>,
) -> bool {
    // Narrow bound names by removing LET-defined names
    let narrowed: FxHashSet<&str> = bound_names
        .iter()
        .filter(|n| !defs.iter().any(|d| d.name.as_str() == **n))
        .copied()
        .collect();
    let mut refs = false;
    for def in defs {
        // Further narrow by def params
        let def_names: FxHashSet<&str> = narrowed
            .iter()
            .filter(|n| !def.params.iter().any(|p| p.as_str() == **n))
            .copied()
            .collect();
        refs |= mark_hoistable_tir_rec(&def.body.node, &def_names, hoistable);
    }
    if !narrowed.is_empty() {
        refs |= mark_hoistable_tir_rec(&body.node, &narrowed, hoistable);
    }
    refs
}

fn mark_children_vec(
    children: &[Spanned<TirExpr>],
    bound_names: &FxHashSet<&str>,
    hoistable: &mut FxHashSet<usize>,
) -> bool {
    let mut refs = false;
    for c in children {
        refs |= mark_hoistable_tir_rec(&c.node, bound_names, hoistable);
    }
    refs
}

fn narrow_tir_multi<'a>(names: &FxHashSet<&'a str>, vars: &[TirBoundVar]) -> FxHashSet<&'a str> {
    names
        .iter()
        .filter(|n| {
            !vars.iter().any(|v| {
                v.name.as_str() == **n
                    || matches!(&v.pattern, Some(TirBoundPattern::Tuple(ts))
                        if ts.iter().any(|(name, _)| name.as_str() == **n))
                    || matches!(&v.pattern, Some(TirBoundPattern::Var(name, _))
                        if name.as_str() == **n)
            })
        })
        .copied()
        .collect()
}

fn narrow_tir_single<'a>(names: &FxHashSet<&'a str>, var: &TirBoundVar) -> FxHashSet<&'a str> {
    names
        .iter()
        .filter(|n| {
            var.name.as_str() != **n
                && !matches!(&var.pattern, Some(TirBoundPattern::Tuple(ts))
                    if ts.iter().any(|(name, _)| name.as_str() == **n))
                && !matches!(&var.pattern, Some(TirBoundPattern::Var(name, _))
                    if name.as_str() == **n)
        })
        .copied()
        .collect()
}

fn narrow_lambda_tir<'a>(names: &FxHashSet<&'a str>, params: &[String]) -> FxHashSet<&'a str> {
    names
        .iter()
        .filter(|n| !params.iter().any(|p| p.as_str() == **n))
        .copied()
        .collect()
}

/// Collect all bound variable names from TIR bound vars.
pub(crate) fn collect_tir_bound_names<'a>(vars: &'a [TirBoundVar]) -> FxHashSet<&'a str> {
    let mut names = FxHashSet::default();
    for v in vars {
        names.insert(v.name.as_str());
        if let Some(pat) = &v.pattern {
            match pat {
                TirBoundPattern::Var(name, _) => {
                    names.insert(name.as_str());
                }
                TirBoundPattern::Tuple(ts) => {
                    for (name, _) in ts {
                        names.insert(name.as_str());
                    }
                }
            }
        }
    }
    names
}

#[cfg(test)]
#[path = "mark_hoistable_tir_tests.rs"]
mod tests;
