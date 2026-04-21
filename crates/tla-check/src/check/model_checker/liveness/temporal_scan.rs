// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Generic Expr tree scanner and predicate-based search functions.
//!
//! Provides `expr_contains`, a single exhaustive recursive scanner over all `Expr`
//! variants. Specific scanners (temporal operators, ENABLED, etc.) are thin wrappers
//! that supply a predicate. This prevents the incomplete-copy bug class where ad-hoc
//! scanners miss operators nested inside `If`, `Let`, `Case`, `FuncApply`, quantifiers,
//! records, etc. (see #1885, #2679).

use super::super::{Expr, ModelChecker, ModuleTarget};

/// Decision returned by a scan predicate for a single `Expr` node.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum ScanDecision {
    /// This node matches — return `true` immediately without recursing.
    Found,
    /// This node doesn't match — continue recursing into children.
    Continue,
}

/// Recursively scan an `Expr` tree, returning `true` if any node's predicate
/// returns `ScanDecision::Found`.
///
/// Handles ALL `Expr` variants exhaustively. When new variants are added to the
/// enum, the compiler forces an update here — preventing silent false-negatives
/// in every scanner that delegates to this function.
pub(crate) fn expr_contains(expr: &Expr, predicate: &impl Fn(&Expr) -> ScanDecision) -> bool {
    if predicate(expr) == ScanDecision::Found {
        return true;
    }

    match expr {
        // --- Leaves (no children) ---
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _)
        | Expr::OpRef(_) => false,

        // --- Unary (single child) ---
        Expr::Not(e)
        | Expr::Neg(e)
        | Expr::Powerset(e)
        | Expr::BigUnion(e)
        | Expr::Domain(e)
        | Expr::Prime(e)
        | Expr::Unchanged(e)
        | Expr::Enabled(e)
        | Expr::Always(e)
        | Expr::Eventually(e) => expr_contains(&e.node, predicate),

        Expr::Label(label) => expr_contains(&label.body.node, predicate),

        // --- Binary (two children) ---
        Expr::And(l, r)
        | Expr::Or(l, r)
        | Expr::Implies(l, r)
        | Expr::Equiv(l, r)
        | Expr::In(l, r)
        | Expr::NotIn(l, r)
        | Expr::Subseteq(l, r)
        | Expr::Union(l, r)
        | Expr::Intersect(l, r)
        | Expr::SetMinus(l, r)
        | Expr::Eq(l, r)
        | Expr::Neq(l, r)
        | Expr::Lt(l, r)
        | Expr::Leq(l, r)
        | Expr::Gt(l, r)
        | Expr::Geq(l, r)
        | Expr::Add(l, r)
        | Expr::Sub(l, r)
        | Expr::Mul(l, r)
        | Expr::Div(l, r)
        | Expr::IntDiv(l, r)
        | Expr::Mod(l, r)
        | Expr::Pow(l, r)
        | Expr::Range(l, r)
        | Expr::LeadsTo(l, r)
        | Expr::WeakFair(l, r)
        | Expr::StrongFair(l, r)
        | Expr::FuncApply(l, r)
        | Expr::FuncSet(l, r) => {
            expr_contains(&l.node, predicate) || expr_contains(&r.node, predicate)
        }

        // --- Apply (operator + argument list) ---
        Expr::Apply(op, args) => {
            expr_contains(&op.node, predicate)
                || args.iter().any(|a| expr_contains(&a.node, predicate))
        }

        // --- Module references ---
        Expr::ModuleRef(target, _, args) => {
            let target_has = match target {
                ModuleTarget::Parameterized(_, params) => {
                    params.iter().any(|p| expr_contains(&p.node, predicate))
                }
                ModuleTarget::Chained(base) => expr_contains(&base.node, predicate),
                ModuleTarget::Named(_) => false,
            };
            target_has || args.iter().any(|a| expr_contains(&a.node, predicate))
        }
        Expr::InstanceExpr(_, subs) => subs.iter().any(|s| expr_contains(&s.to.node, predicate)),
        Expr::SubstIn(subs, body) => {
            subs.iter().any(|s| expr_contains(&s.to.node, predicate))
                || expr_contains(&body.node, predicate)
        }
        Expr::Lambda(_params, body) => expr_contains(&body.node, predicate),

        // --- Quantifiers ---
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            bounds.iter().any(|b| {
                b.domain
                    .as_ref()
                    .is_some_and(|d| expr_contains(&d.node, predicate))
            }) || expr_contains(&body.node, predicate)
        }
        Expr::Choose(bv, body) => {
            bv.domain
                .as_ref()
                .is_some_and(|d| expr_contains(&d.node, predicate))
                || expr_contains(&body.node, predicate)
        }

        // --- Sets ---
        Expr::SetEnum(elems) => elems.iter().any(|e| expr_contains(&e.node, predicate)),
        Expr::SetBuilder(expr, bounds) => {
            expr_contains(&expr.node, predicate)
                || bounds.iter().any(|b| {
                    b.domain
                        .as_ref()
                        .is_some_and(|d| expr_contains(&d.node, predicate))
                })
        }
        Expr::SetFilter(bound, pred_expr) => {
            bound
                .domain
                .as_ref()
                .is_some_and(|d| expr_contains(&d.node, predicate))
                || expr_contains(&pred_expr.node, predicate)
        }

        // --- Functions ---
        Expr::FuncDef(bounds, body) => {
            bounds.iter().any(|b| {
                b.domain
                    .as_ref()
                    .is_some_and(|d| expr_contains(&d.node, predicate))
            }) || expr_contains(&body.node, predicate)
        }
        Expr::Except(base, specs) => {
            expr_contains(&base.node, predicate)
                || specs.iter().any(|s| {
                    s.path.iter().any(|p| match p {
                        tla_core::ast::ExceptPathElement::Index(idx) => {
                            expr_contains(&idx.node, predicate)
                        }
                        tla_core::ast::ExceptPathElement::Field(_) => false,
                    }) || expr_contains(&s.value.node, predicate)
                })
        }

        // --- Records ---
        Expr::Record(fields) | Expr::RecordSet(fields) => fields
            .iter()
            .any(|(_, v)| expr_contains(&v.node, predicate)),
        Expr::RecordAccess(rec, _field) => expr_contains(&rec.node, predicate),

        // --- Tuples ---
        Expr::Tuple(elems) | Expr::Times(elems) => {
            elems.iter().any(|e| expr_contains(&e.node, predicate))
        }

        // --- Control flow ---
        Expr::If(cond, then_e, else_e) => {
            expr_contains(&cond.node, predicate)
                || expr_contains(&then_e.node, predicate)
                || expr_contains(&else_e.node, predicate)
        }
        Expr::Case(arms, other) => {
            arms.iter().any(|a| {
                expr_contains(&a.guard.node, predicate) || expr_contains(&a.body.node, predicate)
            }) || other
                .as_ref()
                .is_some_and(|e| expr_contains(&e.node, predicate))
        }
        Expr::Let(defs, body) => {
            defs.iter().any(|d| expr_contains(&d.body.node, predicate))
                || expr_contains(&body.node, predicate)
        }
    }
}

// ---------------------------------------------------------------------------
// Predicate-based scanners built on expr_contains
// ---------------------------------------------------------------------------

impl<'a> ModelChecker<'a> {
    /// Check if expression contains temporal operators (SafetySplit mode).
    ///
    /// Used by classification logic to determine whether a term should be
    /// treated as a liveness property (containing temporal operators) or a
    /// safety property (purely state-level).
    pub(in super::super) fn contains_temporal_helper(expr: &Expr) -> bool {
        expr_contains(expr, &|e| match e {
            Expr::Always(_)
            | Expr::Eventually(_)
            | Expr::LeadsTo(_, _)
            | Expr::WeakFair(_, _)
            | Expr::StrongFair(_, _) => ScanDecision::Found,
            Expr::Apply(op, _) => {
                if let Expr::Ident(name, _) = &op.node {
                    if name.starts_with("WF_") || name.starts_with("SF_") {
                        return ScanDecision::Found;
                    }
                }
                ScanDecision::Continue
            }
            _ => ScanDecision::Continue,
        })
    }

    /// Check if expression contains `ENABLED` anywhere in the tree.
    ///
    /// The safety-split code still uses this conservative scan when separating
    /// mixed safety/liveness properties. PROPERTY fast-path planning now handles
    /// state-level `ENABLED` through a dedicated eval-state-invariant lane.
    pub(super) fn contains_enabled(expr: &Expr) -> bool {
        expr_contains(expr, &|e| match e {
            Expr::Enabled(_) => ScanDecision::Found,
            _ => ScanDecision::Continue,
        })
    }
}
