// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Span-normalized expression identity: strips source-location metadata from AST
//! expressions to produce deterministic structural identity for SetPred
//! comparison, hashing, and fingerprinting.
//!
//! Part of #2955: Replaced String-based identity (clone + Debug-format entire AST
//! trees) with u64 hash-based identity. The old approach consumed ~12% of runtime
//! in GameOfLife due to `format!("{:?}", normalized.node)` calling Expr::Debug::fmt
//! recursively. The hash walks the AST in place with zero allocation.
//!
//! Extracted from `set_pred.rs` as part of #2747 decomposition.

use std::hash::{Hash, Hasher};
use tla_core::ast::{BoundPattern, BoundVar, CaseArm, ExceptPathElement, ExceptSpec, Expr};
use tla_core::Spanned;

/// Compute a deterministic structural hash of an Expr tree, ignoring all Span fields.
///
/// Two expressions that differ only in source locations (Span) produce the same hash.
/// Uses DefaultHasher (SipHash-1-3) with a fixed seed for determinism within a run.
///
/// Part of #2955: Replaces `expr_identity_sig()` which cloned the entire AST, normalized
/// spans via `SpanNormalizedExprFold`, then called `format!("{:?}", ...)`. That path
/// consumed ~12% of GameOfLife runtime through `core::fmt::write` + `Expr::Debug::fmt`.
pub(super) fn expr_identity_hash(expr: &Expr) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    hash_expr(&mut hasher, expr);
    hasher.finish()
}

/// Compute a deterministic structural hash of a BoundVar, ignoring all Span fields.
///
/// Part of #2955: Replaces `bound_var_identity_sig()` which used `format!("{:?}", ...)`
/// on name, domain, and pattern fields.
pub(super) fn bound_var_identity_hash(bv: &BoundVar) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    hash_bound_var(&mut hasher, bv);
    hasher.finish()
}

/// Hash an Expr tree recursively, skipping all Span fields.
/// Hashes the discriminant first for each variant, then delegates to typed helpers.
fn hash_expr<H: Hasher>(h: &mut H, expr: &Expr) {
    std::mem::discriminant(expr).hash(h);
    match expr {
        // Literals
        Expr::Bool(b) => b.hash(h),
        Expr::Int(n) => n.hash(h),
        Expr::String(s) => s.hash(h),
        // Names
        Expr::Ident(name, id) => {
            name.hash(h);
            id.hash(h);
        }
        Expr::StateVar(name, idx, id) => {
            name.hash(h);
            idx.hash(h);
            id.hash(h);
        }
        Expr::OpRef(s) => s.hash(h),
        // Binary operators (all hash two spanned expr children)
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
            hash_spanned_expr(h, a);
            hash_spanned_expr(h, b);
        }
        // Unary operators (all hash one spanned expr child)
        Expr::Not(a)
        | Expr::Powerset(a)
        | Expr::BigUnion(a)
        | Expr::Domain(a)
        | Expr::Prime(a)
        | Expr::Always(a)
        | Expr::Eventually(a)
        | Expr::Enabled(a)
        | Expr::Unchanged(a)
        | Expr::Neg(a) => {
            hash_spanned_expr(h, a);
        }
        // Length-prefixed spanned expr lists
        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
            hash_spanned_list(h, elems);
        }
        // Compound forms
        Expr::Apply(op, args) => hash_apply(h, op, args),
        Expr::ModuleRef(t, name, args) => hash_module_ref(h, t, name, args),
        Expr::InstanceExpr(module, subs) => hash_instance(h, module, subs),
        Expr::Label(label) => {
            label.name.node.hash(h);
            hash_spanned_expr(h, &label.body);
        }
        Expr::SubstIn(subs, body) => {
            subs.len().hash(h);
            for sub in subs {
                sub.from.node.hash(h);
                hash_spanned_expr(h, &sub.to);
            }
            hash_spanned_expr(h, body);
        }
        Expr::Lambda(params, body) => hash_lambda(h, params, body),
        Expr::Forall(bs, body) | Expr::Exists(bs, body) => hash_bounds_body(h, bs, body),
        Expr::Choose(bv, body) => {
            hash_bound_var(h, bv);
            hash_spanned_expr(h, body);
        }
        Expr::SetBuilder(e, bs) => hash_set_builder(h, e, bs),
        Expr::SetFilter(bv, pred) => {
            hash_bound_var(h, bv);
            hash_spanned_expr(h, pred);
        }
        Expr::FuncDef(bs, body) => hash_bounds_body(h, bs, body),
        Expr::Except(base, specs) => hash_except(h, base, specs),
        Expr::Record(fields) | Expr::RecordSet(fields) => hash_record_fields(h, fields),
        Expr::RecordAccess(rec, field) => {
            hash_spanned_expr(h, rec);
            field.name.node.hash(h);
        }
        Expr::If(c, t, e) => {
            hash_spanned_expr(h, c);
            hash_spanned_expr(h, t);
            hash_spanned_expr(h, e);
        }
        Expr::Case(arms, default) => hash_case(h, arms, default),
        Expr::Let(defs, body) => hash_let(h, defs, body),
    }
}

// === Inline helpers for common patterns ===

/// Hash a Spanned<Expr>, ignoring the Span.
#[inline]
fn hash_spanned_expr<H: Hasher>(h: &mut H, expr: &Spanned<Expr>) {
    hash_expr(h, &expr.node);
}

/// Hash a length-prefixed list of spanned exprs.
#[inline]
fn hash_spanned_list<H: Hasher>(h: &mut H, elems: &[Spanned<Expr>]) {
    elems.len().hash(h);
    for e in elems {
        hash_spanned_expr(h, e);
    }
}

/// Hash bound variables + body (Forall, Exists, FuncDef).
fn hash_bounds_body<H: Hasher>(h: &mut H, bounds: &[BoundVar], body: &Spanned<Expr>) {
    bounds.len().hash(h);
    for bv in bounds {
        hash_bound_var(h, bv);
    }
    hash_spanned_expr(h, body);
}

// === Compound form helpers ===

fn hash_apply<H: Hasher>(h: &mut H, op: &Spanned<Expr>, args: &[Spanned<Expr>]) {
    hash_spanned_expr(h, op);
    hash_spanned_list(h, args);
}

fn hash_module_ref<H: Hasher>(
    h: &mut H,
    target: &tla_core::ast::ModuleTarget,
    name: &str,
    args: &[Spanned<Expr>],
) {
    hash_module_target(h, target);
    name.hash(h);
    hash_spanned_list(h, args);
}

fn hash_instance<H: Hasher>(h: &mut H, module: &str, subs: &[tla_core::ast::Substitution]) {
    module.hash(h);
    subs.len().hash(h);
    for sub in subs {
        sub.from.node.hash(h);
        hash_spanned_expr(h, &sub.to);
    }
}

fn hash_lambda<H: Hasher>(h: &mut H, params: &[Spanned<String>], body: &Spanned<Expr>) {
    params.len().hash(h);
    for p in params {
        p.node.hash(h);
    }
    hash_spanned_expr(h, body);
}

fn hash_set_builder<H: Hasher>(h: &mut H, expr: &Spanned<Expr>, bounds: &[BoundVar]) {
    hash_spanned_expr(h, expr);
    bounds.len().hash(h);
    for bv in bounds {
        hash_bound_var(h, bv);
    }
}

fn hash_except<H: Hasher>(h: &mut H, base: &Spanned<Expr>, specs: &[ExceptSpec]) {
    hash_spanned_expr(h, base);
    specs.len().hash(h);
    for spec in specs {
        hash_except_spec(h, spec);
    }
}

fn hash_record_fields<H: Hasher>(h: &mut H, fields: &[(Spanned<String>, Spanned<Expr>)]) {
    fields.len().hash(h);
    for (name, val) in fields {
        name.node.hash(h);
        hash_spanned_expr(h, val);
    }
}

fn hash_case<H: Hasher>(h: &mut H, arms: &[CaseArm], default: &Option<Box<Spanned<Expr>>>) {
    arms.len().hash(h);
    for arm in arms {
        hash_case_arm(h, arm);
    }
    default.is_some().hash(h);
    if let Some(d) = default {
        hash_spanned_expr(h, d);
    }
}

fn hash_let<H: Hasher>(h: &mut H, defs: &[tla_core::ast::OperatorDef], body: &Spanned<Expr>) {
    defs.len().hash(h);
    for def in defs {
        hash_operator_def(h, def);
    }
    hash_spanned_expr(h, body);
}

// === Structural helpers ===

/// Hash a BoundVar, ignoring Span fields.
fn hash_bound_var<H: Hasher>(h: &mut H, bv: &BoundVar) {
    bv.name.node.hash(h);
    bv.domain.is_some().hash(h);
    if let Some(domain) = &bv.domain {
        hash_spanned_expr(h, domain);
    }
    bv.pattern.is_some().hash(h);
    if let Some(pattern) = &bv.pattern {
        match pattern {
            BoundPattern::Var(v) => {
                0u8.hash(h);
                v.node.hash(h);
            }
            BoundPattern::Tuple(vs) => {
                1u8.hash(h);
                vs.len().hash(h);
                for v in vs {
                    v.node.hash(h);
                }
            }
        }
    }
}

/// Hash a ModuleTarget, ignoring Span fields.
fn hash_module_target<H: Hasher>(h: &mut H, target: &tla_core::ast::ModuleTarget) {
    use tla_core::ast::ModuleTarget;
    std::mem::discriminant(target).hash(h);
    match target {
        ModuleTarget::Named(name) => name.hash(h),
        ModuleTarget::Parameterized(name, args) => {
            name.hash(h);
            hash_spanned_list(h, args);
        }
        ModuleTarget::Chained(base) => hash_spanned_expr(h, base),
    }
}

/// Hash a CaseArm, ignoring Span fields.
#[inline]
fn hash_case_arm<H: Hasher>(h: &mut H, arm: &CaseArm) {
    hash_spanned_expr(h, &arm.guard);
    hash_spanned_expr(h, &arm.body);
}

/// Hash an OperatorDef, ignoring Span fields.
fn hash_operator_def<H: Hasher>(h: &mut H, def: &tla_core::ast::OperatorDef) {
    def.name.node.hash(h);
    def.params.len().hash(h);
    for p in &def.params {
        p.name.node.hash(h);
        p.arity.hash(h);
    }
    hash_spanned_expr(h, &def.body);
    def.local.hash(h);
    def.is_recursive.hash(h);
}

/// Hash an ExceptSpec, ignoring Span fields.
fn hash_except_spec<H: Hasher>(h: &mut H, spec: &ExceptSpec) {
    spec.path.len().hash(h);
    for elem in &spec.path {
        match elem {
            ExceptPathElement::Index(e) => {
                0u8.hash(h);
                hash_spanned_expr(h, e);
            }
            ExceptPathElement::Field(f) => {
                1u8.hash(h);
                f.name.node.hash(h);
            }
        }
    }
    hash_spanned_expr(h, &spec.value);
}
