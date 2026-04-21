// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Value-to-Expr conversion and AST walking helpers for z4 enumeration.

use num_bigint::BigInt;
use num_traits::ToPrimitive;
use tla_core::ast::{Expr, ModuleTarget};
use tla_core::Span;
use tla_core::Spanned;

use crate::eval::EvalCtx;
use crate::Value;

/// Convert a `Value` into an `Expr` (with spans) that is safe to pass through the z4 translation path.
///
/// This intentionally only supports a narrow subset of `Value` variants that map cleanly onto
/// expression forms supported by `tla-z4` translation (notably set membership domains).
///
/// Part of #251 / #515: Safe constant pre-evaluation gating.
pub(super) fn try_value_to_z4_spanned_expr(value: &Value, span: Span) -> Option<Spanned<Expr>> {
    // Avoid materializing enormous SetEnum disjunctions during pre-evaluation.
    const MAX_Z4_SETENUM_ELEMS: usize = 5_000;

    let node = match value {
        Value::Bool(b) => Expr::Bool(*b),
        Value::SmallInt(n) => Expr::Int(BigInt::from(*n)),
        Value::Int(n) => Expr::Int(n.as_ref().clone()),
        Value::String(s) => Expr::String(s.to_string()),
        Value::Interval(interval) => Expr::Range(
            Box::new(Spanned::new(Expr::Int(interval.low().clone()), span)),
            Box::new(Spanned::new(Expr::Int(interval.high().clone()), span)),
        ),
        Value::Tuple(elems) => {
            let exprs: Vec<Spanned<Expr>> = elems
                .iter()
                .map(|e| try_value_to_z4_spanned_expr(e, span))
                .collect::<Option<Vec<_>>>()?;
            Expr::Tuple(exprs)
        }
        Value::Seq(elems) => {
            let exprs: Vec<Spanned<Expr>> = elems
                .iter()
                .map(|e| try_value_to_z4_spanned_expr(e, span))
                .collect::<Option<Vec<_>>>()?;
            Expr::Tuple(exprs)
        }
        // Encode sequence-shaped functions as tuples so membership/indexing still translates.
        Value::Func(f) => {
            if f.domain_len() > MAX_Z4_SETENUM_ELEMS {
                return None;
            }
            let mut tuple_elems: Vec<Spanned<Expr>> = Vec::with_capacity(f.domain_len());
            for (i, (k, v)) in f.mapping_iter().enumerate() {
                let expected = (i + 1) as i64;
                let ok = match k {
                    Value::SmallInt(n) => *n == expected,
                    Value::Int(n) => n.to_i64() == Some(expected),
                    _ => false,
                };
                if !ok {
                    return None;
                }
                tuple_elems.push(try_value_to_z4_spanned_expr(v, span)?);
            }
            Expr::Tuple(tuple_elems)
        }
        Value::IntFunc(f) => {
            let f = f.as_ref();
            let len = tla_eval::interval_len_for_bounds_check(f.min(), f.max());
            if f.min() != 1 || len != f.values().len() || len > MAX_Z4_SETENUM_ELEMS {
                return None;
            }
            let exprs: Vec<Spanned<Expr>> = f
                .values()
                .iter()
                .map(|e| try_value_to_z4_spanned_expr(e, span))
                .collect::<Option<Vec<_>>>()?;
            Expr::Tuple(exprs)
        }
        Value::Set(set) => {
            if set.len() > MAX_Z4_SETENUM_ELEMS {
                return None;
            }
            let exprs: Vec<Spanned<Expr>> = set
                .iter()
                .map(|e| try_value_to_z4_spanned_expr(e, span))
                .collect::<Option<Vec<_>>>()?;
            Expr::SetEnum(exprs)
        }
        // Materialize small finite lazy-set values into SetEnum for z4-safe membership domains.
        Value::Subset(_)
        | Value::FuncSet(_)
        | Value::RecordSet(_)
        | Value::TupleSet(_)
        | Value::SetCup(_)
        | Value::SetCap(_)
        | Value::SetDiff(_)
        | Value::KSubset(_)
        | Value::BigUnion(_) => {
            let len = value.set_len()?;
            if len > BigInt::from(MAX_Z4_SETENUM_ELEMS) {
                return None;
            }
            let set = value.to_sorted_set()?;
            let exprs: Vec<Spanned<Expr>> = set
                .iter()
                .map(|e| try_value_to_z4_spanned_expr(e, span))
                .collect::<Option<Vec<_>>>()?;
            Expr::SetEnum(exprs)
        }
        _ => return None,
    };

    Some(Spanned::new(node, span))
}

pub(super) fn collect_referenced_zero_arg_ops(
    expr: &Spanned<Expr>,
    ctx: &EvalCtx,
    out: &mut std::collections::BTreeSet<String>,
) {
    if let Expr::Ident(name, _) = &expr.node {
        if let Some(def) = ctx.shared().ops.get(name) {
            if def.params.is_empty() {
                out.insert(name.clone());
            }
        }
    }

    match &expr.node {
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _)
        | Expr::OpRef(_) => {}

        Expr::Apply(op, args) => {
            collect_referenced_zero_arg_ops(op, ctx, out);
            for a in args {
                collect_referenced_zero_arg_ops(a, ctx, out);
            }
        }
        Expr::ModuleRef(target, _, args) => {
            match target {
                ModuleTarget::Named(_) => {}
                ModuleTarget::Parameterized(_, params) => {
                    for p in params {
                        collect_referenced_zero_arg_ops(p, ctx, out);
                    }
                }
                ModuleTarget::Chained(base) => {
                    collect_referenced_zero_arg_ops(base, ctx, out);
                }
            }

            for a in args {
                collect_referenced_zero_arg_ops(a, ctx, out);
            }
        }
        Expr::InstanceExpr(_, subs) => {
            for sub in subs {
                collect_referenced_zero_arg_ops(&sub.to, ctx, out);
            }
        }
        Expr::Lambda(_, body) => {
            collect_referenced_zero_arg_ops(body, ctx, out);
        }
        Expr::Label(label) => {
            collect_referenced_zero_arg_ops(&label.body, ctx, out);
        }
        Expr::SubstIn(subs, body) => {
            for sub in subs {
                collect_referenced_zero_arg_ops(&sub.to, ctx, out);
            }
            collect_referenced_zero_arg_ops(body, ctx, out);
        }

        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::LeadsTo(a, b)
        | Expr::WeakFair(a, b)
        | Expr::StrongFair(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::Lt(a, b)
        | Expr::Leq(a, b)
        | Expr::Gt(a, b)
        | Expr::Geq(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Subseteq(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::FuncApply(a, b)
        | Expr::FuncSet(a, b)
        | Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::IntDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Pow(a, b)
        | Expr::Range(a, b) => {
            collect_referenced_zero_arg_ops(a, ctx, out);
            collect_referenced_zero_arg_ops(b, ctx, out);
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
        | Expr::Neg(a) => {
            collect_referenced_zero_arg_ops(a, ctx, out);
        }

        Expr::Forall(bvs, body)
        | Expr::Exists(bvs, body)
        | Expr::FuncDef(bvs, body)
        | Expr::SetBuilder(body, bvs) => {
            for bv in bvs {
                if let Some(domain) = &bv.domain {
                    collect_referenced_zero_arg_ops(domain, ctx, out);
                }
            }
            collect_referenced_zero_arg_ops(body, ctx, out);
        }
        Expr::Choose(bv, body) | Expr::SetFilter(bv, body) => {
            if let Some(domain) = &bv.domain {
                collect_referenced_zero_arg_ops(domain, ctx, out);
            }
            collect_referenced_zero_arg_ops(body, ctx, out);
        }

        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
            for e in elems {
                collect_referenced_zero_arg_ops(e, ctx, out);
            }
        }
        Expr::Record(fields) => {
            for (_, e) in fields {
                collect_referenced_zero_arg_ops(e, ctx, out);
            }
        }
        Expr::RecordAccess(base, _) => {
            collect_referenced_zero_arg_ops(base, ctx, out);
        }
        Expr::RecordSet(fields) => {
            for (_, domain) in fields {
                collect_referenced_zero_arg_ops(domain, ctx, out);
            }
        }

        Expr::If(c, t, e) => {
            collect_referenced_zero_arg_ops(c, ctx, out);
            collect_referenced_zero_arg_ops(t, ctx, out);
            collect_referenced_zero_arg_ops(e, ctx, out);
        }
        Expr::Case(arms, other) => {
            for arm in arms {
                collect_referenced_zero_arg_ops(&arm.guard, ctx, out);
                collect_referenced_zero_arg_ops(&arm.body, ctx, out);
            }
            if let Some(other) = other {
                collect_referenced_zero_arg_ops(other, ctx, out);
            }
        }
        Expr::Let(defs, body) => {
            for def in defs {
                collect_referenced_zero_arg_ops(&def.body, ctx, out);
            }
            collect_referenced_zero_arg_ops(body, ctx, out);
        }
        Expr::Except(base, specs) => {
            collect_referenced_zero_arg_ops(base, ctx, out);
            for spec in specs {
                for p in &spec.path {
                    if let tla_core::ast::ExceptPathElement::Index(ix) = p {
                        collect_referenced_zero_arg_ops(ix, ctx, out);
                    }
                }
                collect_referenced_zero_arg_ops(&spec.value, ctx, out);
            }
        }
    }
}

/// Extract variable name from an expression that represents a variable reference.
/// Works for both `Ident("x")` (from unit tests) and `StateVar("x", ...)` (from parser).
/// Part of #532: Handle both Ident and StateVar for heterogeneous detection.
pub(crate) fn extract_var_name(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Ident(name, _) => Some(name.clone()),
        Expr::StateVar(name, _, _) => Some(name.clone()),
        _ => None,
    }
}
