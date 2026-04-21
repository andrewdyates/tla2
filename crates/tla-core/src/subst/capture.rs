// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Capture checking for substitution safety in TLA+ expressions.
//!
//! Provides functions to determine whether substituting a parameter with
//! an expression would cause variable capture (a free variable in the
//! replacement becoming bound by a local binder in the target expression).

use crate::ast::{ExceptPathElement, Expr, ModuleTarget};
use crate::span::Spanned;
use std::collections::HashSet;

use super::free_vars::bound_names_from_bound_var;
use super::{free_vars, BoundNameStack};

/// Check if substituting `param_name` with an expression containing `arg_free`
/// would cause variable capture in `expr`.
///
/// Returns `true` if substitution would be unsound (variable capture would occur),
/// `false` if the substitution is safe.
///
/// Variable capture occurs when a free variable in the substituted expression
/// becomes bound by a local binder in the target expression. For example:
/// ```text
/// \A x \in S : x + y     // y is free
/// ```
/// Substituting `y |-> x` (replacing `y` with `x`) is unsafe because `x` would be
/// captured by the `\A x` binder.
pub fn substitution_would_capture(
    expr: &Expr,
    param_name: &str,
    arg_free: &HashSet<String>,
    bound: &mut BoundNameStack,
) -> bool {
    match expr {
        // Literals cannot contain the parameter
        Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::OpRef(_) => false,

        // Check if this is the parameter being substituted
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            if name == param_name && !bound.contains(param_name) {
                // Would substitute here - check if any free vars would be captured
                return arg_free.iter().any(|v| bound.contains(v.as_str()));
            }
            false
        }

        // Application: check operator and arguments
        Expr::Apply(op, args) => {
            if substitution_would_capture(&op.node, param_name, arg_free, bound) {
                return true;
            }
            for a in args {
                if substitution_would_capture(&a.node, param_name, arg_free, bound) {
                    return true;
                }
            }
            false
        }

        Expr::ModuleRef(target, _, args) => {
            let target_risk = match target {
                ModuleTarget::Named(_) => false,
                ModuleTarget::Parameterized(_, params) => params
                    .iter()
                    .any(|p| substitution_would_capture(&p.node, param_name, arg_free, bound)),
                ModuleTarget::Chained(base) => {
                    substitution_would_capture(&base.node, param_name, arg_free, bound)
                }
            };
            target_risk
                || args
                    .iter()
                    .any(|a| substitution_would_capture(&a.node, param_name, arg_free, bound))
        }

        Expr::InstanceExpr(_, subs) => subs
            .iter()
            .any(|s| substitution_would_capture(&s.to.node, param_name, arg_free, bound)),
        Expr::SubstIn(subs, body) => {
            subs.iter()
                .any(|s| substitution_would_capture(&s.to.node, param_name, arg_free, bound))
                || substitution_would_capture(&body.node, param_name, arg_free, bound)
        }

        Expr::Lambda(params, body) => {
            let mark = bound.mark();
            bound.push_names(params.iter().map(|p| p.node.clone()));
            let risk = substitution_would_capture(&body.node, param_name, arg_free, bound);
            bound.pop_to(mark);
            risk
        }
        Expr::Label(label) => {
            substitution_would_capture(&label.body.node, param_name, arg_free, bound)
        }

        // Binary operators
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
        | Expr::Range(a, b)
        | Expr::FuncSet(a, b) => {
            substitution_would_capture(&a.node, param_name, arg_free, bound)
                || substitution_would_capture(&b.node, param_name, arg_free, bound)
        }

        // Unary operators
        Expr::Not(a)
        | Expr::Prime(a)
        | Expr::Always(a)
        | Expr::Eventually(a)
        | Expr::Enabled(a)
        | Expr::Unchanged(a)
        | Expr::Powerset(a)
        | Expr::BigUnion(a)
        | Expr::Domain(a)
        | Expr::Neg(a) => substitution_would_capture(&a.node, param_name, arg_free, bound),

        Expr::If(cond, then_e, else_e) => {
            substitution_would_capture(&cond.node, param_name, arg_free, bound)
                || substitution_would_capture(&then_e.node, param_name, arg_free, bound)
                || substitution_would_capture(&else_e.node, param_name, arg_free, bound)
        }

        Expr::Case(arms, other) => {
            for arm in arms {
                if substitution_would_capture(&arm.guard.node, param_name, arg_free, bound)
                    || substitution_would_capture(&arm.body.node, param_name, arg_free, bound)
                {
                    return true;
                }
            }
            if let Some(default) = other {
                return substitution_would_capture(&default.node, param_name, arg_free, bound);
            }
            false
        }

        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) | Expr::FuncDef(bounds, body) => {
            // Check domains first (outside binding scope)
            for b in bounds {
                if let Some(domain) = &b.domain {
                    if substitution_would_capture(&domain.node, param_name, arg_free, bound) {
                        return true;
                    }
                }
            }
            // Check body with bindings in scope
            let mark = bound.mark();
            bound.push_names(bounds.iter().flat_map(bound_names_from_bound_var));
            let risk = substitution_would_capture(&body.node, param_name, arg_free, bound);
            bound.pop_to(mark);
            risk
        }

        Expr::Choose(bound_var, body) => {
            if let Some(domain) = &bound_var.domain {
                if substitution_would_capture(&domain.node, param_name, arg_free, bound) {
                    return true;
                }
            }
            let mark = bound.mark();
            bound.push_names(bound_names_from_bound_var(bound_var));
            let risk = substitution_would_capture(&body.node, param_name, arg_free, bound);
            bound.pop_to(mark);
            risk
        }

        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => elems
            .iter()
            .any(|e| substitution_would_capture(&e.node, param_name, arg_free, bound)),

        Expr::SetBuilder(body, bounds) => {
            for b in bounds {
                if let Some(domain) = &b.domain {
                    if substitution_would_capture(&domain.node, param_name, arg_free, bound) {
                        return true;
                    }
                }
            }
            let mark = bound.mark();
            bound.push_names(bounds.iter().flat_map(bound_names_from_bound_var));
            let risk = substitution_would_capture(&body.node, param_name, arg_free, bound);
            bound.pop_to(mark);
            risk
        }

        Expr::SetFilter(bound_var, pred) => {
            if let Some(domain) = &bound_var.domain {
                if substitution_would_capture(&domain.node, param_name, arg_free, bound) {
                    return true;
                }
            }
            let mark = bound.mark();
            bound.push_names(bound_names_from_bound_var(bound_var));
            let risk = substitution_would_capture(&pred.node, param_name, arg_free, bound);
            bound.pop_to(mark);
            risk
        }

        Expr::FuncApply(func, arg) => {
            substitution_would_capture(&func.node, param_name, arg_free, bound)
                || substitution_would_capture(&arg.node, param_name, arg_free, bound)
        }

        Expr::Except(base, specs) => {
            if substitution_would_capture(&base.node, param_name, arg_free, bound) {
                return true;
            }
            for spec in specs {
                for elem in &spec.path {
                    if let ExceptPathElement::Index(idx_expr) = elem {
                        if substitution_would_capture(&idx_expr.node, param_name, arg_free, bound) {
                            return true;
                        }
                    }
                }
                if substitution_would_capture(&spec.value.node, param_name, arg_free, bound) {
                    return true;
                }
            }
            false
        }

        Expr::Record(fields) => fields
            .iter()
            .any(|(_, v)| substitution_would_capture(&v.node, param_name, arg_free, bound)),

        Expr::RecordAccess(r, _) => {
            substitution_would_capture(&r.node, param_name, arg_free, bound)
        }

        Expr::RecordSet(fields) => fields
            .iter()
            .any(|(_, v)| substitution_would_capture(&v.node, param_name, arg_free, bound)),

        Expr::Let(defs, body) => {
            let mark = bound.mark();
            bound.push_names(defs.iter().map(|d| d.name.node.clone()));

            for def in defs {
                let def_mark = bound.mark();
                bound.push_names(def.params.iter().map(|p| p.name.node.clone()));
                if substitution_would_capture(&def.body.node, param_name, arg_free, bound) {
                    return true;
                }
                bound.pop_to(def_mark);
            }

            let risk = substitution_would_capture(&body.node, param_name, arg_free, bound);
            bound.pop_to(mark);
            risk
        }
    }
}

/// Check if inlining an operator definition with given arguments would cause variable capture.
///
/// Returns `true` if the substitution is safe (no capture), `false` if capture would occur.
///
/// This is the primary API for checking whether operator inlining is safe.
pub fn inlining_is_capture_safe(def: &crate::ast::OperatorDef, args: &[Spanned<Expr>]) -> bool {
    if def.params.len() != args.len() {
        // Arity mismatch - caller should handle this separately
        return true;
    }

    for (param, arg) in def.params.iter().zip(args.iter()) {
        if param.arity != 0 {
            // Higher-order parameters are not value-inlined
            continue;
        }
        let arg_free = free_vars(&arg.node);
        if arg_free.is_empty() {
            // No free vars means no risk of capture
            continue;
        }
        let mut bound = BoundNameStack::default();
        if substitution_would_capture(
            &def.body.node,
            param.name.node.as_str(),
            &arg_free,
            &mut bound,
        ) {
            return false;
        }
    }
    true
}
