// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! INSTANCE resolution and substitution composition.
//!
//! Contains `get_instance_info`, `compose_substitutions`, `subst_in_instance_info`,
//! and `apply_substitutions`.
//!
//! Part of #1643 (module_ref.rs decomposition).

use super::super::super::{EvalCtx, EvalError, EvalResult, InstanceInfo};
use super::super::module_ref_chained::instance_info_from_substituted_expr;
use tla_core::ast::{Expr, Substitution};
use tla_core::{Span, Spanned};

/// Helper to get InstanceInfo from instance name and operator name
pub(crate) fn get_instance_info(
    ctx: &EvalCtx,
    instance_name: &str,
    op_name: &str,
    span: Option<Span>,
) -> EvalResult<InstanceInfo> {
    // Check if the "instance" is actually an operator that defines an instance
    if let Some(def) = ctx.get_op(instance_name) {
        if let Expr::InstanceExpr(module_name, substitutions) = &def.body.node {
            // If we're already evaluating inside an instance, compose this instance's
            // substitutions through the outer instance's substitutions.
            let effective_instance_subs =
                compose_substitutions(substitutions, ctx.instance_substitutions());

            // Now look up op_name in this module - it should be an InstanceExpr too
            let op_def = ctx
                .get_instance_op(module_name, op_name)
                .ok_or_else(|| EvalError::UndefinedOp {
                    name: format!("{instance_name}!{op_name}"),
                    span,
                })?
                .clone();

            // Part of #3056 Phase B: SubstIn wrapping instead of eager rewriting.
            let mut info = subst_in_instance_info(
                &op_def.body,
                &effective_instance_subs,
                instance_name,
                op_name,
                span,
            )?;
            info.substitutions = ctx
                .compute_effective_instance_substitutions(&info.module_name, &info.substitutions);
            return Ok(info);
        }
    }

    // Try looking up as a registered instance
    if let Some(info) = ctx.get_instance(instance_name) {
        let effective_instance_subs =
            compose_substitutions(&info.substitutions, ctx.instance_substitutions());

        let op_def = ctx
            .get_instance_op(&info.module_name, op_name)
            .ok_or_else(|| EvalError::UndefinedOp {
                name: format!("{instance_name}!{op_name}"),
                span,
            })?
            .clone();

        // Part of #3056 Phase B: SubstIn wrapping instead of eager rewriting.
        let mut info = subst_in_instance_info(
            &op_def.body,
            &effective_instance_subs,
            instance_name,
            op_name,
            span,
        )?;
        info.substitutions =
            ctx.compute_effective_instance_substitutions(&info.module_name, &info.substitutions);
        return Ok(info);
    }

    Err(EvalError::UndefinedOp {
        name: format!("{instance_name}!{op_name}"),
        span,
    })
}

/// Compose instance substitutions through nested INSTANCE chains (TLC `Subst.compose()`).
pub fn compose_substitutions(
    inner_subs: &[Substitution],
    outer_subs: Option<&[Substitution]>,
) -> Vec<Substitution> {
    let Some(outer_subs) = outer_subs else {
        return inner_subs.to_vec();
    };
    if outer_subs.is_empty() {
        return inner_subs.to_vec();
    }

    // TLC composes substitutions through nested instances by:
    // 1) translating inner substitution RHS into the outer context, and
    // 2) inheriting any outer substitutions not overridden by the inner instance.
    let mut combined = Vec::with_capacity(inner_subs.len() + outer_subs.len());
    let mut overridden: std::collections::HashSet<&str> = std::collections::HashSet::new();

    for sub in inner_subs {
        overridden.insert(sub.from.node.as_str());
        combined.push(Substitution {
            from: sub.from.clone(),
            to: apply_substitutions(&sub.to, outer_subs),
        });
    }

    for sub in outer_subs {
        if overridden.contains(sub.from.node.as_str()) {
            continue;
        }
        combined.push(sub.clone());
    }

    combined
}

/// Part of #3056 Phase B: Wrap operator body in SubstIn and extract InstanceInfo.
fn subst_in_instance_info(
    body: &Spanned<Expr>,
    subs: &[Substitution],
    instance_name: &str,
    op_name: &str,
    span: Option<Span>,
) -> EvalResult<InstanceInfo> {
    let wrapped = Spanned::new(
        Expr::SubstIn(subs.to_vec(), Box::new(body.clone())),
        body.span,
    );
    // outer_subs=None: SubstIn wrapping carries the subs; no separate outer composition.
    instance_info_from_substituted_expr(
        &wrapped,
        None,
        format!("{instance_name}!{op_name} is not an instance definition"),
        span,
    )
}

/// Apply substitutions to an expression (INSTANCE ... WITH lhs <- rhs).
pub fn apply_substitutions(expr: &Spanned<Expr>, subs: &[Substitution]) -> Spanned<Expr> {
    tla_core::apply_substitutions_v(expr, subs)
}
