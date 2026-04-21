// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared PROPERTY planning for BFS promotion and safety-temporal fast paths.

use crate::check::{expr_contains, ScanDecision};
use crate::eval::EvalCtx;
use crate::liveness::{AstToLive, ExprLevel};
use rustc_hash::FxHashMap;
use tla_core::ast::{Expr, ModuleTarget, OperatorDef};
use tla_core::Spanned;

use super::instance_qualify::qualify_instance_ops;
use super::{contains_module_ref, contains_temporal_standalone, flatten_and_terms_standalone};

/// Shared semantic buckets for PROPERTY terms.
///
/// The bucket shapes intentionally mirror the existing execution lanes so
/// adapters can preserve current behavior while sharing one semantic plan.
pub(crate) enum PlannedPropertyTerm {
    Init(Spanned<Expr>),
    StateCompiled(Spanned<Expr>),
    StateEval(Spanned<Expr>),
    ActionCompiled(Spanned<Expr>),
    ActionEval(Spanned<Expr>),
    Liveness(Spanned<Expr>),
}

/// Shared PROPERTY plan consumed by BFS preparation and safety-temporal logic.
pub(crate) struct PlannedProperty {
    pub(crate) property: String,
    pub(crate) terms: Vec<PlannedPropertyTerm>,
}

pub(crate) fn wrap_with_let_defs(
    defs: &Option<Vec<OperatorDef>>,
    expr: Spanned<Expr>,
) -> Spanned<Expr> {
    match defs {
        Some(defs) => Spanned::new(Expr::Let(defs.clone(), Box::new(expr.clone())), expr.span),
        None => expr,
    }
}

pub(crate) fn contains_enabled_standalone(expr: &Expr) -> bool {
    expr_contains(expr, &|e| match e {
        Expr::Enabled(_) => ScanDecision::Found,
        _ => ScanDecision::Continue,
    })
}

fn is_real_action_subscript(ctx: &EvalCtx, expr: &Spanned<Expr>) -> bool {
    ctx.is_action_subscript_span(expr.span)
}

pub(crate) fn plan_property_terms(
    ctx: &EvalCtx,
    op_defs: &FxHashMap<String, OperatorDef>,
    prop_name: &str,
) -> Option<PlannedProperty> {
    let def = op_defs.get(prop_name)?;

    let (let_defs, prop_body) = match &def.body.node {
        Expr::Let(defs, inner) => (Some(defs.clone()), (**inner).clone()),
        Expr::ModuleRef(target, op_name, args) => {
            (None, resolve_module_ref_body(ctx, target, op_name, args)?)
        }
        _ => (None, def.body.clone()),
    };

    let mut split_terms = Vec::new();
    flatten_and_terms_standalone(&prop_body, &mut split_terms);

    let converter = AstToLive::new();
    let mut planned_terms = Vec::new();

    for term in split_terms {
        match &term.node {
            Expr::Always(inner) => {
                let body = wrap_with_let_defs(&let_defs, (**inner).clone());
                let inner_level = converter.get_level_with_ctx(ctx, &inner.node);
                let real_action_subscript = is_real_action_subscript(ctx, inner);

                // Real `[A]_v` / `<<A>>_v` syntax remains an action property even when
                // the lowered `A \/ UNCHANGED v` body is semantically state-level
                // (for example `[][decision = none]_<<decision>>` in FastPaxos).
                if real_action_subscript && !matches!(inner_level, ExprLevel::Temporal) {
                    if contains_module_ref(&inner.node) || contains_enabled_standalone(&inner.node)
                    {
                        planned_terms.push(PlannedPropertyTerm::ActionEval(body));
                    } else {
                        planned_terms.push(PlannedPropertyTerm::ActionCompiled(body));
                    }
                    continue;
                }

                if contains_temporal_standalone(&inner.node) {
                    if matches!(inner_level, ExprLevel::Constant | ExprLevel::State)
                        && contains_enabled_standalone(&inner.node)
                    {
                        planned_terms.push(PlannedPropertyTerm::StateEval(body));
                    } else {
                        planned_terms.push(PlannedPropertyTerm::Liveness(wrap_with_let_defs(
                            &let_defs,
                            term.clone(),
                        )));
                    }
                    continue;
                }

                match inner_level {
                    ExprLevel::Constant | ExprLevel::State => {
                        planned_terms.push(PlannedPropertyTerm::StateCompiled(body));
                    }
                    ExprLevel::Action => {
                        if !real_action_subscript {
                            planned_terms.push(PlannedPropertyTerm::Liveness(wrap_with_let_defs(
                                &let_defs,
                                term.clone(),
                            )));
                        } else if contains_module_ref(&inner.node) {
                            planned_terms.push(PlannedPropertyTerm::ActionEval(body));
                        } else {
                            planned_terms.push(PlannedPropertyTerm::ActionCompiled(body));
                        }
                    }
                    ExprLevel::Temporal => {
                        planned_terms.push(PlannedPropertyTerm::Liveness(wrap_with_let_defs(
                            &let_defs,
                            term.clone(),
                        )));
                    }
                }
            }
            _ => {
                if contains_temporal_standalone(&term.node) {
                    planned_terms.push(PlannedPropertyTerm::Liveness(wrap_with_let_defs(
                        &let_defs,
                        term.clone(),
                    )));
                    continue;
                }

                match converter.get_level_with_ctx(ctx, &term.node) {
                    ExprLevel::Constant | ExprLevel::State => {
                        planned_terms.push(PlannedPropertyTerm::Init(wrap_with_let_defs(
                            &let_defs,
                            term.clone(),
                        )));
                    }
                    ExprLevel::Action | ExprLevel::Temporal => {
                        planned_terms.push(PlannedPropertyTerm::Liveness(wrap_with_let_defs(
                            &let_defs,
                            term.clone(),
                        )));
                    }
                }
            }
        }
    }

    Some(PlannedProperty {
        property: prop_name.to_string(),
        terms: planned_terms,
    })
}

/// Resolve a ModuleRef property body for classification.
///
/// Returns the operator body with module-local references qualified as
/// ModuleRef nodes. Substitutions are not applied here; the eval path handles
/// them when it resolves the ModuleRef nodes during evaluation.
fn resolve_module_ref_body(
    ctx: &EvalCtx,
    target: &ModuleTarget,
    op_name: &str,
    args: &[Spanned<Expr>],
) -> Option<Spanned<Expr>> {
    if !args.is_empty() {
        return None;
    }
    let ModuleTarget::Named(instance_name) = target else {
        return None;
    };
    let info = ctx.get_instance(instance_name)?;
    let op_def = ctx.get_instance_op(&info.module_name, op_name)?;
    if !op_def.params.is_empty() {
        return None;
    }
    let qualified = qualify_instance_ops(ctx, target, &info.module_name, op_def.body.clone());
    Some(qualified)
}
