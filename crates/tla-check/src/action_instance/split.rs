// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Recursive action-instance splitting.
//!
//! Implements the TLC-style expansion of the Next relation into a flat list of
//! action instances by expanding disjunctions and bounded existentials.
//!
//! Extracted from action_instance/mod.rs to reduce file size.

use super::{ActionInstance, SplitCtx};
use crate::enumerate::{classify_iter_error_for_speculative_path, IterDomainAction};
use crate::error::EvalResult;
use crate::eval::{eval_iter_set_tlc_normalized, try_eval_const_level, EvalCtx};
use crate::value::Value;
use std::sync::Arc;
use tla_core::ast::{BoundVar, Expr, ModuleTarget};
use tla_core::Spanned;

pub(super) fn split_action_instances_rec(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    split: &SplitCtx,
    out: &mut Vec<ActionInstance>,
) -> EvalResult<()> {
    match &expr.node {
        Expr::Or(a, b) => {
            split_action_instances_rec(ctx, a, split, out)?;
            split_action_instances_rec(ctx, b, split, out)?;
        }

        // LET wrapper - transparent for splitting but must be preserved for evaluation parity.
        Expr::Let(defs, body) => {
            let mut next = split.clone();
            next.let_wrappers.push(defs.clone());
            split_action_instances_rec(ctx, body, &next, out)?;
        }

        // Bounded EXISTS: split only when all bounds have an enumerable const-level domain.
        Expr::Exists(bounds, body) => {
            let mut tmp = Vec::new();
            if try_split_exists_all_bounds(ctx, bounds, 0, body, split, &mut tmp)? {
                out.extend(tmp);
            } else {
                // If multiple bounds were flattened into a single Exists, try the reverse order as a
                // fallback. This is important for dependent domains, where later bounds may mention
                // earlier ones. If the bounds are already in spec order, the forward split succeeds
                // and we never take this path.
                if bounds.len() > 1 {
                    let mut rev = bounds.clone();
                    rev.reverse();
                    let mut tmp2 = Vec::new();
                    if try_split_exists_all_bounds(ctx, &rev, 0, body, split, &mut tmp2)? {
                        out.extend(tmp2);
                        return Ok(());
                    }
                }
                push_leaf_action(ctx, expr, split, out);
            }
        }

        // Zero-argument operator reference.
        Expr::Ident(name, _) => {
            let resolved = ctx.resolve_op_name(name.as_str());
            if let Some(def) = ctx.get_op(resolved) {
                if def.params.is_empty() && !split.op_stack.iter().any(|n| n == resolved) {
                    let mut next = split.clone();
                    next.action_name = Some(resolved.to_string());
                    next.op_stack.push(resolved.to_string());
                    split_action_instances_rec(ctx, &def.body, &next, out)?;
                    return Ok(());
                }
            }
            push_leaf_action(ctx, expr, split, out);
        }

        // Module/Instance reference: M!Op(...) or IS(x,y)!Op(...).
        //
        // Treat module refs as leaf actions, pre-binding const-level actual args
        // to operator formal params so the instance carries TLC-style bindings.
        //
        // Part of #3100: Also bind parameterized target actuals (e.g., the `7` in
        // `Z7(7)!Next`) so that `split_action_meta` can distinguish `I(1)!Next`
        // from `I(2)!Next` via binding-based provenance matching.
        Expr::ModuleRef(target, op_name, args) => {
            let Some(target_name) = module_target_simple_name(target) else {
                push_leaf_action(ctx, expr, split, out);
                return Ok(());
            };
            let Some(module_name) = resolve_instance_module_name(ctx, target_name) else {
                push_leaf_action(ctx, expr, split, out);
                return Ok(());
            };

            let resolved_op_name = ctx.resolve_op_name(op_name.as_str());
            let Some(def) = ctx.get_instance_op(&module_name, resolved_op_name) else {
                push_leaf_action(ctx, expr, split, out);
                return Ok(());
            };
            if def.params.len() != args.len() {
                push_leaf_action(ctx, expr, split, out);
                return Ok(());
            }

            // Part of #3100: Bind parameterized target actuals first.
            // For I(7)!Next, bind the target operator's formals (e.g., "n") to
            // the evaluated target actuals (e.g., 7). These bindings flow into
            // split_action_meta and allow the fairness matcher to distinguish
            // I(1)!Next from I(2)!Next.
            let ctx_with_target = if let ModuleTarget::Parameterized(tname, target_actuals) = target
            {
                if let Some(target_def) = ctx.get_op(tname) {
                    if target_def.params.len() == target_actuals.len() {
                        let mut target_values = Vec::with_capacity(target_actuals.len());
                        let mut all_const = true;
                        for arg in target_actuals {
                            if let Some(v) = try_eval_const_level(ctx, arg) {
                                target_values.push(v);
                            } else {
                                all_const = false;
                                break;
                            }
                        }
                        if all_const {
                            let target_bindings: Vec<(Arc<str>, Value)> = target_def
                                .params
                                .iter()
                                .zip(target_values)
                                .map(|(p, v)| (Arc::from(p.name.node.as_str()), v))
                                .collect();
                            Some(ctx.bind_all(target_bindings))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            };
            let base_ctx = ctx_with_target.as_ref().unwrap_or(ctx);

            // Bind operator-call actuals on top of target bindings.
            let mut values: Vec<Value> = Vec::with_capacity(args.len());
            for arg in args {
                let Some(v) = try_eval_const_level(base_ctx, arg) else {
                    push_leaf_action(ctx, expr, split, out);
                    return Ok(());
                };
                values.push(v);
            }

            let bindings: Vec<(Arc<str>, Value)> = def
                .params
                .iter()
                .zip(values)
                .map(|(param, v)| (Arc::from(param.name.node.as_str()), v))
                .collect();
            let ctx2 = base_ctx.bind_all(bindings.clone());

            let mut next = split.clone();
            next.action_name = Some(format!("{target_name}!{resolved_op_name}"));
            next.formal_bindings = bindings;
            push_leaf_action(&ctx2, expr, &next, out);
        }

        // Operator application specialization guarded by const-level arg evaluation.
        Expr::Apply(op_expr, args) => {
            let Expr::Ident(op_name, _) = &op_expr.node else {
                push_leaf_action(ctx, expr, split, out);
                return Ok(());
            };

            let resolved = ctx.resolve_op_name(op_name.as_str());
            let Some(def) = ctx.get_op(resolved) else {
                push_leaf_action(ctx, expr, split, out);
                return Ok(());
            };

            if def.params.len() != args.len() || split.op_stack.iter().any(|n| n == resolved) {
                push_leaf_action(ctx, expr, split, out);
                return Ok(());
            }

            let mut values: Vec<Value> = Vec::with_capacity(args.len());
            for arg in args {
                let Some(v) = try_eval_const_level(ctx, arg) else {
                    push_leaf_action(ctx, expr, split, out);
                    return Ok(());
                };
                values.push(v);
            }

            // Specialize: bind formals to values, then recurse into operator body.
            let bindings: Vec<(Arc<str>, Value)> = def
                .params
                .iter()
                .zip(values)
                .map(|(param, v)| (Arc::from(param.name.node.as_str()), v))
                .collect();
            let ctx2 = ctx.bind_all(bindings.clone());

            let mut next = split.clone();
            next.action_name = Some(resolved.to_string());
            next.formal_bindings = bindings;
            next.op_stack.push(resolved.to_string());
            split_action_instances_rec(&ctx2, &def.body, &next, out)?;
        }

        _ => push_leaf_action(ctx, expr, split, out),
    }
    Ok(())
}

fn push_leaf_action(
    ctx: &EvalCtx,
    expr: &Spanned<Expr>,
    split: &SplitCtx,
    out: &mut Vec<ActionInstance>,
) {
    let mut wrapped = expr.clone();
    for defs in split.let_wrappers.iter().rev() {
        let span = wrapped.span;
        wrapped = Spanned::new(Expr::Let(defs.clone(), Box::new(wrapped)), span);
    }

    let name = split.action_name.clone().or_else(|| match &expr.node {
        Expr::Ident(n, _) => Some(ctx.resolve_op_name(n.as_str()).to_string()),
        Expr::Apply(op, _) => match &op.node {
            Expr::Ident(n, _) => Some(ctx.resolve_op_name(n.as_str()).to_string()),
            _ => None,
        },
        Expr::ModuleRef(target, op, _) => match target {
            ModuleTarget::Named(t) | ModuleTarget::Parameterized(t, _) => Some(format!("{t}!{op}")),
            ModuleTarget::Chained(_) => None,
        },
        _ => None,
    });

    out.push(ActionInstance {
        name,
        expr: wrapped,
        bindings: ctx.get_local_bindings(),
        formal_bindings: split.formal_bindings.clone(),
    });
}

fn try_split_exists_all_bounds(
    ctx: &EvalCtx,
    bounds: &[BoundVar],
    idx: usize,
    body: &Spanned<Expr>,
    split: &SplitCtx,
    out: &mut Vec<ActionInstance>,
) -> EvalResult<bool> {
    if idx >= bounds.len() {
        split_action_instances_rec(ctx, body, split, out)?;
        return Ok(true);
    }

    if bounds[idx].pattern.is_some() {
        return Ok(false);
    }

    let domain_expr = match bounds[idx].domain.as_ref() {
        Some(e) => e,
        None => return Ok(false),
    };
    let domain_val = match try_eval_const_level(ctx, domain_expr) {
        Some(v) => v,
        None => return Ok(false),
    };
    // Part of #1828: use eval_iter_set for SetPred-aware iteration.
    // Part of #1886: discriminate "not enumerable" (defer) from fatal eval errors.
    // Part of #2987: use TLC-normalized ordering for BFS parity.
    let domain_elems: Vec<Value> =
        match eval_iter_set_tlc_normalized(ctx, &domain_val, Some(domain_expr.span)) {
            Ok(iter) => iter.collect(),
            Err(ref e)
                if classify_iter_error_for_speculative_path(e) == IterDomainAction::Defer =>
            {
                return Ok(false);
            }
            Err(e) => return Err(e),
        };

    let name: Arc<str> = Arc::from(bounds[idx].name.node.as_str());
    for v in domain_elems {
        let ctx2 = ctx.bind_local(Arc::clone(&name), v);
        if !try_split_exists_all_bounds(&ctx2, bounds, idx + 1, body, split, out)? {
            return Ok(false);
        }
    }

    Ok(true)
}

fn module_target_simple_name(target: &ModuleTarget) -> Option<&str> {
    match target {
        ModuleTarget::Named(name) => Some(name.as_str()),
        ModuleTarget::Parameterized(name, _) => Some(name.as_str()),
        ModuleTarget::Chained(_) => None,
    }
}

fn resolve_instance_module_name(ctx: &EvalCtx, instance_name: &str) -> Option<String> {
    if let Some(info) = ctx.get_instance(instance_name) {
        return Some(info.module_name.clone());
    }
    let def = ctx.get_op(instance_name)?;
    let Expr::InstanceExpr(module_name, _subs) = &def.body.node else {
        return None;
    };
    Some(module_name.clone())
}
