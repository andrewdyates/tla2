// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::fallback::eval_action_leaves_fallback;
use super::{eval_bool_expr_with_entry_mode, InlineLeafEntryMode};
use crate::error::{EvalError, EvalResult};
use crate::eval::EvalCtx;
use crate::liveness::live_expr::LiveExpr;
use crate::state::{ArrayState, Fingerprint};

pub(super) fn action_leaf_preserves_batch_boundary(expr: &LiveExpr) -> bool {
    match expr {
        LiveExpr::Bool(_) | LiveExpr::ActionPred { .. } => true,
        LiveExpr::StateChanged {
            subscript: None, ..
        } => true,
        LiveExpr::Not(inner)
        | LiveExpr::Always(inner)
        | LiveExpr::Eventually(inner)
        | LiveExpr::Next(inner) => action_leaf_preserves_batch_boundary(inner),
        LiveExpr::And(parts) | LiveExpr::Or(parts) => {
            parts.iter().all(action_leaf_preserves_batch_boundary)
        }
        LiveExpr::Enabled { .. }
        | LiveExpr::StatePred { .. }
        | LiveExpr::StateChanged {
            subscript: Some(_), ..
        } => false,
    }
}

fn eval_action_leaf_array(
    ctx: &mut EvalCtx,
    expr: &LiveExpr,
    current_fp: Fingerprint,
    current_array: &ArrayState,
    next_fp: Fingerprint,
    next_array: &ArrayState,
    entry_mode: InlineLeafEntryMode,
) -> EvalResult<bool> {
    match expr {
        LiveExpr::Bool(b) => Ok(*b),
        LiveExpr::ActionPred { expr, bindings, .. } => match bindings {
            Some(chain) => {
                let eval_ctx = ctx.with_liveness_bindings(chain);
                eval_bool_expr_with_entry_mode(&eval_ctx, expr, entry_mode)
            }
            None => eval_bool_expr_with_entry_mode(ctx, expr, entry_mode),
        },
        LiveExpr::StateChanged {
            subscript,
            bindings,
            tag,
        } => match subscript.as_ref() {
            Some(sub_expr) => super::super::checker::eval_subscript_changed_array_cached(
                ctx,
                current_fp,
                current_array,
                next_fp,
                next_array,
                sub_expr,
                bindings.as_ref(),
                *tag,
            ),
            None => Ok(current_fp != next_fp),
        },
        LiveExpr::Not(inner) => Ok(!eval_action_leaf_array(
            ctx,
            inner,
            current_fp,
            current_array,
            next_fp,
            next_array,
            entry_mode,
        )?),
        LiveExpr::And(parts) => {
            for part in parts {
                if !eval_action_leaf_array(
                    ctx,
                    part,
                    current_fp,
                    current_array,
                    next_fp,
                    next_array,
                    entry_mode,
                )? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        LiveExpr::Or(parts) => {
            for part in parts {
                if eval_action_leaf_array(
                    ctx,
                    part,
                    current_fp,
                    current_array,
                    next_fp,
                    next_array,
                    entry_mode,
                )? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        LiveExpr::StatePred { expr, .. } | LiveExpr::Enabled { action: expr, .. } => {
            Err(EvalError::Internal {
                message: format!(
                    "array-native action leaf evaluation received state-level expression {:?}",
                    expr.node
                ),
                span: Some(expr.span),
            })
        }
        LiveExpr::Always(_) | LiveExpr::Eventually(_) | LiveExpr::Next(_) => {
            Err(EvalError::Internal {
                message: "array-native action leaf evaluation received unsupported liveness node"
                    .to_string(),
                span: None,
            })
        }
    }
}

pub(crate) fn eval_action_leaves_array(
    ctx: &mut EvalCtx,
    leaves: &[&LiveExpr],
    current_fp: Fingerprint,
    current_array: &ArrayState,
    next_fp: Fingerprint,
    next_array: &ArrayState,
) -> EvalResult<Vec<(u32, bool)>> {
    if leaves.is_empty() {
        return Ok(Vec::new());
    }

    let registry = ctx.var_registry().clone();
    if registry.is_empty() {
        let current_state = current_array.to_state(&registry);
        let next_state = next_array.to_state(&registry);
        return eval_action_leaves_fallback(ctx, leaves, &current_state, &next_state);
    }

    let _state_guard = ctx.bind_state_env_guard(current_array.env_ref());
    let _next_state_guard = ctx.take_next_state_guard();
    let _next_guard = ctx.take_next_state_env_guard();
    ctx.bind_next_state_env(next_array.env_ref());

    let all_batch_safe = leaves
        .iter()
        .all(|expr| action_leaf_preserves_batch_boundary(expr));

    let mut out = Vec::with_capacity(leaves.len());
    if all_batch_safe {
        crate::eval::evict_next_state_subst_entries();
        crate::eval::evict_next_state_eager_bindings();
        for expr in leaves {
            if let Some(tag) = expr.tag() {
                let result = eval_action_leaf_array(
                    ctx,
                    expr,
                    current_fp,
                    current_array,
                    next_fp,
                    next_array,
                    InlineLeafEntryMode::Inline,
                )?;
                out.push((tag, result));
            }
        }
    } else {
        let mut entry_mode = InlineLeafEntryMode::Boundary;
        for expr in leaves {
            if let Some(tag) = expr.tag() {
                let result = eval_action_leaf_array(
                    ctx,
                    expr,
                    current_fp,
                    current_array,
                    next_fp,
                    next_array,
                    entry_mode,
                )?;
                out.push((tag, result));
                entry_mode = if action_leaf_preserves_batch_boundary(expr) {
                    InlineLeafEntryMode::Inline
                } else {
                    InlineLeafEntryMode::Boundary
                };
            }
        }
    }

    Ok(out)
}
