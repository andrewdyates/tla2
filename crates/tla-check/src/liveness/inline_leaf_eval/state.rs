// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::fallback::eval_state_leaves_with_cached_successors_fallback;
use super::{eval_bool_expr_with_entry_mode, InlineLeafEntryMode};
use crate::enumerate::is_disabled_action_error;
use crate::error::{EvalError, EvalResult};
use crate::eval::{BindingChain, EvalCtx};
use crate::liveness::boolean_contract::expect_live_bool;
use crate::liveness::live_expr::LiveExpr;
use crate::state::{ArrayState, Fingerprint};
use rustc_hash::FxHashMap;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;

pub(super) fn state_leaf_preserves_batch_boundary(expr: &LiveExpr) -> bool {
    match expr {
        LiveExpr::Bool(_) | LiveExpr::StatePred { .. } => true,
        LiveExpr::Not(inner)
        | LiveExpr::Always(inner)
        | LiveExpr::Eventually(inner)
        | LiveExpr::Next(inner) => state_leaf_preserves_batch_boundary(inner),
        LiveExpr::And(parts) | LiveExpr::Or(parts) => {
            parts.iter().all(state_leaf_preserves_batch_boundary)
        }
        LiveExpr::Enabled { .. } | LiveExpr::ActionPred { .. } | LiveExpr::StateChanged { .. } => {
            false
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn eval_enabled_with_array_successors(
    ctx: &mut EvalCtx,
    current_fp: Fingerprint,
    current_array: &ArrayState,
    action: &Arc<Spanned<Expr>>,
    bindings: Option<&BindingChain>,
    require_state_change: bool,
    subscript: Option<&Arc<Spanned<Expr>>>,
    tag: u32,
    successors: &[(&ArrayState, Fingerprint)],
) -> EvalResult<bool> {
    super::super::checker::eval_enabled_cached_mut(ctx, current_fp, tag, |ctx| {
        for (next_array, next_fp) in successors {
            if require_state_change {
                if let Some(sub_expr) = subscript {
                    if !super::super::checker::eval_subscript_changed_array_cached(
                        ctx,
                        current_fp,
                        current_array,
                        *next_fp,
                        next_array,
                        sub_expr,
                        bindings,
                        tag,
                    )? {
                        continue;
                    }
                } else if *next_fp == current_fp {
                    continue;
                }
            }

            let prev_next_state = ctx.next_state_mut().take();
            let _next_guard = ctx.take_next_state_env_guard();
            ctx.bind_next_state_env(next_array.env_ref());

            crate::eval::evict_next_state_subst_entries();
            crate::eval::evict_next_state_eager_bindings();

            let result = match bindings {
                Some(chain) => {
                    let eval_ctx = ctx.with_liveness_bindings(chain);
                    crate::eval::eval_entry_inline(&eval_ctx, action)
                }
                None => crate::eval::eval_entry_inline(ctx, action),
            };
            match result {
                Ok(value) => {
                    *ctx.next_state_mut() = prev_next_state;
                    if expect_live_bool(&value, Some(action.span))? {
                        return Ok(true);
                    }
                }
                Err(e) if is_disabled_action_error(&e) => {
                    *ctx.next_state_mut() = prev_next_state;
                }
                Err(e) => {
                    *ctx.next_state_mut() = prev_next_state;
                    return Err(e);
                }
            }
        }
        Ok(false)
    })
}

fn eval_state_leaf_array(
    ctx: &mut EvalCtx,
    expr: &LiveExpr,
    current_fp: Fingerprint,
    current_array: &ArrayState,
    successors: &[(&ArrayState, Fingerprint)],
    entry_mode: InlineLeafEntryMode,
) -> EvalResult<bool> {
    match expr {
        LiveExpr::Bool(b) => Ok(*b),
        LiveExpr::StatePred { expr, bindings, .. } => match bindings {
            Some(chain) => {
                let eval_ctx = ctx.with_liveness_bindings(chain);
                eval_bool_expr_with_entry_mode(&eval_ctx, expr, entry_mode)
            }
            None => eval_bool_expr_with_entry_mode(ctx, expr, entry_mode),
        },
        LiveExpr::Enabled {
            action,
            bindings,
            require_state_change,
            subscript,
            tag,
        } => eval_enabled_with_array_successors(
            ctx,
            current_fp,
            current_array,
            action,
            bindings.as_ref(),
            *require_state_change,
            subscript.as_ref(),
            *tag,
            successors,
        ),
        LiveExpr::Not(inner) => Ok(!eval_state_leaf_array(
            ctx,
            inner,
            current_fp,
            current_array,
            successors,
            entry_mode,
        )?),
        LiveExpr::And(parts) => {
            for part in parts {
                if !eval_state_leaf_array(
                    ctx,
                    part,
                    current_fp,
                    current_array,
                    successors,
                    entry_mode,
                )? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        LiveExpr::Or(parts) => {
            for part in parts {
                if eval_state_leaf_array(
                    ctx,
                    part,
                    current_fp,
                    current_array,
                    successors,
                    entry_mode,
                )? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        LiveExpr::ActionPred { expr, .. }
        | LiveExpr::StateChanged {
            subscript: Some(expr),
            ..
        } => Err(EvalError::Internal {
            message: format!(
                "array-native state leaf evaluation received action-level expression {:?}",
                expr.node
            ),
            span: Some(expr.span),
        }),
        LiveExpr::StateChanged {
            subscript: None, ..
        }
        | LiveExpr::Always(_)
        | LiveExpr::Eventually(_)
        | LiveExpr::Next(_) => Err(EvalError::Internal {
            message: "array-native state leaf evaluation received unsupported liveness node"
                .to_string(),
            span: None,
        }),
    }
}

pub(crate) fn eval_state_leaves_with_array_successors(
    ctx: &mut EvalCtx,
    leaves: &[&LiveExpr],
    current_fp: Fingerprint,
    current_array: &ArrayState,
    successors: &[(&ArrayState, Fingerprint)],
) -> EvalResult<Vec<(u32, bool)>> {
    if leaves.is_empty() {
        return Ok(Vec::new());
    }

    let registry = ctx.var_registry().clone();
    if registry.is_empty() {
        let current_state = current_array.to_state(&registry);
        let cached_successors: Vec<_> = successors
            .iter()
            .map(|(state, _)| state.to_state(&registry))
            .collect();
        return eval_state_leaves_with_cached_successors_fallback(
            ctx,
            leaves,
            &current_state,
            &cached_successors,
        );
    }

    let mut enabled_indices = Vec::new();
    let mut non_enabled_indices = Vec::new();
    for (index, leaf) in leaves.iter().enumerate() {
        if matches!(leaf, LiveExpr::Enabled { .. }) {
            enabled_indices.push(index);
        } else {
            non_enabled_indices.push(index);
        }
    }
    debug_assert_eq!(
        enabled_indices.len() + non_enabled_indices.len(),
        leaves.len()
    );

    let _state_guard = ctx.bind_state_env_guard(current_array.env_ref());
    let _next_state_guard = ctx.take_next_state_guard();
    let _next_guard = ctx.take_next_state_env_guard();

    let enabled_results_map: Option<FxHashMap<u32, bool>> = if enabled_indices.len() > 1 {
        let enabled_leaves: Vec<_> = enabled_indices.iter().map(|&i| leaves[i]).collect();
        let results = eval_enabled_leaves_batched(
            ctx,
            current_fp,
            current_array,
            &enabled_leaves,
            successors,
        )?;
        Some(results.into_iter().collect())
    } else {
        None
    };

    let mut out = Vec::with_capacity(leaves.len());
    let mut entry_mode = InlineLeafEntryMode::Boundary;
    for expr in leaves {
        if let Some(tag) = expr.tag() {
            if let Some(ref map) = enabled_results_map {
                if let Some(&result) = map.get(&tag) {
                    out.push((tag, result));
                    entry_mode = InlineLeafEntryMode::Boundary;
                    continue;
                }
            }
            let result = eval_state_leaf_array(
                ctx,
                expr,
                current_fp,
                current_array,
                successors,
                entry_mode,
            )?;
            out.push((tag, result));
            entry_mode = if state_leaf_preserves_batch_boundary(expr) {
                InlineLeafEntryMode::Inline
            } else {
                InlineLeafEntryMode::Boundary
            };
        }
    }

    Ok(out)
}

fn eval_enabled_leaves_batched(
    ctx: &mut EvalCtx,
    current_fp: Fingerprint,
    current_array: &ArrayState,
    enabled_leaves: &[&LiveExpr],
    successors: &[(&ArrayState, Fingerprint)],
) -> EvalResult<Vec<(u32, bool)>> {
    let use_cache = !ctx.var_registry().is_empty();
    let mut resolved = Vec::with_capacity(enabled_leaves.len());
    let mut unresolved_count = 0usize;

    for leaf in enabled_leaves {
        if let LiveExpr::Enabled { tag, .. } = leaf {
            if use_cache {
                if let Some(result) = super::super::checker::get_enabled_cached(current_fp, *tag) {
                    resolved.push(Some(result));
                    continue;
                }
            }
            resolved.push(None);
            unresolved_count += 1;
        } else {
            resolved.push(None);
        }
    }

    if unresolved_count == 0 {
        return Ok(enabled_leaves
            .iter()
            .zip(resolved.iter())
            .filter_map(|(leaf, res)| leaf.tag().map(|tag| (tag, res.unwrap_or(false))))
            .collect());
    }

    // Part of #3962: Use ctx-aware variant to sync in_enabled_scope shadow.
    let _enabled_guard = crate::eval::enter_enabled_scope_with_ctx(ctx);
    for (next_array, next_fp) in successors {
        if unresolved_count == 0 {
            break;
        }

        let prev_next_state = ctx.next_state_mut().take();
        let _next_guard = ctx.take_next_state_env_guard();
        ctx.bind_next_state_env(next_array.env_ref());
        crate::eval::evict_next_state_subst_entries();
        crate::eval::evict_next_state_eager_bindings();

        let mut any_eval_this_succ = false;
        for (index, leaf) in enabled_leaves.iter().enumerate() {
            if resolved[index].is_some() {
                continue;
            }

            if let LiveExpr::Enabled {
                action,
                bindings,
                require_state_change,
                subscript,
                tag,
            } = leaf
            {
                if *require_state_change {
                    if let Some(sub_expr) = subscript {
                        if !super::super::checker::eval_subscript_changed_array_cached(
                            ctx,
                            current_fp,
                            current_array,
                            *next_fp,
                            next_array,
                            sub_expr,
                            bindings.as_ref(),
                            *tag,
                        )? {
                            continue;
                        }
                    } else if *next_fp == current_fp {
                        continue;
                    }
                }

                if any_eval_this_succ {
                    crate::eval::evict_next_state_subst_entries();
                }
                any_eval_this_succ = true;

                let result = match bindings {
                    Some(chain) => {
                        let eval_ctx = ctx.with_liveness_bindings(chain);
                        crate::eval::eval_entry_inline(&eval_ctx, action)
                    }
                    None => crate::eval::eval_entry_inline(ctx, action),
                };

                match result {
                    Ok(value) => {
                        if expect_live_bool(&value, Some(action.span))? {
                            resolved[index] = Some(true);
                            if use_cache {
                                super::super::checker::set_enabled_cache(current_fp, *tag, true);
                            }
                            unresolved_count -= 1;
                        }
                    }
                    Err(e) if is_disabled_action_error(&e) => {}
                    Err(e) => {
                        *ctx.next_state_mut() = prev_next_state;
                        return Err(e);
                    }
                }
            }
        }

        *ctx.next_state_mut() = prev_next_state;
    }

    for (index, leaf) in enabled_leaves.iter().enumerate() {
        if resolved[index].is_none() {
            if let LiveExpr::Enabled { tag, .. } = leaf {
                resolved[index] = Some(false);
                if use_cache {
                    super::super::checker::set_enabled_cache(current_fp, *tag, false);
                }
            }
        }
    }

    Ok(enabled_leaves
        .iter()
        .zip(resolved.iter())
        .filter_map(|(leaf, res)| leaf.tag().map(|tag| (tag, res.unwrap_or(false))))
        .collect())
}
