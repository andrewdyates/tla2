// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{build_state_env, CachedSuccessorEvaluator};
use crate::error::EvalResult;
use crate::eval::EvalCtx;
use crate::liveness::live_expr::LiveExpr;
use crate::liveness::live_expr_eval::eval_live_expr_core;
use crate::state::State;
use std::sync::Arc;

pub(super) fn eval_state_leaves_with_cached_successors_fallback(
    ctx: &mut EvalCtx,
    leaves: &[&LiveExpr],
    current_state: &State,
    cached_successors: &[State],
) -> EvalResult<Vec<(u32, bool)>> {
    if leaves.is_empty() {
        return Ok(Vec::new());
    }

    let mut evaluator = CachedSuccessorEvaluator { cached_successors };
    let registry = ctx.var_registry().clone();
    let mut out = Vec::with_capacity(leaves.len());

    if !registry.is_empty() {
        let current_values = current_state.to_values(&registry);
        let _state_guard = ctx.bind_state_array_guard(&current_values);
        let _next_state_guard = ctx.take_next_state_guard();
        let _next_guard = ctx.take_next_state_env_guard();

        for expr in leaves {
            if let Some(tag) = expr.tag() {
                let result =
                    eval_live_expr_core(&mut evaluator, ctx, expr, current_state, None, None)?;
                out.push((tag, result));
            }
        }

        return Ok(out);
    }

    let prev_env = ctx.env().clone();
    let _next_state_guard = ctx.take_next_state_guard();
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    for expr in leaves {
        if let Some(tag) = expr.tag() {
            let result = eval_live_expr_core(&mut evaluator, ctx, expr, current_state, None, None)?;
            out.push((tag, result));
        }
    }

    *ctx.env_mut() = prev_env;
    Ok(out)
}

pub(super) fn eval_action_leaves_fallback(
    ctx: &mut EvalCtx,
    leaves: &[&LiveExpr],
    current_state: &State,
    next_state: &State,
) -> EvalResult<Vec<(u32, bool)>> {
    if leaves.is_empty() {
        return Ok(Vec::new());
    }

    let mut evaluator = CachedSuccessorEvaluator {
        cached_successors: &[],
    };
    let registry = ctx.var_registry().clone();
    let mut out = Vec::with_capacity(leaves.len());

    if !registry.is_empty() {
        let current_values = current_state.to_values(&registry);
        let next_values = next_state.to_values(&registry);
        let next_env = build_state_env(ctx, next_state);

        let _state_guard = ctx.bind_state_array_guard(&current_values);
        let _next_state_guard = ctx.take_next_state_guard();
        let _next_guard = ctx.take_next_state_env_guard();
        *ctx.next_state_mut() = Some(next_env);
        ctx.bind_next_state_array(&next_values);

        for expr in leaves {
            if let Some(tag) = expr.tag() {
                let result = eval_live_expr_core(
                    &mut evaluator,
                    ctx,
                    expr,
                    current_state,
                    Some(next_state),
                    None,
                )?;
                out.push((tag, result));
            }
        }

        return Ok(out);
    }

    let prev_env = ctx.env().clone();
    let _next_state_guard = ctx.take_next_state_guard();
    for (name, value) in current_state.vars() {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }
    *ctx.next_state_mut() = Some(build_state_env(ctx, next_state));

    for expr in leaves {
        if let Some(tag) = expr.tag() {
            let result = eval_live_expr_core(
                &mut evaluator,
                ctx,
                expr,
                current_state,
                Some(next_state),
                None,
            )?;
            out.push((tag, result));
        }
    }

    *ctx.env_mut() = prev_env;
    Ok(out)
}
