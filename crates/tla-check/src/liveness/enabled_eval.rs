// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared ENABLED evaluation logic for liveness.
//!
//! Both `consistency.rs` (BFS consistency checks) and `checker/eval.rs`
//! (SCC/PEM checks) must run the same ENABLED algorithm to avoid drift.

use crate::enumerate::is_disabled_action_error;
use crate::error::EvalResult;
use crate::eval::{BindingChain, Env, EvalCtx};
use crate::liveness::boolean_contract::expect_live_bool;
use crate::state::State;
use std::sync::Arc;
use tla_core::{ast::Expr, Spanned};

type ExprRef = Arc<Spanned<Expr>>;

pub(super) struct EnabledEvalRequest<'a> {
    pub(super) ctx_current: &'a EvalCtx,
    pub(super) current_state: &'a State,
    pub(super) action: &'a ExprRef,
    pub(super) bindings: Option<&'a BindingChain>,
    pub(super) require_state_change: bool,
    pub(super) subscript: Option<&'a ExprRef>,
    pub(super) cached_successors: &'a [State],
}

pub(super) fn eval_enabled_uncached<F>(
    request: EnabledEvalRequest<'_>,
    mut eval_subscript_changed: F,
) -> EvalResult<bool>
where
    F: FnMut(&EvalCtx, &State, &State, &ExprRef) -> EvalResult<bool>,
{
    let vars: Vec<Arc<str>> = request.ctx_current.shared().var_registry.names().to_vec();
    if !vars.is_empty() {
        let mut eval_ctx = request.ctx_current.clone();
        *eval_ctx.next_state_mut() = None;
        // Part of #2755: snapshot state pairs BEFORE clearing state_env so that
        // eval_enabled_cp's snapshot_state_pairs finds them via env.
        let state_pairs = eval_ctx.snapshot_state_pairs(&vars);
        let _ = eval_ctx.take_state_env();
        let _ = eval_ctx.take_next_state_env();
        for (name, value) in &state_pairs {
            eval_ctx.bind_mut(Arc::clone(name), value.clone());
        }
        // Part of #2895: Apply liveness bindings via BindingChain (shadows state vars).
        // BindingChain bindings survive closure/function entry, no write_to_env needed.
        if let Some(chain) = request.bindings {
            eval_ctx = eval_ctx.with_liveness_bindings(chain);
        }

        if request.require_state_change {
            if cached_successor_satisfies_action(
                &eval_ctx,
                request.current_state,
                request.action,
                request.bindings,
                true,
                request.subscript,
                request.cached_successors,
                &mut eval_subscript_changed,
            )? {
                return Ok(true);
            }

            let successors = match crate::enumerate::enumerate_action_successors(
                &mut eval_ctx,
                request.action,
                request.current_state,
                &vars,
            ) {
                Ok(successors) => successors,
                Err(e) if is_disabled_action_error(&e) => return Ok(false),
                Err(e) => return Err(e),
            };
            return any_state_change(
                &eval_ctx,
                request.current_state,
                request.subscript,
                &successors,
                &mut eval_subscript_changed,
            );
        }

        if cached_successor_satisfies_action(
            &eval_ctx,
            request.current_state,
            request.action,
            request.bindings,
            false,
            request.subscript,
            request.cached_successors,
            &mut eval_subscript_changed,
        )? {
            return Ok(true);
        }

        return crate::enabled::eval_enabled_cp(&mut eval_ctx, request.action, &vars);
    }

    eval_enabled_fallback(&request, &mut eval_subscript_changed)
}

#[allow(clippy::too_many_arguments)]
fn cached_successor_satisfies_action<F>(
    eval_ctx: &EvalCtx,
    current_state: &State,
    action: &ExprRef,
    bindings: Option<&BindingChain>,
    require_state_change: bool,
    subscript: Option<&ExprRef>,
    cached_successors: &[State],
    eval_subscript_changed: &mut F,
) -> EvalResult<bool>
where
    F: FnMut(&EvalCtx, &State, &State, &ExprRef) -> EvalResult<bool>,
{
    for succ_state in cached_successors {
        if require_state_change
            && !has_state_change(
                eval_ctx,
                current_state,
                succ_state,
                subscript,
                eval_subscript_changed,
            )?
        {
            continue;
        }

        match transition_satisfies_action(eval_ctx, current_state, succ_state, action, bindings) {
            Ok(true) => return Ok(true),
            Ok(false) => {}
            Err(e) if is_disabled_action_error(&e) => {}
            Err(e) => return Err(e),
        }
    }

    Ok(false)
}

fn any_state_change<F>(
    eval_ctx: &EvalCtx,
    current_state: &State,
    subscript: Option<&ExprRef>,
    successors: &[State],
    eval_subscript_changed: &mut F,
) -> EvalResult<bool>
where
    F: FnMut(&EvalCtx, &State, &State, &ExprRef) -> EvalResult<bool>,
{
    for succ in successors {
        if has_state_change(
            eval_ctx,
            current_state,
            succ,
            subscript,
            eval_subscript_changed,
        )? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn eval_enabled_fallback<F>(
    request: &EnabledEvalRequest<'_>,
    eval_subscript_changed: &mut F,
) -> EvalResult<bool>
where
    F: FnMut(&EvalCtx, &State, &State, &ExprRef) -> EvalResult<bool>,
{
    let mut eval_ctx = request.ctx_current.clone();
    *eval_ctx.next_state_mut() = None;
    let _ = eval_ctx.take_state_env();
    let _ = eval_ctx.take_next_state_env();
    // Part of #2895: Apply liveness bindings via BindingChain.
    if let Some(chain) = request.bindings {
        eval_ctx = eval_ctx.with_liveness_bindings(chain);
    }

    cached_successor_satisfies_action(
        &eval_ctx,
        request.current_state,
        request.action,
        request.bindings,
        request.require_state_change,
        request.subscript,
        request.cached_successors,
        eval_subscript_changed,
    )
}

fn has_state_change<F>(
    ctx: &EvalCtx,
    current_state: &State,
    successor_state: &State,
    subscript: Option<&ExprRef>,
    eval_subscript_changed: &mut F,
) -> EvalResult<bool>
where
    F: FnMut(&EvalCtx, &State, &State, &ExprRef) -> EvalResult<bool>,
{
    if let Some(sub_expr) = subscript {
        return eval_subscript_changed(ctx, current_state, successor_state, sub_expr);
    }
    Ok(successor_state.fingerprint() != current_state.fingerprint())
}

fn transition_satisfies_action(
    eval_ctx: &EvalCtx,
    current_state: &State,
    successor_state: &State,
    action: &ExprRef,
    bindings: Option<&BindingChain>,
) -> EvalResult<bool> {
    let mut action_ctx = eval_ctx.clone();
    for (name, value) in current_state.vars() {
        action_ctx.env_mut().insert(Arc::clone(name), value.clone());
    }
    // Part of #2895: Apply liveness bindings via BindingChain (shadows state vars).
    if let Some(chain) = bindings {
        action_ctx = action_ctx.with_liveness_bindings(chain);
    }

    let mut next_env = Env::new();
    for (name, value) in successor_state.vars() {
        next_env.insert(Arc::clone(name), value.clone());
    }
    action_ctx.set_next_state(next_env);

    let value = super::eval_live_entry(&action_ctx, action)?;
    expect_live_bool(&value, Some(action.span))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::liveness::test_helpers::spanned;
    use crate::Value;
    use tla_core::name_intern::NameId;

    fn identity_action() -> ExprRef {
        let x = spanned(Expr::Ident("x".to_string(), NameId::INVALID));
        let x_prime = spanned(Expr::Prime(Box::new(x.clone())));
        Arc::new(spanned(Expr::Eq(Box::new(x_prime), Box::new(x))))
    }

    #[test]
    fn test_cached_successor_satisfies_action_accepts_self_loop_without_state_change() {
        let eval_ctx = EvalCtx::new();
        let current = State::from_pairs([("x", Value::int(5))]);
        let mut eval_subscript_changed = |_: &EvalCtx, _: &State, _: &State, _: &ExprRef| {
            unreachable!("no subscript check when require_state_change=false")
        };

        let enabled = cached_successor_satisfies_action(
            &eval_ctx,
            &current,
            &identity_action(),
            None,
            false,
            None,
            std::slice::from_ref(&current),
            &mut eval_subscript_changed,
        )
        .expect("self-loop successor should evaluate without error");

        assert!(
            enabled,
            "require_state_change=false should accept a cached self-loop that satisfies the action"
        );
    }

    #[test]
    fn test_cached_successor_satisfies_action_skips_self_loop_with_state_change() {
        let eval_ctx = EvalCtx::new();
        let current = State::from_pairs([("x", Value::int(5))]);
        let mut eval_subscript_changed = |_: &EvalCtx, _: &State, _: &State, _: &ExprRef| {
            unreachable!("no subscript check without a subscript expression")
        };

        let enabled = cached_successor_satisfies_action(
            &eval_ctx,
            &current,
            &identity_action(),
            None,
            true,
            None,
            std::slice::from_ref(&current),
            &mut eval_subscript_changed,
        )
        .expect("self-loop successor should evaluate without error");

        assert!(
            !enabled,
            "require_state_change=true must skip a cached self-loop successor"
        );
    }
}
