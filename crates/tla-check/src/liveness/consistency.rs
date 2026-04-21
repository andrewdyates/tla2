// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consistency checking for liveness
//!
//! This module implements checking whether a state is consistent with a tableau node.
//! A state is consistent with a tableau node iff all state predicates in the particle
//! evaluate to TRUE when the state variables are bound.
//!
//! # TLC Reference
//!
//! This follows TLC's `TBGraphNode.isConsistent()` method which checks whether
//! a state satisfies all the state-level formulas in a tableau node.

use super::live_expr::LiveExpr;
use super::live_expr_eval::{eval_live_expr_core, LiveExprEvaluator};
use super::tableau::TableauNode;
use crate::error::EvalResult;
#[cfg(test)]
use crate::eval::Env;
use crate::eval::{BindingChain, EvalCtx};
#[cfg(test)]
use crate::liveness::ExprLevel;
use crate::state::State;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;
use tla_eval::tir::TirProgram;

/// Evaluate whether the subscript expression changed between two states.
///
/// Returns true iff `subscript(s1) ≠ subscript(s2)`.
fn eval_subscript_changed(
    ctx: &EvalCtx,
    s1: &State,
    s2: &State,
    subscript: &Arc<Spanned<Expr>>,
) -> EvalResult<bool> {
    // Evaluate subscript in s1.
    //
    // Keep the base env (constants/config bindings like `Node`) and overlay
    // state variables for this concrete state.
    // Part of #2144: skip state vars that shadow local bindings (quantifier
    // variables). BindingChain is preserved by with_explicit_env and checked
    // first during lookup, but closure entry replaces the chain and would
    // expose the overwritten env entry.
    let mut env1 = ctx.env().clone();
    for (name, value) in s1.vars() {
        if !ctx.has_local_binding(name.as_ref()) {
            env1.insert(Arc::clone(name), value.clone());
        }
    }
    // Fix #2780: Clear SUBST_CACHE before evaluating val1 via with_explicit_env
    // (state_env=None, pointer 0). A prior call's val2 evaluation may have left
    // entries keyed on the same pointer 0, causing stale hits here.
    crate::eval::clear_subst_cache();
    let ctx1 = ctx.with_explicit_env(env1);
    let val1 = super::eval_live_entry(&ctx1, subscript)?;

    // Clear only SUBST_CACHE between state evaluations. with_explicit_env sets
    // state_env=None, so eval_entry's pointer-based invalidation (which compares
    // state_env identity) sees both calls as "same state" and serves stale
    // INSTANCE substitution results. Keep other caches hot for performance.
    crate::eval::clear_subst_cache();

    // Evaluate subscript in s2 with the same base-env preservation.
    let mut env2 = ctx.env().clone();
    for (name, value) in s2.vars() {
        if !ctx.has_local_binding(name.as_ref()) {
            env2.insert(Arc::clone(name), value.clone());
        }
    }
    let ctx2 = ctx.with_explicit_env(env2);
    let val2 = super::eval_live_entry(&ctx2, subscript)?;

    Ok(val1 != val2)
}

/// LiveExprEvaluator for BFS consistency checking.
///
/// Uses a callback for successor enumeration (ENABLED) and uncached
/// subscript evaluation. No symmetry support.
struct ConsistencyEvaluator<'a, F> {
    get_successors: &'a mut F,
}

impl<F> LiveExprEvaluator for ConsistencyEvaluator<'_, F>
where
    F: FnMut(&State) -> EvalResult<Vec<State>>,
{
    fn eval_subscript_changed(
        &self,
        ctx: &EvalCtx,
        current: &State,
        next: &State,
        sub_expr: &Arc<Spanned<Expr>>,
        _tag: u32,
    ) -> EvalResult<bool> {
        eval_subscript_changed(ctx, current, next, sub_expr)
    }

    fn eval_enabled(
        &mut self,
        ctx: &EvalCtx,
        current_state: &State,
        action: &Arc<Spanned<Expr>>,
        bindings: &Option<BindingChain>,
        require_state_change: bool,
        subscript: &Option<Arc<Spanned<Expr>>>,
        tag: u32,
    ) -> EvalResult<bool> {
        super::checker::eval_enabled_cached(ctx, current_state.fingerprint(), tag, || {
            let cached_successors = if require_state_change || ctx.var_registry().is_empty() {
                (self.get_successors)(current_state)?
            } else {
                Vec::new()
            };
            super::enabled_eval::eval_enabled_uncached(
                super::enabled_eval::EnabledEvalRequest {
                    ctx_current: ctx,
                    current_state,
                    action,
                    bindings: bindings.as_ref(),
                    require_state_change,
                    subscript: subscript.as_ref(),
                    cached_successors: &cached_successors,
                },
                eval_subscript_changed,
            )
        })
    }
}

/// Check if a state is consistent with a tableau node
///
/// A state is consistent with a tableau node iff all state predicates
/// in the node evaluate to TRUE with the state's variable bindings.
///
/// # Arguments
///
/// * `ctx` - Base evaluation context (with operators loaded)
/// * `state` - The TLA+ state to check
/// * `node` - The tableau node to check against
/// * `get_successors` - Callback to enumerate successor states (for ENABLED)
///
/// # Returns
///
/// * `Ok(true)` if the state is consistent with the tableau node
/// * `Ok(false)` if any state predicate evaluates to FALSE
/// * `Err(...)` if evaluation fails
pub(super) fn is_state_consistent<F>(
    ctx: &EvalCtx,
    state: &State,
    node: &TableauNode,
    get_successors: &mut F,
    tir: Option<&TirProgram<'_>>,
) -> EvalResult<bool>
where
    F: FnMut(&State) -> EvalResult<Vec<State>>,
{
    // Bind state variables to the context
    let mut state_ctx = ctx.clone();
    for (name, value) in state.vars() {
        state_ctx.bind_mut(Arc::clone(name), value.clone());
    }

    // Check each state predicate in the tableau node.
    // eval_live_expr_core enforces boolean contract at leaf level, so non-boolean
    // values from StatePred/ActionPred are TypeError before reaching here.
    for pred in node.state_preds() {
        if !eval_live_expr(&state_ctx, pred, state, None, get_successors, tir)? {
            return Ok(false);
        }
    }

    Ok(true)
}

/// Check if a state transition is consistent with a tableau node
///
/// This is used for action predicates that depend on both current and next state.
///
/// # Arguments
///
/// * `ctx` - Base evaluation context
/// * `current_state` - The current TLA+ state
/// * `next_state` - The next TLA+ state (for primed variables)
/// * `node` - The tableau node containing action predicates
/// * `get_successors` - Callback to enumerate successor states (for ENABLED)
///
/// # Returns
///
/// * `Ok(true)` if the transition is consistent
/// * `Ok(false)` if any action predicate evaluates to FALSE
/// * `Err(...)` if evaluation fails
#[cfg(test)]
pub(super) fn is_transition_consistent<F>(
    ctx: &EvalCtx,
    current_state: &State,
    next_state: &State,
    node: &TableauNode,
    get_successors: &mut F,
) -> EvalResult<bool>
where
    F: FnMut(&State) -> EvalResult<Vec<State>>,
{
    // Bind current state variables
    let mut trans_ctx = ctx.clone();
    for (name, value) in current_state.vars() {
        trans_ctx.bind_mut(Arc::clone(name), value.clone());
    }

    // Set up next-state bindings for primed variables
    let mut next_env = Env::new();
    for (name, value) in next_state.vars() {
        next_env.insert(Arc::clone(name), value.clone());
    }
    trans_ctx.set_next_state(next_env);

    // Check non-temporal predicates in the particle. Temporal operators
    // (Always, Eventually, Next) are handled by the tableau structure itself
    // and would cause EvalError::Internal if evaluated here.
    for formula in node
        .particle()
        .formulas()
        .iter()
        .filter(|f| f.level() != ExprLevel::Temporal)
    {
        if !eval_live_expr(
            &trans_ctx,
            formula,
            current_state,
            Some(next_state),
            get_successors,
            None, // TIR not wired through test path
        )? {
            return Ok(false);
        }
    }

    Ok(true)
}

/// Evaluate a LiveExpr in a state context
///
/// This evaluates state predicates, action predicates, and boolean combinations.
/// Temporal operators (Always, Eventually, Next) are not evaluated here -
/// they are handled by the tableau structure itself.
///
/// Delegates to the shared [`eval_live_expr_core`] with a [`ConsistencyEvaluator`]
/// that provides callback-based successor access and uncached subscript evaluation.
///
/// # Arguments
///
/// * `ctx` - Evaluation context with state variables bound
/// * `expr` - The LiveExpr to evaluate
/// * `current_state` - Current state (for ENABLED checking)
/// * `next_state` - Next state (for action predicates, if available)
/// * `get_successors` - Callback to enumerate successor states (for ENABLED)
pub(super) fn eval_live_expr<F>(
    ctx: &EvalCtx,
    expr: &LiveExpr,
    current_state: &State,
    next_state: Option<&State>,
    get_successors: &mut F,
    tir: Option<&TirProgram<'_>>,
) -> EvalResult<bool>
where
    F: FnMut(&State) -> EvalResult<Vec<State>>,
{
    let mut evaluator = ConsistencyEvaluator { get_successors };
    eval_live_expr_core(&mut evaluator, ctx, expr, current_state, next_state, tir)
}

#[cfg(test)]
#[path = "consistency_tests/mod.rs"]
mod tests;
