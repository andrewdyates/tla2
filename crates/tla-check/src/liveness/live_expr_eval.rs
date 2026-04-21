// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared LiveExpr evaluation core.
//!
//! Both `consistency.rs` (BFS tableau consistency checks) and `checker/eval.rs`
//! (SCC/PEM constraint checks) evaluate `LiveExpr` trees with identical match-arm
//! logic for `Bool`, `StatePred`, `ActionPred`, `Not`, `And`, `Or`, and temporal
//! operator rejection. The only differences are:
//!
//! - **ENABLED**: different successor sources (callback vs pre-computed HashMap)
//! - **StateChanged without subscript**: symmetry-aware vs plain fingerprint comparison
//! - **StateChanged with subscript**: cached vs uncached evaluation
//!
//! This module extracts the shared evaluation logic into `eval_live_expr_core`,
//! parameterized by a `LiveExprEvaluator` trait that each call site implements.
//! Bug fixes in one location now propagate to both code paths automatically.
//!
//! See `designs/2026-02-28-2791-liveness-eval-dedup.md` for the full design.

use super::boolean_contract::expect_live_bool;
#[cfg(debug_assertions)]
use super::checker::{debug_action_pred, debug_bindings, debug_changed};
use super::live_expr::LiveExpr;
use crate::enumerate::tir_leaf::eval_leaf_entry;
use crate::error::{EvalError, EvalResult};
use crate::eval::{BindingChain, EvalCtx};
use crate::expr_visitor::expr_contains_prime_v;
use crate::state::State;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;
use tla_eval::tir::TirProgram;

/// Callbacks for environment-dependent behavior during LiveExpr evaluation.
///
/// Each call site (consistency checking, SCC/PEM checker) implements this trait
/// to provide its specific ENABLED evaluation, subscript caching, and symmetry
/// handling while sharing the common match-arm logic in [`eval_live_expr_core`].
pub(crate) trait LiveExprEvaluator {
    /// Compare fingerprints for `StateChanged` when no subscript expression is present.
    ///
    /// Default: direct fingerprint inequality.
    /// Override: symmetry-aware canonical fingerprint comparison.
    fn state_changed_no_subscript(&self, current: &State, next: &State) -> EvalResult<bool> {
        Ok(current.fingerprint() != next.fingerprint())
    }

    /// Evaluate whether the subscript expression changed between two states.
    ///
    /// Consistency path: uncached evaluation via `eval_subscript_changed`.
    /// Checker path: cached evaluation via `subscript_cache::eval_subscript_changed`.
    fn eval_subscript_changed(
        &self,
        ctx: &EvalCtx,
        current: &State,
        next: &State,
        sub_expr: &Arc<Spanned<Expr>>,
        tag: u32,
    ) -> EvalResult<bool>;

    /// Evaluate ENABLED for the given state/action/bindings.
    ///
    /// Both paths call `eval_enabled_cached` internally but differ in:
    /// - How cached successors are obtained (callback vs HashMap)
    /// - Which subscript evaluator is passed to `eval_enabled_uncached`
    #[allow(clippy::too_many_arguments)]
    fn eval_enabled(
        &mut self,
        ctx: &EvalCtx,
        current_state: &State,
        action: &Arc<Spanned<Expr>>,
        bindings: &Option<BindingChain>,
        require_state_change: bool,
        subscript: &Option<Arc<Spanned<Expr>>>,
        tag: u32,
    ) -> EvalResult<bool>;
}

/// Shared recursive evaluation of LiveExpr trees.
///
/// This function implements the common match-arm logic shared between
/// `consistency.rs::eval_live_expr` and `checker/eval.rs::eval_live_check_expr_inner`.
/// The `evaluator` parameter provides environment-specific behavior for ENABLED,
/// subscript evaluation, and symmetry handling.
///
/// # Arguments
///
/// * `evaluator` — Trait implementor providing ENABLED, subscript, and symmetry logic
/// * `ctx` — Evaluation context with state variables already bound
/// * `expr` — The LiveExpr to evaluate
/// * `current_state` — Current state (for ENABLED successor lookup)
/// * `next_state` — Next state if action context is available (for ActionPred, StateChanged)
/// * `tir` — Optional TIR program for leaf expression evaluation (Part of #3194).
///   When `Some`, StatePred and ActionPred leaves attempt TIR evaluation first,
///   falling back to AST eval. When `None`, behavior is identical to before.
pub(crate) fn eval_live_expr_core<E: LiveExprEvaluator>(
    evaluator: &mut E,
    ctx: &EvalCtx,
    expr: &LiveExpr,
    current_state: &State,
    next_state: Option<&State>,
    tir: Option<&TirProgram<'_>>,
) -> EvalResult<bool> {
    match expr {
        LiveExpr::Bool(b) => Ok(*b),

        LiveExpr::StatePred { expr, bindings, .. } => {
            // Evaluate the AST expression in the current context, optionally
            // extending it with liveness bounded-quantifier bindings.
            // Part of #2895: BindingChain bindings survive closure/function entry,
            // so no defensive write_to_env workaround is needed.
            let eval_ctx = match bindings {
                Some(ref chain) => ctx.with_liveness_bindings(chain),
                None => ctx.clone(),
            };
            let value = eval_leaf_entry(&eval_ctx, expr, tir)?;
            expect_live_bool(&value, Some(expr.span))
        }

        LiveExpr::ActionPred {
            expr,
            bindings,
            tag,
            ..
        } => {
            // Action predicates require next state for primed variables.
            // Plan construction classifies ActionPred into ea_action/ae_action,
            // NOT ea_state/ae_state. If we reach here with next_state=None and the
            // expression contains primed vars, the caller passed an action-level
            // expression through a state-only eval path — this is a classification
            // bug that can cause polarity-dependent false negatives (#2286).
            if next_state.is_none() && expr_contains_prime_v(&expr.node) {
                debug_assert!(
                    false,
                    "ActionPred (tag={}) evaluated without next_state — \
                     classification bug (#2286). \
                     Action-level expressions must not appear in state_preds().",
                    tag
                );
                return Err(EvalError::Internal {
                    message: format!(
                        "ActionPred (tag={}) evaluated without action context — \
                         action-level expression in state-only eval path (see #2286)",
                        tag
                    ),
                    span: Some(expr.span),
                });
            }
            // Debug: print bindings info when TLA2_DEBUG_BINDINGS is set
            debug_eprintln!(
                debug_bindings(),
                "[DEBUG BINDINGS] ActionPred tag={} bindings={:?}",
                tag,
                bindings.as_ref().map(|b| format!("{:?}", b))
            );
            // Part of #2895: BindingChain bindings survive closure/function entry.
            let eval_ctx = match bindings {
                Some(ref chain) => ctx.with_liveness_bindings(chain),
                None => ctx.clone(),
            };
            let value = eval_leaf_entry(&eval_ctx, expr, tir).map_err(|e| {
                debug_eprintln!(
                    debug_action_pred(),
                    "[DEBUG ACTION_PRED] ActionPred(tag={}) FAILED: {}",
                    tag,
                    e
                );
                e
            })?;
            let result = expect_live_bool(&value, Some(expr.span))?;
            debug_eprintln!(
                debug_action_pred(),
                "[DEBUG ACTION_PRED] tag={} expr={:?} result={}",
                tag,
                expr.node,
                result
            );
            Ok(result)
        }

        LiveExpr::Enabled {
            action,
            bindings,
            require_state_change,
            subscript,
            tag,
        } => {
            // Part of #2895: Apply liveness bindings via BindingChain before
            // delegating to the evaluator's ENABLED implementation.
            let eval_ctx = match bindings {
                Some(ref chain) => ctx.with_liveness_bindings(chain),
                None => ctx.clone(),
            };
            evaluator.eval_enabled(
                &eval_ctx,
                current_state,
                action,
                bindings,
                *require_state_change,
                subscript,
                *tag,
            )
        }

        LiveExpr::StateChanged {
            subscript,
            bindings,
            tag,
            ..
        } => {
            // StateChanged is true iff e' ≠ e for subscript expression e.
            // This is used for subscripted action semantics <<A>>_e = A /\ (e' ≠ e).
            match next_state {
                Some(ns) => {
                    if let Some(sub_expr) = subscript.as_ref() {
                        // Part of #2895: BindingChain bindings survive closure/function entry.
                        let eval_ctx = match bindings {
                            Some(ref chain) => ctx.with_liveness_bindings(chain),
                            None => ctx.clone(),
                        };
                        let result = evaluator.eval_subscript_changed(
                            &eval_ctx,
                            current_state,
                            ns,
                            sub_expr,
                            *tag,
                        )?;
                        debug_eprintln!(
                            debug_changed(),
                            "[DEBUG CHANGED] tag={} subscript={:?} result={}",
                            tag,
                            sub_expr.node,
                            result
                        );
                        Ok(result)
                    } else {
                        // No subscript — use global fingerprint comparison (with
                        // optional symmetry-aware canonical fp lookup).
                        evaluator.state_changed_no_subscript(current_state, ns)
                    }
                }
                None => {
                    // StateChanged is action-level and should not be evaluated
                    // without a next state. Same classification invariant as ActionPred (#2286).
                    debug_assert!(
                        false,
                        "StateChanged (tag={}) evaluated without next_state — \
                         classification bug (#2286)",
                        tag
                    );
                    Err(EvalError::Internal {
                        message: format!(
                            "StateChanged (tag={}) evaluated without next_state — \
                             action-level expression in state-only eval path (see #2286)",
                            tag
                        ),
                        span: subscript.as_ref().map(|e| e.span),
                    })
                }
            }
        }

        LiveExpr::Not(inner) => Ok(!eval_live_expr_core(
            evaluator,
            ctx,
            inner,
            current_state,
            next_state,
            tir,
        )?),

        LiveExpr::And(exprs) => {
            for e in exprs {
                if !eval_live_expr_core(evaluator, ctx, e, current_state, next_state, tir)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }

        LiveExpr::Or(exprs) => {
            for e in exprs {
                if eval_live_expr_core(evaluator, ctx, e, current_state, next_state, tir)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }

        // Temporal operators should never reach state-level evaluation —
        // the tableau decomposes them before is_state_consistent is called.
        // If one leaks through, it's a bug in tableau construction.
        LiveExpr::Always(_) | LiveExpr::Eventually(_) | LiveExpr::Next(_) => {
            Err(EvalError::Internal {
                message: format!(
                    "unexpected temporal operator in live expression evaluation: {}",
                    expr
                ),
                span: None,
            })
        }
    }
}

#[cfg(test)]
#[path = "live_expr_eval_tests.rs"]
mod tests;
