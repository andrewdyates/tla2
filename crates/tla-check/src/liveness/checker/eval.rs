// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression evaluation for liveness constraint checking.
//!
//! Evaluates LiveExpr check expressions against concrete states and transitions,
//! including ENABLED evaluation. Subscript change detection is in `subscript_cache`.
//!
//! The core match-arm logic is shared with `consistency.rs` via
//! [`crate::liveness::live_expr_eval::eval_live_expr_core`]. This module provides
//! the [`CheckerEvaluator`] implementation that supplies SCC/PEM-specific behavior:
//! symmetry-aware fingerprint comparison, cached subscript evaluation, and
//! HashMap-based successor lookup for ENABLED.

#[cfg(test)]
use super::check_mask::CheckMask;
use super::BehaviorGraph;
use super::{LiveExpr, LivenessChecker};
use crate::error::EvalResult;
use crate::eval::{BindingChain, EvalCtx};
use crate::liveness::live_expr_eval::{eval_live_expr_core, LiveExprEvaluator};
use crate::liveness::SuccessorWitnessMap;
use crate::state::{Fingerprint, State};
use crate::var_index::VarRegistry;
use rustc_hash::FxHashMap;
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::Spanned;
use tla_eval::tir::TirProgram;

fn enabled_lookup_fp(
    state_fp_to_canon_fp: &Option<Arc<FxHashMap<Fingerprint, Fingerprint>>>,
    state_fp: Fingerprint,
) -> Fingerprint {
    state_fp_to_canon_fp
        .as_ref()
        .and_then(|fp_map| fp_map.get(&state_fp).copied())
        .unwrap_or(state_fp)
}

fn enabled_successors(
    state_fp_to_canon_fp: &Option<Arc<FxHashMap<Fingerprint, Fingerprint>>>,
    succ_witnesses: &Option<Arc<SuccessorWitnessMap>>,
    state_successors: &FxHashMap<Fingerprint, Arc<Vec<State>>>,
    state_successor_fps: &FxHashMap<Fingerprint, Arc<Vec<Fingerprint>>>,
    graph: &BehaviorGraph,
    registry: &VarRegistry,
    state_fp: Fingerprint,
) -> Vec<State> {
    let lookup_fp = enabled_lookup_fp(state_fp_to_canon_fp, state_fp);
    for fp in [lookup_fp, state_fp] {
        if let Some(witnesses) = succ_witnesses.as_ref().and_then(|map| map.get(&fp)) {
            // Part of #2661: Convert ArrayState→State lazily on the SCC ENABLED
            // evaluation path. This is rare (only reached when safety-temporal
            // fast path returns NotApplicable). The hot path in safety_temporal.rs
            // and safety_parts.rs uses ArrayState::values() directly.
            return witnesses
                .iter()
                .map(|(_, arr)| arr.to_state(registry))
                .collect();
        }
        if let Some(succs) = state_successors.get(&fp) {
            return succs.as_ref().clone();
        }
        if let Some(succ_fps) = state_successor_fps.get(&fp) {
            return succ_fps
                .iter()
                .filter_map(|succ_fp| graph.get_state_by_fp(*succ_fp).cloned())
                .collect();
        }
        if fp == state_fp {
            break;
        }
    }
    Vec::new()
}

/// LiveExprEvaluator for SCC/PEM constraint checking.
///
/// Provides symmetry-aware fingerprint comparison, cached subscript evaluation
/// via `subscript_cache`, and HashMap-based successor lookup for ENABLED.
struct CheckerEvaluator<'a> {
    state_fp_to_canon_fp: &'a Option<Arc<FxHashMap<Fingerprint, Fingerprint>>>,
    succ_witnesses: &'a Option<Arc<SuccessorWitnessMap>>,
    state_successors: &'a FxHashMap<Fingerprint, Arc<Vec<State>>>,
    state_successor_fps: &'a FxHashMap<Fingerprint, Arc<Vec<Fingerprint>>>,
    graph: &'a BehaviorGraph,
    /// Part of #2661: Registry needed for ArrayState→State conversion in
    /// enabled_successors when witness map contains ArrayState values.
    registry: &'a VarRegistry,
}

impl LiveExprEvaluator for CheckerEvaluator<'_> {
    fn state_changed_no_subscript(&self, current: &State, next: &State) -> EvalResult<bool> {
        // Under symmetry, compare canonical fingerprints to detect true state change.
        if let Some(fp_map) = self.state_fp_to_canon_fp {
            let canon_current = fp_map.get(&current.fingerprint()).copied();
            let canon_next = fp_map.get(&next.fingerprint()).copied();
            match (canon_current, canon_next) {
                (Some(c1), Some(c2)) => Ok(c1 != c2),
                _ => Ok(current.fingerprint() != next.fingerprint()),
            }
        } else {
            Ok(current.fingerprint() != next.fingerprint())
        }
    }

    fn eval_subscript_changed(
        &self,
        ctx: &EvalCtx,
        current: &State,
        next: &State,
        sub_expr: &Arc<Spanned<Expr>>,
        tag: u32,
    ) -> EvalResult<bool> {
        super::subscript_cache::eval_subscript_changed(ctx, current, next, sub_expr, Some(tag))
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
        let state_successors = self.state_successors;
        let state_successor_fps = self.state_successor_fps;
        let state_fp_to_canon_fp = self.state_fp_to_canon_fp;
        let succ_witnesses = self.succ_witnesses;
        let graph = self.graph;
        let registry = self.registry;
        super::eval_enabled_cached(ctx, current_state.fingerprint(), tag, || {
            let owned_successors = enabled_successors(
                state_fp_to_canon_fp,
                succ_witnesses,
                state_successors,
                state_successor_fps,
                graph,
                registry,
                current_state.fingerprint(),
            );
            let cached_successors = owned_successors.as_slice();
            crate::liveness::enabled_eval::eval_enabled_uncached(
                crate::liveness::enabled_eval::EnabledEvalRequest {
                    ctx_current: ctx,
                    current_state,
                    action,
                    bindings: bindings.as_ref(),
                    require_state_change,
                    subscript: subscript.as_ref(),
                    cached_successors,
                },
                |eval_ctx, s1, s2, sub_expr| {
                    super::subscript_cache::eval_subscript_changed(eval_ctx, s1, s2, sub_expr, None)
                },
            )
        })
    }
}

impl LivenessChecker {
    #[cfg(test)]
    pub(super) fn eval_check_on_state(
        &mut self,
        check: &LiveExpr,
        state: &State,
    ) -> EvalResult<bool> {
        self.eval_live_check_expr(check, state, None, None)
    }

    /// Evaluate ALL action checks for a single transition in one state-binding epoch.
    ///
    /// Sets up state bindings once and evaluates all used checks, producing a bitmask.
    /// This keeps the evaluator's SUBST_CACHE warm across checks for the same transition,
    /// avoiding redundant INSTANCE chain resolution. For EWD998ChanID with 3-level INSTANCE
    /// nesting, this reduces SUBST_CACHE clearances from N_checks × N_transitions to
    /// N_transitions, providing ~5-10× speedup in populate_node_check_masks (#2364).
    ///
    /// Falls back to per-check evaluation when symmetry is active (different witness
    /// expansion per check) or when VarRegistry is empty (test fallback path).
    /// Returns a `CheckMask` supporting >64 check indices (#2890).
    #[cfg(test)]
    pub(super) fn eval_action_checks_batched(
        &mut self,
        checks: &[LiveExpr],
        used: &[bool],
        current_state: &State,
        next_state: &State,
    ) -> EvalResult<CheckMask> {
        // Symmetry witnesses require per-check witness expansion; fall back to individual eval.
        // VIEW-only (no witnesses) uses the batched array-based path for SUBST_CACHE warmth.
        if self.succ_witnesses.is_some() {
            let mut mask = CheckMask::new();
            for (check_idx, check) in checks.iter().enumerate() {
                if !used.get(check_idx).copied().unwrap_or(false) {
                    continue;
                }
                if self.eval_check_on_transition(check, current_state, next_state)? {
                    mask.set(check_idx);
                }
            }
            return Ok(mask);
        }

        let registry_is_empty = self.ctx.var_registry().is_empty();

        if !registry_is_empty {
            let cached_next_env = self.get_cached_env(next_state);
            let registry_cloned = self.ctx.var_registry().clone();
            let current_values = current_state.to_values(&registry_cloned);
            let next_values = next_state.to_values(&registry_cloned);

            // Bind state arrays ONCE for all checks in this batch.
            let _state_guard = self.ctx.bind_state_array_guard(&current_values);

            let _next_state_guard = self.ctx.take_next_state_guard();
            let _next_guard = self.ctx.take_next_state_env_guard();
            *self.ctx.next_state_mut() = Some(cached_next_env);
            self.ctx.bind_next_state_array(&next_values);

            let mut mask = CheckMask::new();
            for (check_idx, check) in checks.iter().enumerate() {
                if !used.get(check_idx).copied().unwrap_or(false) {
                    continue;
                }
                if self.eval_live_check_expr_inner(check, current_state, Some(next_state), None)? {
                    mask.set(check_idx);
                }
            }

            Ok(mask)
        } else {
            // Fallback: evaluate each check individually
            let mut mask = CheckMask::new();
            for (check_idx, check) in checks.iter().enumerate() {
                if !used.get(check_idx).copied().unwrap_or(false) {
                    continue;
                }
                if self.eval_check_on_transition(check, current_state, next_state)? {
                    mask.set(check_idx);
                }
            }
            Ok(mask)
        }
    }

    #[cfg(test)]
    pub(super) fn eval_check_on_transition(
        &mut self,
        check: &LiveExpr,
        state0: &State,
        state1: &State,
    ) -> EvalResult<bool> {
        // Under symmetry, a reduced edge (state0 -> state1) can represent multiple concrete
        // successor states. Evaluate the check existentially over all concrete witnesses.
        // Clone the Arc references we need to avoid borrow issues
        let fp_map = self.state_fp_to_canon_fp.clone();
        let witnesses = self.succ_witnesses.clone();
        if let (Some(fp_map), Some(witnesses)) = (fp_map, witnesses) {
            let fp0 = state0.fingerprint();
            let fp1 = state1.fingerprint();

            let Some(canon0) = fp_map.get(&fp0).copied() else {
                return self.eval_live_check_expr(check, state0, Some(state1), None);
            };
            let Some(canon1) = fp_map.get(&fp1).copied() else {
                return self.eval_live_check_expr(check, state0, Some(state1), None);
            };

            // The reduced graph always contains an explicit stuttering self-loop (s -> s).
            if canon0 == canon1 && self.eval_live_check_expr(check, state0, Some(state0), None)? {
                return Ok(true);
            }

            if let Some(succs) = witnesses.get(&canon0) {
                let registry = self.ctx.var_registry().clone();
                for (dest_canon_fp, succ_arr) in succs {
                    if *dest_canon_fp != canon1 {
                        continue;
                    }
                    // Part of #2661: Convert ArrayState→State on this test-only path.
                    let succ_state = succ_arr.to_state(&registry);
                    if self.eval_live_check_expr(check, state0, Some(&succ_state), None)? {
                        return Ok(true);
                    }
                }
            }

            // No concrete candidate satisfied the check.
            return Ok(false);
        }

        self.eval_live_check_expr(check, state0, Some(state1), None)
    }

    /// Evaluate a liveness check expression against current (and optionally next) state.
    ///
    /// Optimized to use array-based state binding via `bind_state_array` when the
    /// VarRegistry is populated. Falls back to HashMap-based binding when the
    /// registry is empty (e.g., in tests with minimal setup).
    pub(super) fn eval_live_check_expr(
        &mut self,
        expr: &LiveExpr,
        current_state: &State,
        next_state: Option<&State>,
        tir: Option<&TirProgram<'_>>,
    ) -> EvalResult<bool> {
        // Get cached next_state Env upfront (avoids repeated HashMap construction)
        let cached_next_env = next_state.map(|ns| self.get_cached_env(ns));

        let registry = self.ctx.var_registry();

        // Use optimized array-based path if VarRegistry is populated
        if !registry.is_empty() {
            let registry_cloned = registry.clone();
            let current_values = current_state.to_values(&registry_cloned);
            // BUG FIX #1096: Declare next_values at same scope as current_values so it
            // outlives the bind_next_state_array reference. Previously next_values was
            // declared inside an if block and dropped before eval_live_check_expr_inner
            // finished, causing a use-after-free (dangling StateEnvRef pointer).
            let next_values = next_state.map(|ns| ns.to_values(&registry_cloned));

            // Save current state_env and bind new one (O(1) pointer swap)
            let _state_guard = self.ctx.bind_state_array_guard(&current_values);

            // Save current next_state and set new one if provided (using cached Env)
            let prev_next_state = self.ctx.next_state_mut().take();
            let _next_guard = self.ctx.take_next_state_env_guard();
            if let Some(env) = cached_next_env.clone() {
                *self.ctx.next_state_mut() = Some(env);
            }
            // BUG FIX #1089: Also bind array-based next_state_env for INSTANCE'd property
            // checking. Complex primed expressions (e.g., in INSTANCE substitutions) use
            // the fallback path in core.rs that swaps state_env with next_state_env.
            if let Some(ref nv) = next_values {
                self.ctx.bind_next_state_array(nv);
            }

            let result = self.eval_live_check_expr_inner(expr, current_state, next_state, tir);

            // _next_guard and _state_guard restore array envs on drop
            *self.ctx.next_state_mut() = prev_next_state;

            result
        } else {
            // Fallback: Use HashMap-based binding for empty VarRegistry (e.g., minimal tests)
            // Bind current state variables to env
            let prev_env = self.ctx.env().clone();
            for (name, value) in current_state.vars() {
                self.ctx.bind_mut(Arc::clone(name), value.clone());
            }

            // Save current next_state and set new one if provided (using cached Env)
            let prev_next_state = self.ctx.next_state_mut().take();
            if let Some(env) = cached_next_env {
                *self.ctx.next_state_mut() = Some(env);
            }

            let result = self.eval_live_check_expr_inner(expr, current_state, next_state, tir);

            // Restore previous state
            *self.ctx.env_mut() = prev_env;
            *self.ctx.next_state_mut() = prev_next_state;

            result
        }
    }

    /// Inner recursive evaluation of liveness check expressions.
    ///
    /// Delegates to the shared [`eval_live_expr_core`] with a [`CheckerEvaluator`]
    /// that provides symmetry-aware comparison, cached subscript evaluation, and
    /// HashMap-based successor lookup.
    ///
    /// Uses `self.ctx` which has been pre-configured with:
    /// - `state_env` pointing to current state values
    /// - `next_state` set if action context is needed
    pub(super) fn eval_live_check_expr_inner(
        &self,
        expr: &LiveExpr,
        current_state: &State,
        next_state: Option<&State>,
        tir: Option<&TirProgram<'_>>,
    ) -> EvalResult<bool> {
        let registry = self.ctx.var_registry();
        let mut evaluator = CheckerEvaluator {
            state_fp_to_canon_fp: &self.state_fp_to_canon_fp,
            succ_witnesses: &self.succ_witnesses,
            state_successors: &self.state_successors,
            state_successor_fps: &self.state_successor_fps,
            graph: &self.graph,
            registry,
        };
        eval_live_expr_core(
            &mut evaluator,
            &self.ctx,
            expr,
            current_state,
            next_state,
            tir,
        )
    }

    pub(super) fn eval_enabled(
        &self,
        ctx_current: &EvalCtx,
        current_state: &State,
        action: &std::sync::Arc<tla_core::Spanned<tla_core::ast::Expr>>,
        bindings: Option<&crate::eval::BindingChain>,
        require_state_change: bool,
        subscript: Option<&std::sync::Arc<tla_core::Spanned<tla_core::ast::Expr>>>,
    ) -> EvalResult<bool> {
        let registry = self.ctx.var_registry();
        let owned_successors = enabled_successors(
            &self.state_fp_to_canon_fp,
            &self.succ_witnesses,
            &self.state_successors,
            &self.state_successor_fps,
            &self.graph,
            registry,
            current_state.fingerprint(),
        );
        let cached_successors = owned_successors.as_slice();
        super::super::enabled_eval::eval_enabled_uncached(
            super::super::enabled_eval::EnabledEvalRequest {
                ctx_current,
                current_state,
                action,
                bindings,
                require_state_change,
                subscript,
                cached_successors,
            },
            |ctx, s1, s2, sub_expr| {
                super::subscript_cache::eval_subscript_changed(ctx, s1, s2, sub_expr, None)
            },
        )
    }
}
