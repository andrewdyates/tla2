// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ENABLED evaluation helpers for the EA precompute pass (#2572, #2364).
//!
//! Extracted from `ea_precompute.rs` to stay under the 500-line file limit.
//! Contains the `EnabledInfo` struct, tree-walking collectors, and the
//! array-based + fallback ENABLED evaluation methods used by
//! `populate_node_check_masks`.

use super::live_expr::LiveExpr;
use super::LivenessChecker;
use crate::state::Fingerprint;

/// Information about an ENABLED sub-expression extracted from check expressions.
///
/// Used by `populate_node_check_masks` and the `eval_enabled_array_fast`/
/// `eval_enabled_fallback` helper methods.
pub(super) struct EnabledInfo {
    pub(super) action: std::sync::Arc<tla_core::Spanned<tla_core::ast::Expr>>,
    pub(super) bindings: Option<crate::eval::BindingChain>,
    pub(super) require_state_change: bool,
    pub(super) subscript: Option<std::sync::Arc<tla_core::Spanned<tla_core::ast::Expr>>>,
    pub(super) tag: u32,
}

/// Walk a `LiveExpr` tree and collect all `ENABLED` sub-expressions.
pub(super) fn collect_enabled_nodes(expr: &LiveExpr, out: &mut Vec<EnabledInfo>) {
    match expr {
        LiveExpr::Enabled {
            action,
            bindings,
            require_state_change,
            subscript,
            tag,
        } => {
            out.push(EnabledInfo {
                action: std::sync::Arc::clone(action),
                bindings: bindings.clone(),
                require_state_change: *require_state_change,
                subscript: subscript.clone(),
                tag: *tag,
            });
        }
        LiveExpr::And(parts) | LiveExpr::Or(parts) => {
            for p in parts {
                collect_enabled_nodes(p, out);
            }
        }
        LiveExpr::Not(inner) => collect_enabled_nodes(inner, out),
        _ => {}
    }
}

impl LivenessChecker {
    /// Evaluate ENABLED using array-based state binding fast path (#2364).
    ///
    /// State arrays must already be bound to `from_state` via `bind_state_array_guard`.
    /// Iterates cached successors with array-based next_state binding for each,
    /// sharing the SUBST_CACHE warmth from the caller's binding epoch.
    ///
    /// After exhaustive BFS, `cached_succs` contains ALL reachable successor states.
    /// Any action-specific successor is a subset of these. Therefore, if no cached
    /// successor satisfies the ENABLED condition, ENABLED is false — no fallback to
    /// `enumerate_action_successors` is needed. This eliminates the O(|Next| × eval_cost)
    /// re-enumeration that dominated liveness checking time for INSTANCE-heavy specs.
    ///
    /// Ref: TLC's `LiveCheck.java` — ENABLED uses pre-computed successor arrays
    /// from the state graph, never re-enumerates.
    pub(super) fn eval_enabled_array_fast(
        ctx: &mut crate::eval::EvalCtx,
        info: &EnabledInfo,
        from_state: &crate::state::State,
        from_fp: Fingerprint,
        cached_succs: &[crate::state::State],
        succ_envs: &[std::sync::Arc<crate::eval::Env>],
        registry: &tla_core::VarRegistry,
    ) -> crate::error::EvalResult<bool> {
        // Iterate all cached successors (complete from exhaustive BFS).
        for (succ_idx, succ) in cached_succs.iter().enumerate() {
            let succ_fp = succ.fingerprint();

            // For require_state_change=true: skip successors where subscript
            // is unchanged (stuttering steps).
            if info.require_state_change {
                if info.subscript.is_some() {
                    match super::subscript_cache::check_subscript_changed_cached(
                        from_fp, succ_fp, info.tag,
                    ) {
                        Some(false) => continue,
                        Some(true) => {}
                        None => {
                            // Cache miss: fall back to full ENABLED evaluation.
                            // This should not happen when pre-population is correct.
                            return Self::eval_enabled_fallback(
                                ctx,
                                info,
                                from_state,
                                cached_succs,
                            );
                        }
                    }
                } else if succ_fp == from_fp {
                    continue;
                }
            }

            // Bind next_state arrays (SUBST_CACHE stays warm for from_state).
            let next_values = succ.to_values(registry);
            let prev_next = ctx.next_state_mut().take();
            let _next_guard = ctx.take_next_state_env_guard();
            *ctx.next_state_mut() = Some(std::sync::Arc::clone(&succ_envs[succ_idx]));
            ctx.bind_next_state_array(&next_values);

            // Evaluate action expression with array binding.
            // Part of #2895: BindingChain bindings survive closure/function entry.
            let eval_ctx = match info.bindings {
                Some(ref chain) => ctx.with_liveness_bindings(chain),
                None => ctx.clone(),
            };
            match crate::eval::eval_entry(&eval_ctx, &info.action) {
                Ok(value) => {
                    *ctx.next_state_mut() = prev_next;
                    if crate::liveness::boolean_contract::expect_live_bool(
                        &value,
                        Some(info.action.span),
                    )? {
                        return Ok(true);
                    }
                }
                Err(e) if crate::enumerate::is_disabled_action_error(&e) => {
                    *ctx.next_state_mut() = prev_next;
                }
                Err(e) => {
                    *ctx.next_state_mut() = prev_next;
                    return Err(e);
                }
            }
        }

        // All cached successors exhausted with no match. After exhaustive BFS,
        // cached_succs contains every reachable successor state. Any state
        // reachable via the specific action A is a subset of these successors.
        // Therefore ENABLED(<<A>>_v) is false — no need for the expensive
        // enumerate_action_successors fallback (#2364).
        Ok(false)
    }

    /// Dispatch ENABLED evaluation for a node, trying full-state then fingerprint paths.
    ///
    /// Unified entry point used by `populate_node_check_masks` to avoid duplicating
    /// the state-successors vs fingerprint-successors dispatch logic inline.
    pub(super) fn eval_enabled_for_node(
        &mut self,
        info: &EnabledInfo,
        from_state: &crate::state::State,
        from_fp: Fingerprint,
        registry: &tla_core::VarRegistry,
    ) -> crate::error::EvalResult<bool> {
        if let Some(succs) = self.state_successors.get(&from_fp).cloned() {
            let succ_envs: Vec<std::sync::Arc<crate::eval::Env>> =
                succs.iter().map(|s| self.get_cached_env(s)).collect();
            Self::eval_enabled_array_fast(
                &mut self.ctx,
                info,
                from_state,
                from_fp,
                &succs,
                &succ_envs,
                registry,
            )
        } else if let Some(succ_fps) = self.state_successor_fps.get(&from_fp).cloned() {
            self.eval_enabled_array_fast_from_fps(info, from_state, from_fp, &succ_fps, registry)
        } else {
            Ok(false)
        }
    }

    /// Evaluate ENABLED using successor fingerprints backed by the shared graph cache.
    ///
    /// This preserves the fingerprint-only direct graph path from #3065 by
    /// resolving successor states lazily instead of rebuilding `Vec<State>`
    /// after exploration.
    pub(super) fn eval_enabled_array_fast_from_fps(
        &mut self,
        info: &EnabledInfo,
        from_state: &crate::state::State,
        from_fp: Fingerprint,
        cached_succ_fps: &[Fingerprint],
        registry: &tla_core::VarRegistry,
    ) -> crate::error::EvalResult<bool> {
        for &succ_fp in cached_succ_fps {
            if info.require_state_change {
                if info.subscript.is_some() {
                    match super::subscript_cache::check_subscript_changed_cached(
                        from_fp, succ_fp, info.tag,
                    ) {
                        Some(false) => continue,
                        Some(true) => {}
                        None => {
                            return Self::eval_enabled_fallback(
                                &self.ctx,
                                info,
                                from_state,
                                &self.successor_states_for_enabled(from_fp),
                            );
                        }
                    }
                } else if succ_fp == from_fp {
                    if self.succ_witnesses.is_some() {
                        return Self::eval_enabled_fallback(
                            &self.ctx,
                            info,
                            from_state,
                            &self.successor_states_for_enabled(from_fp),
                        );
                    }
                    continue;
                }
            }

            // Part of #3746: When the graph's state cache doesn't contain the
            // successor state data, fall back to the full-state ENABLED evaluation
            // path which resolves successors via successor_states_for_enabled()
            // (filter_map over get_state_by_fp — gracefully skips missing fps).
            // This can happen in parallel mode when populate_state_successor_fps_from_graph
            // records successor fingerprints whose concrete state data is not available
            // in the shared state cache.
            let next_values = {
                let Some(succ) = self.graph.get_state_by_fp(succ_fp) else {
                    return Self::eval_enabled_fallback(
                        &self.ctx,
                        info,
                        from_state,
                        &self.successor_states_for_enabled(from_fp),
                    );
                };
                succ.to_values(registry)
            };

            let prev_next = self.ctx.next_state_mut().take();
            let _next_guard = self.ctx.take_next_state_env_guard();
            let cached_env = match self.get_cached_env_by_fp(succ_fp) {
                Ok(env) => env,
                Err(_) => {
                    // Same fallback: missing state data for env construction.
                    return Self::eval_enabled_fallback(
                        &self.ctx,
                        info,
                        from_state,
                        &self.successor_states_for_enabled(from_fp),
                    );
                }
            };
            *self.ctx.next_state_mut() = Some(cached_env);
            self.ctx.bind_next_state_array(&next_values);

            let eval_ctx = match info.bindings {
                Some(ref chain) => self.ctx.with_liveness_bindings(chain),
                None => self.ctx.clone(),
            };
            match crate::eval::eval_entry(&eval_ctx, &info.action) {
                Ok(value) => {
                    *self.ctx.next_state_mut() = prev_next;
                    if crate::liveness::boolean_contract::expect_live_bool(
                        &value,
                        Some(info.action.span),
                    )? {
                        return Ok(true);
                    }
                }
                Err(e) if crate::enumerate::is_disabled_action_error(&e) => {
                    *self.ctx.next_state_mut() = prev_next;
                }
                Err(e) => {
                    *self.ctx.next_state_mut() = prev_next;
                    return Err(e);
                }
            }
        }

        Ok(false)
    }

    /// Fallback ENABLED evaluation using HashMap-based state binding.
    ///
    /// Used when the array-based fast path cannot determine the result. This
    /// delegates to `eval_enabled_uncached` which clones the EvalCtx and uses
    /// HashMap-based state binding. Note: this invalidates SUBST_CACHE entries
    /// from the caller's array binding epoch.
    pub(super) fn eval_enabled_fallback(
        ctx: &crate::eval::EvalCtx,
        info: &EnabledInfo,
        from_state: &crate::state::State,
        cached_succs: &[crate::state::State],
    ) -> crate::error::EvalResult<bool> {
        // Part of #2895: Apply liveness bindings via BindingChain.
        let eval_ctx = match info.bindings {
            Some(ref chain) => ctx.with_liveness_bindings(chain),
            None => ctx.clone(),
        };
        super::super::enabled_eval::eval_enabled_uncached(
            super::super::enabled_eval::EnabledEvalRequest {
                ctx_current: &eval_ctx,
                current_state: from_state,
                action: &info.action,
                bindings: info.bindings.as_ref(),
                require_state_change: info.require_state_change,
                subscript: info.subscript.as_ref(),
                cached_successors: cached_succs,
            },
            |eval_ctx, s1, s2, sub_expr| {
                // Direct subscript evaluation for fallback (no cache dependency).
                // Fix #2780, Part of #3458: Clear eval-scope caches before evaluating
                // val1 via with_explicit_env (state_env=None, pointer 0). A prior closure
                // invocation's val2 evaluation may have left entries keyed on the same
                // pointer 0, causing stale hits. Upgraded from clear_subst_cache() to
                // clear_for_eval_scope_boundary() to also clear zero-arg, nary, and
                // INSTANCE-scoped LET caches that could be stale across re-binding.
                crate::eval::clear_for_eval_scope_boundary();
                let mut env1 = eval_ctx.env().clone();
                for (name, value) in s1.vars() {
                    // Part of #2144: skip state vars that shadow local bindings.
                    if !eval_ctx.has_local_binding(name.as_ref()) {
                        env1.insert(std::sync::Arc::clone(name), value.clone());
                    }
                }
                let ctx1 = eval_ctx.with_explicit_env(env1);
                let v1 = crate::eval::eval_entry(&ctx1, sub_expr)?;
                crate::eval::clear_for_eval_scope_boundary();
                let mut env2 = eval_ctx.env().clone();
                for (name, value) in s2.vars() {
                    // Part of #2144: skip state vars that shadow local bindings.
                    if !eval_ctx.has_local_binding(name.as_ref()) {
                        env2.insert(std::sync::Arc::clone(name), value.clone());
                    }
                }
                let ctx2 = eval_ctx.with_explicit_env(env2);
                let v2 = crate::eval::eval_entry(&ctx2, sub_expr)?;
                Ok(v1 != v2)
            },
        )
    }
}
