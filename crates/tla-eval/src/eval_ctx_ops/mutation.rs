// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EvalCtx context mutation methods: state-switch constructors, action context
//! cache, and environment manipulation. Part of #2764 / #1643.

use crate::cache::clear_for_eval_scope_boundary;
use crate::eval_cache_lifecycle::enter_eval_boundary;
use crate::eval_ctx_guards::ExplicitNextStateGuard;
use crate::{
    invalidate_state_identity_tracking_with_ctx, Env, EvalCtx, NextStateMutGuard,
    StateIdentityGuard,
};
use std::cell::RefCell;
use std::sync::Arc;
use tla_core::ast::OperatorDef;

// Thread-local cache for `TlcActionContext` per `OperatorDef` pointer.
//
// Part of #3364: `install_outermost_tlc_action_context` was rebuilding the same
// context (name + params) on every action evaluation — 6.7M times in a 20k-state
// bosco sample (9.9% of total allocations). The context depends only on the
// operator definition's name and zero-arity params, which are fixed at parse time.
// Caching by def pointer reduces this to ~N allocations (one per distinct operator).
thread_local! {
    static ACTION_CTX_CACHE: RefCell<rustc_hash::FxHashMap<usize, Arc<crate::core::TlcActionContext>>> =
        RefCell::new(rustc_hash::FxHashMap::default());
}

/// Clear the action context cache. Called during `reset_global_state`.
pub fn clear_action_ctx_cache() {
    ACTION_CTX_CACHE.with(|cache| cache.borrow_mut().clear());
}

impl EvalCtx {
    // ---- Context mutation methods ----

    /// Set next_state, clearing array-based next_state_env. Part of #1383.
    /// Part of #3407: Permanently advances hoist state generation (no RAII restore).
    pub fn set_next_state(&mut self, next_state: Env) {
        crate::cache::advance_hoist_state_generation_ctx(self);
        invalidate_state_identity_tracking_with_ctx(self);
        let s = self.stable_mut();
        s.next_state = Some(Arc::new(next_state));
        s.next_state_env = None;
        self.tlc_action_context = None;
    }

    /// Create a context with explicit environment bindings, clearing state_env.
    pub fn with_explicit_env(&self, env: Env) -> Self {
        let mut ctx = self.clone();
        let s = ctx.stable_mut();
        s.env = Arc::new(env);
        s.next_state = None;
        s.state_env = None;
        s.next_state_env = None;
        ctx.tlc_action_context = None;
        ctx
    }

    /// Bind explicit next-state bindings for the current scope and restore the
    /// previous explicit/array-backed next-state view on drop.
    ///
    /// Part of #3460: successor-evaluation paths need a temporary explicit
    /// `next_state` without routing through `with_next_state_for_eval_scope()`,
    /// which performs a global eval-scope cache clear. This guard provides the
    /// same safety properties as the array-state guards without that broad clear.
    #[allow(dead_code)] // Tested in eval_ctx_guards tests; not yet adopted by tla-check callers.
    pub(crate) fn bind_explicit_next_state_guard(
        &mut self,
        next_state: impl Into<Arc<Env>>,
    ) -> ExplicitNextStateGuard {
        let hoist_guard = crate::cache::bump_hoist_state_generation_ctx(self);
        let state_identity_guard = StateIdentityGuard::new_with_ctx(self);
        let stable = self.stable_mut();
        let prev_next_state_env = stable.next_state_env.take();
        let prev_next_state = stable.next_state.replace(next_state.into());
        self.tlc_action_context = None;
        ExplicitNextStateGuard {
            ctx: self as *mut EvalCtx,
            prev_next_state,
            prev_next_state_env,
            _hoist_guard: hoist_guard,
            _state_identity_guard: state_identity_guard,
        }
    }

    /// Create a context view with no current-state and no next-state bindings (TLCState.Empty).
    /// Part of #858, #1383.
    pub fn without_state_and_next(&self) -> Self {
        let mut ctx = self.clone();
        let s = ctx.stable_mut();
        s.next_state = None;
        s.state_env = None;
        s.next_state_env = None;
        ctx.tlc_action_context = None;
        ctx
    }

    #[inline]
    pub(crate) fn in_tlc_action_scope(&self) -> bool {
        self.next_state.is_some() || self.next_state_env.is_some()
    }

    #[inline]
    pub(crate) fn tlc_action_context(&self) -> Option<&crate::core::TlcActionContext> {
        self.tlc_action_context.as_deref()
    }

    pub(crate) fn install_outermost_tlc_action_context(&mut self, def: &OperatorDef) {
        if !self.in_tlc_action_scope() || self.tlc_action_context.is_some() {
            return;
        }
        // Part of #3364: Cache the TlcActionContext per OperatorDef pointer.
        // The context (name + zero-arity params) is fixed at parse time and
        // identical across all evaluations of the same operator. Previously
        // rebuilt on every call — 6.7M times (9.9% of allocations) in bosco 20k.
        let key = def as *const OperatorDef as usize;
        let cached = ACTION_CTX_CACHE.with(|cache| {
            let map = cache.borrow();
            map.get(&key).map(Arc::clone)
        });
        self.tlc_action_context = Some(cached.unwrap_or_else(|| {
            let ctx = Arc::new(crate::core::TlcActionContext {
                name: Arc::from(def.name.node.as_str()),
                params: Arc::from(
                    def.params
                        .iter()
                        .filter(|param| param.arity == 0)
                        .map(|param| Arc::from(param.name.node.as_str()))
                        .collect::<Vec<_>>(),
                ),
            });
            ACTION_CTX_CACHE.with(|cache| {
                cache.borrow_mut().insert(key, Arc::clone(&ctx));
            });
            ctx
        }));
    }

    /// Clear the HashMap-based `next_state` and return an RAII guard that
    /// restores it on drop. Part of #3421.
    ///
    /// Prefer this over manual `let prev = ctx.next_state_mut().take()` /
    /// `*ctx.next_state_mut() = prev` patterns because this is early-return-safe.
    /// Also calls `invalidate_state_identity_tracking()` on drop because
    /// changing `next_state` can affect primed-variable resolution paths that
    /// interact with the eval cache.
    pub fn take_next_state_guard(&mut self) -> NextStateMutGuard {
        let prev = self.stable_mut().next_state.take();
        invalidate_state_identity_tracking_with_ctx(self);
        NextStateMutGuard {
            ctx: self as *mut EvalCtx,
            prev,
        }
    }

    // ---- State-env constructors ----

    /// Create context with next-state bindings for primed variable resolution
    pub fn with_next_state(&self, next_state: Env) -> Self {
        let mut ctx = self.clone();
        let s = ctx.stable_mut();
        s.next_state = Some(Arc::new(next_state));
        s.next_state_env = None;
        ctx.tlc_action_context = None;
        ctx
    }

    /// Create context with different state_env / next_state_env.
    ///
    /// This is the raw constructor — it does NOT establish a cache boundary.
    /// Prefer [`with_state_envs_for_eval`] when the clone will be used for
    /// direct `eval()` calls (e.g., SetPred captured-state restoration).
    pub(crate) fn with_state_envs(
        &self,
        state_env: Option<crate::StateEnvRef>,
        next_state_env: Option<crate::StateEnvRef>,
    ) -> Self {
        let mut ctx = self.clone();
        let s = ctx.stable_mut();
        s.state_env = state_env;
        s.next_state_env = next_state_env;
        ctx
    }

    /// Create context with different state_env / next_state_env and establish
    /// a cache boundary.
    ///
    /// Part of #3416: For clone-based state-array switches that bypass the
    /// mutable guard APIs (`bind_*_guard`, `set_next_state`). The existing
    /// `eval_entry` state-identity tracker sees `state_env` / `next_state_env`,
    /// so we reuse the precise `enter_eval_boundary()` logic.
    ///
    /// Use this instead of raw `with_state_envs()` when the returned context
    /// will be used for direct `eval()` calls that skip `eval_entry()`.
    pub(crate) fn with_state_envs_for_eval(
        &self,
        state_env: Option<crate::StateEnvRef>,
        next_state_env: Option<crate::StateEnvRef>,
    ) -> Self {
        let ctx = self.with_state_envs(state_env, next_state_env);
        enter_eval_boundary(&ctx);
        ctx
    }

    /// Create context with next-state bindings and establish a conservative
    /// eval-scope cache boundary.
    ///
    /// Part of #3416: `with_next_state()` sets `next_state` (explicit `Env`),
    /// which is NOT visible to the `eval_entry` state-identity pointer tracker
    /// (that only sees `state_env` / `next_state_env`). So instead of the
    /// precise pointer-identity check, we conservatively clear eval-scope
    /// caches and invalidate state-identity tracking.
    ///
    /// Use this instead of raw `with_next_state()` when the returned context
    /// will be used for `eval()` or `eval_leaf()` calls that skip `eval_entry()`.
    pub fn with_next_state_for_eval_scope(&self, next_state: Env) -> Self {
        let ctx = self.with_next_state(next_state);
        clear_for_eval_scope_boundary();
        // Part of #3962: Use ctx-aware variant — the new ctx shares the same
        // Rc<EvalRuntimeState> so its shadow is kept in sync.
        invalidate_state_identity_tracking_with_ctx(&ctx);
        ctx
    }
}
