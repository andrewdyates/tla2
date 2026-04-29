// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! EvalCtx binding methods (`bind*`, `into_bind*`).
//!
//! Part of #2895: All binding methods write to BindingChain ONLY. The env
//! HashMap dual-write (Arc::make_mut + insert per binding) is eliminated.
//! This removes the O(n) HashMap clone that was the root cause of #1383.
//!
//! Part of #2955: local_stack Vec replaced by binding_depth counter.
//! BindingChain is the sole source of truth for local bindings.
//!
//! Extracted from core.rs to keep the main evaluation context definition concise.
//! Scope management methods (`with_*`, `without_*`) are in eval_ctx_scope.rs.

use super::core::{EvalCtx, OpEnv};
use crate::binding_chain::BindingValue;
use crate::value::Value;
use std::sync::Arc;
use tla_core::name_intern::{intern_name, NameId};

impl EvalCtx {
    // ========================= Binding Methods =========================

    /// Extend environment with a new binding.
    pub fn bind(&self, name: impl Into<Arc<str>>, value: Value) -> Self {
        let mut ctx = self.clone();
        ctx.bind_shadow_aware(self.local_ops.as_deref(), name.into(), value);
        ctx
    }

    /// Owned-consuming variant of `bind` — mutates in place, avoiding a clone.
    ///
    /// Part of #1383: Use when the caller already owns the `EvalCtx` and won't
    /// use it after binding. Saves one full struct clone per call.
    #[inline]
    pub fn into_bind(mut self, name: impl Into<Arc<str>>, value: Value) -> Self {
        let local_ops = self.local_ops.clone();
        self.bind_shadow_aware(local_ops.as_deref(), name.into(), value);
        self
    }

    /// Owned-consuming variant of `bind2` — mutates in place, avoiding a clone.
    ///
    /// Part of #1383: Use when the caller already owns the `EvalCtx`.
    #[inline]
    pub fn into_bind2(
        self,
        name1: impl Into<Arc<str>>,
        value1: Value,
        name2: impl Into<Arc<str>>,
        value2: Value,
    ) -> Self {
        self.into_bind_many([(name1.into(), value1), (name2.into(), value2)])
    }

    /// Owned-consuming variant of `bind3` — mutates in place, avoiding a clone.
    ///
    /// Part of #1383: Use when the caller already owns the `EvalCtx`.
    #[inline]
    pub fn into_bind3(
        self,
        name1: impl Into<Arc<str>>,
        value1: Value,
        name2: impl Into<Arc<str>>,
        value2: Value,
        name3: impl Into<Arc<str>>,
        value3: Value,
    ) -> Self {
        self.into_bind_many([
            (name1.into(), value1),
            (name2.into(), value2),
            (name3.into(), value3),
        ])
    }

    /// Extend environment with multiple bindings, preserving `bind()` shadowing semantics.
    ///
    /// This avoids constructing intermediate `EvalCtx` values for hot paths that
    /// previously chained `.bind(...).bind(...)` calls.
    pub fn bind_many(&self, bindings: impl IntoIterator<Item = (Arc<str>, Value)>) -> Self {
        let mut ctx = self.clone();
        let local_ops = self.local_ops.as_deref();

        for (name_arc, value) in bindings {
            ctx.bind_shadow_aware(local_ops, name_arc, value);
        }

        ctx
    }

    #[inline]
    pub(super) fn bind_shadow_aware(
        &mut self,
        _local_ops: Option<&OpEnv>,
        name_arc: Arc<str>,
        value: Value,
    ) {
        // Part of #2895 Step 2: Always push to BindingChain (unconditional).
        // Previously, chain push was conditional on shadowing — non-shadowing bindings
        // went to env HashMap only. Now BindingChain is the sole destination for all
        // local bindings, matching TLC's Context.cons() which always appends.
        // The env HashMap write is removed — it was the source of O(n) Arc::make_mut
        // clones on every binding operation (the #1383 root cause).
        let name_id = intern_name(name_arc.as_ref());
        let depth = self.binding_depth;
        self.bindings = self
            .bindings
            .cons_local(name_id, BindingValue::eager(value), depth);
        self.binding_depth += 1;
    }

    /// Two-parameter convenience wrapper around `bind_many` for hot operator paths.
    #[inline]
    pub fn bind2(
        &self,
        name1: impl Into<Arc<str>>,
        value1: Value,
        name2: impl Into<Arc<str>>,
        value2: Value,
    ) -> Self {
        self.bind_many([(name1.into(), value1), (name2.into(), value2)])
    }

    /// Owned-consuming variant of `bind_many` — mutates in place, avoiding a clone.
    ///
    /// Part of #1383: Use when the caller already owns the `EvalCtx` and won't
    /// use it after binding. Saves one full struct clone per call.
    #[inline]
    pub fn into_bind_many(mut self, bindings: impl IntoIterator<Item = (Arc<str>, Value)>) -> Self {
        let local_ops = self.local_ops.clone();
        let local_ops_ref = local_ops.as_deref();
        for (name_arc, value) in bindings {
            self.bind_shadow_aware(local_ops_ref, name_arc, value);
        }
        self
    }

    /// Three-parameter convenience wrapper around `bind_many` for indexed folds.
    #[inline]
    pub fn bind3(
        &self,
        name1: impl Into<Arc<str>>,
        value1: Value,
        name2: impl Into<Arc<str>>,
        value2: Value,
        name3: impl Into<Arc<str>>,
        value3: Value,
    ) -> Self {
        self.bind_many([
            (name1.into(), value1),
            (name2.into(), value2),
            (name3.into(), value3),
        ])
    }

    /// Extend environment with a new local binding.
    ///
    /// Part of #2895: Pushes to BindingChain only (no env HashMap write).
    /// Previously also wrote to env — that O(n) clone is eliminated.
    pub fn bind_local(&self, name: impl Into<Arc<str>>, value: Value) -> Self {
        let name_arc = name.into();
        let name_id = intern_name(name_arc.as_ref());
        let mut ctx = self.clone();
        let depth = ctx.binding_depth;
        ctx.bindings = ctx
            .bindings
            .cons_local(name_id, BindingValue::eager(value), depth);
        ctx.binding_depth += 1;
        ctx
    }

    /// Owned-consuming variant of `bind_local` — mutates in place, avoiding a clone.
    ///
    /// Part of #1383, #2895: Chain-only binding, no env HashMap write.
    #[inline]
    pub fn into_bind_local(mut self, name: impl Into<Arc<str>>, value: Value) -> Self {
        let name_arc = name.into();
        let name_id = intern_name(name_arc.as_ref());
        let depth = self.binding_depth;
        self.bindings = self
            .bindings
            .cons_local(name_id, BindingValue::eager(value), depth);
        self.binding_depth += 1;
        self
    }

    /// Owned-consuming variant using a pre-interned name/id pair.
    ///
    /// Part of #3395: name parameter removed — no longer stored in BindingNode.
    /// Part of #3805: Consider using `into_bind_by_id` to avoid the Arc::clone.
    #[inline]
    pub fn into_bind_local_preinterned(
        mut self,
        _name: Arc<str>,
        name_id: NameId,
        value: Value,
    ) -> Self {
        let depth = self.binding_depth;
        self.bindings = self
            .bindings
            .cons_local(name_id, BindingValue::eager(value), depth);
        self.binding_depth += 1;
        self
    }

    /// Owned-consuming bind using only NameId — zero Arc overhead.
    ///
    /// Part of #3805: Eliminates the unnecessary `Arc::clone` in
    /// `into_bind_local_preinterned` for callers that have a NameId.
    #[inline]
    pub fn into_bind_by_id(mut self, name_id: NameId, value: Value) -> Self {
        let depth = self.binding_depth;
        self.bindings = self
            .bindings
            .cons_local(name_id, BindingValue::eager(value), depth);
        self.binding_depth += 1;
        self
    }

    /// Rebind the current recursive parameter in place when the chain shape
    /// proves the old head is the previous parameter value.
    #[inline]
    pub(crate) fn try_rebind_recursive_local_preinterned(
        &mut self,
        name_id: NameId,
        self_name_id: NameId,
        value: Value,
    ) -> bool {
        self.bindings
            .try_rebind_recursive_param(name_id, self_name_id, value)
    }

    /// Extend environment with multiple bindings.
    ///
    /// Part of #2895: Chain-only binding, no env HashMap write.
    pub fn bind_all(&self, bindings: impl IntoIterator<Item = (Arc<str>, Value)>) -> Self {
        let mut ctx = self.clone();
        for (name, value) in bindings {
            let name_id = intern_name(name.as_ref());
            let depth = ctx.binding_depth;
            ctx.bindings = ctx
                .bindings
                .cons_local(name_id, BindingValue::eager(value), depth);
            ctx.binding_depth += 1;
        }
        ctx
    }

    /// Owned-consuming variant of `bind_all` — mutates in place, avoiding a clone.
    ///
    /// Part of #1383, #2895: Chain-only binding, no env HashMap write.
    #[inline]
    pub fn into_bind_all(mut self, bindings: impl IntoIterator<Item = (Arc<str>, Value)>) -> Self {
        for (name, value) in bindings {
            let name_id = intern_name(name.as_ref());
            let depth = self.binding_depth;
            self.bindings = self
                .bindings
                .cons_local(name_id, BindingValue::eager(value), depth);
            self.binding_depth += 1;
        }
        self
    }

    /// Bind operator parameters with pre-interned names and minimal overhead.
    ///
    /// Part of #3000: Extended from RECURSIVE-only to ALL user-defined operators.
    /// This is the critical hot path for operator application. Key optimizations:
    /// - No local_stack Vec clone (O(n) → O(1): just copy binding_depth)
    /// - BindingValue moved into chain (supports both Eager and Lazy bindings)
    /// - 1 Rc refcount bump for stable (vs ~10 Arc/Rc bumps + Option clones)
    /// - Accepts BindingValue (Eager or Lazy) instead of Value, enabling lazy
    ///   argument evaluation matching TLC LazyValue semantics.
    pub(crate) fn bind_preinterned(
        &self,
        bindings: impl IntoIterator<Item = (Arc<str>, BindingValue, NameId)>,
    ) -> Self {
        let mut binding_chain = self.bindings.clone();
        let mut depth = self.binding_depth;
        for (_interned, bv, name_id) in bindings {
            binding_chain = binding_chain.cons_local(name_id, bv, depth);
            depth += 1;
        }
        EvalCtx {
            stable: std::rc::Rc::clone(&self.stable),
            binding_depth: depth,
            call_by_name_subs: self.call_by_name_subs.clone(),
            tlc_action_context: self.tlc_action_context.clone(),
            recursion_depth: self.recursion_depth,
            active_lazy_func: self.active_lazy_func.clone(),
            bindings: binding_chain,
            let_def_overlay: self.let_def_overlay.clone(),
            sparse_next_state_env: self.sparse_next_state_env,
        }
    }

    /// Extend the EvalCtx with liveness quantifier bindings from a stored BindingChain.
    ///
    /// Each binding in `liveness_chain` is cons'd onto the current BindingChain.
    /// Mirrors TLC's `tool.eval(expr, getContext(), state)` pattern in LNStateAST.java:39.
    ///
    /// Part of #2895: Replaces `with_fast_bindings` + `write_to_env` pattern.
    /// BindingChain bindings survive closure/function entry (they're captured by closures),
    /// so no defensive `write_to_env` workaround is needed.
    pub fn with_liveness_bindings(
        &self,
        liveness_chain: &crate::binding_chain::BindingChain,
    ) -> Self {
        let mut ctx = self.clone();
        // Collect the eager bindings (reversed: chain is newest-first, we need oldest-first
        // to cons in correct order so that newer bindings shadow older ones).
        let entries: Vec<_> = liveness_chain.iter_eager().collect();
        for (name_id, _name_str, value) in entries.into_iter().rev() {
            ctx.bindings = ctx.bindings.cons_liveness_local(
                name_id,
                crate::binding_chain::BindingValue::eager(value),
                ctx.binding_depth,
            );
            ctx.binding_depth += 1;
        }
        ctx
    }
}
