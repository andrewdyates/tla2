// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! EvalCtx scope management methods (`with_*`, `without_*`).
//!
//! Extracted from eval_ctx_bind.rs to keep files under 500 LOC.
//! Contains methods for managing operator scopes, INSTANCE substitutions,
//! and module-level binding contexts.

use super::core::{EvalCtx, OpEnv};
use crate::binding_chain::BindingValue;
use crate::cache::scope_ids::{compute_instance_subs_id, compute_local_ops_scope_id};
use crate::value::Value;
use std::sync::Arc;
use tla_core::ast::Substitution;
use tla_core::name_intern::intern_name;

impl EvalCtx {
    // ========================= Scope Management =========================

    /// Create a context with local operator definitions (for LET expressions)
    pub fn with_local_ops(&self, local_ops: OpEnv) -> Self {
        let mut ctx = self.clone();
        let local_ops = Arc::new(local_ops);
        let id = compute_local_ops_scope_id(&local_ops);
        let s = ctx.stable_mut();
        s.local_ops = Some(local_ops);
        s.scope_ids.local_ops = id;
        ctx
    }

    /// Create a context with INSTANCE substitutions active for this scope.
    pub fn with_instance_substitutions(&self, subs: Vec<Substitution>) -> Self {
        let mut ctx = self.clone();
        let id = compute_instance_subs_id(&subs);
        let s = ctx.stable_mut();
        s.instance_substitutions = Some(Arc::new(subs));
        s.scope_ids.instance_substitutions = id;
        ctx
    }

    /// Get active INSTANCE substitutions for this scope.
    pub fn instance_substitutions(&self) -> Option<&[Substitution]> {
        self.stable
            .instance_substitutions
            .as_ref()
            .map(|v| v.as_slice())
    }

    /// Part of #188: Create a context with call-by-name substitutions for operators with primed parameters.
    ///
    /// This is the O(1) alternative to `apply_substitutions()` which does O(tree) AST rewriting.
    /// Instead of rewriting the AST, we store the substitutions in the context and resolve them
    /// during identifier evaluation.
    pub fn with_call_by_name_subs(&self, subs: Vec<Substitution>) -> Self {
        let mut ctx = self.clone();
        // Part of #2956: Now a hot field — direct set, no Rc::make_mut needed.
        ctx.call_by_name_subs = Some(Arc::new(subs));
        ctx
    }

    /// Part of #188: Get active call-by-name substitutions for this scope.
    pub fn call_by_name_subs(&self) -> Option<&[Substitution]> {
        // Part of #2956: Now a hot field on EvalCtx, not through stable Deref.
        self.call_by_name_subs.as_ref().map(|v| v.as_slice())
    }

    /// Part of #188: Create a context without call-by-name substitutions.
    ///
    /// Used when evaluating substitution expressions to avoid infinite recursion.
    /// Part of #2956: Now a hot field — direct set, no Rc::make_mut needed.
    /// Previously, each call triggered Rc::make_mut on EvalCtxStable (~16 Arc bumps).
    pub fn without_call_by_name_subs(&self) -> Self {
        let mut ctx = self.clone();
        ctx.call_by_name_subs = None;
        ctx
    }

    /// Create a context without INSTANCE substitutions.
    /// Used when evaluating substitution expressions (the RHS of WITH clauses)
    /// which are written in the outer module's context.
    pub fn without_instance_substitutions(&self) -> Self {
        let mut ctx = self.clone();
        let s = ctx.stable_mut();
        s.instance_substitutions = None;
        s.scope_ids.instance_substitutions = 0;
        s.eager_subst_bindings = None;
        s.skip_prime_validation = false;
        ctx.bindings = crate::binding_chain::BindingChain::empty();
        ctx
    }

    /// Create a context without local operator definitions.
    ///
    /// This is primarily used when evaluating operators from an outer module while inside an
    /// INSTANCE scope. The instanced module's operator namespace must not shadow outer-module
    /// operator bodies (e.g., a local `Node` operator shadowing an outer constant `Node`).
    pub fn without_local_ops(&self) -> Self {
        let mut ctx = self.clone();
        let s = ctx.stable_mut();
        s.local_ops = None;
        s.scope_ids.local_ops = 0;
        ctx
    }

    /// Create a context without INSTANCE-specific resolution metadata, preserving
    /// the current binding chain.
    ///
    /// Use this when the binding chain is already correct for the target scope:
    /// - Paths reachable only from `with_instance_scope()` where the chain is empty
    /// - LazyBinding forcing where the chain is the captured definition-site chain
    ///
    /// If the chain contains instance entries that would shadow outer-scope names,
    /// use [`with_outer_resolution_scope`] instead (which also restores
    /// `pre_scope_bindings`).
    ///
    /// Part of #3056 Phase 5: introduced alongside `with_outer_resolution_scope`
    /// for call sites where chain restoration is unnecessary.
    pub(crate) fn without_instance_resolution_scope(&self) -> Self {
        let mut ctx = self.clone();
        let s = ctx.stable_mut();
        s.instance_substitutions = None;
        s.scope_ids.instance_substitutions = 0;
        s.eager_subst_bindings = None;
        s.skip_prime_validation = false;
        s.local_ops = None;
        s.scope_ids.local_ops = 0;
        ctx
    }

    /// Rewind to the pre-INSTANCE resolution scope: clear INSTANCE metadata
    /// AND restore the binding chain / operator scope snapshots saved when an
    /// INSTANCE frame was entered.
    ///
    /// This is the explicit "outer-scope handle" that TLC keeps as the original
    /// context `c` alongside the extended substitution context `c1` in
    /// `evalImplSubstInKind` (Tool.java:1863-1872). TLA2 saves this handle as
    /// `pre_scope_bindings` and `pre_scope_local_ops` in
    /// `with_module_scope`/`with_module_scope_arced_subs` and
    /// `with_instance_scope`.
    ///
    /// # When to use this vs `without_instance_resolution_scope`
    ///
    /// - **`without_instance_resolution_scope`**: Use when the binding chain is
    ///   already correct (e.g., paths only reachable from `with_instance_scope()`
    ///   where the chain is already empty, or LazyBinding forcing where the chain
    ///   is the captured definition-site chain).
    ///
    /// - **`with_outer_resolution_scope`** (this method): Use when the binding
    ///   chain was rebuilt by `eval_module_ref` (via
    ///   `build_binding_chain_from_eager`/`build_lazy_subst_bindings`) and contains
    ///   instance substitution entries that would incorrectly shadow outer-scope
    ///   operators or variables. Restricted to 3 audited boundary sites:
    ///   - `eval_ident_shared_zero_arg_op`: shared zero-arg operator body eval
    ///   - `eval_statevar_implicit_instance_substitution`: implicit Ident eval
    ///   - `eval_module_ref_target` config override: override RHS eval
    ///
    /// Part of #3056 Phase 5: renamed from `without_instance_subs_and_local_ops`
    /// to describe semantics (boundary rewind) rather than mechanism (stripping).
    /// Reduced from 10 production call sites to exactly these 3 audited uses,
    /// which are intentional pre-INSTANCE boundary rewinds, not unfinished migration.
    pub fn with_outer_resolution_scope(&self) -> Self {
        let mut ctx = self.without_instance_resolution_scope();
        // Restore pre-INSTANCE scope bindings if available, preserving
        // outer-scope quantifier/param bindings through INSTANCE scope stripping.
        // Part of #3030: fixes MCYoYoPruning `Undefined variable: n` regression.
        ctx.bindings = ctx
            .pre_scope_bindings
            .clone()
            .unwrap_or_else(crate::binding_chain::BindingChain::empty);
        {
            let s = ctx.stable_mut();
            s.local_ops = s.pre_scope_local_ops.clone();
            s.scope_ids.local_ops = if s.local_ops.is_some() {
                crate::cache::scope_ids::INVALIDATED
            } else {
                0
            };
        }
        ctx
    }

    /// Create a context with module scope: local ops, bindings, and INSTANCE substitutions.
    ///
    /// Part of #1383: Eliminates the triple-clone in the common pattern
    /// `ctx.with_local_ops(ops).bind_all(bindings).with_instance_substitutions(subs)`.
    pub fn with_module_scope(
        &self,
        local_ops: OpEnv,
        bindings: impl IntoIterator<Item = (Arc<str>, Value)>,
        instance_substitutions: Vec<Substitution>,
    ) -> Self {
        self.with_module_scope_shared(Arc::new(local_ops), bindings, instance_substitutions)
    }

    /// Create a context with module scope using a pre-shared local operator map.
    ///
    /// This avoids cloning large `OpEnv` maps in hot paths where the same instance scope
    /// is entered repeatedly (for example, chained INSTANCE references).
    pub fn with_module_scope_shared(
        &self,
        local_ops: Arc<OpEnv>,
        bindings: impl IntoIterator<Item = (Arc<str>, Value)>,
        instance_substitutions: Vec<Substitution>,
    ) -> Self {
        let mut ctx = self.clone();
        // Part of #2991: Save pre-scope chain BEFORE pushing module-scope bindings.
        // build_eager_subst_bindings uses this to evaluate substitution RHS in the
        // outer-module context while preserving parametrized INSTANCE param bindings
        // (e.g., Succ in P(Succ) == INSTANCE M) that are on the chain from the caller.
        let pre_scope_chain = ctx.bindings.clone();
        // Part of #3056 Phase B: Save pre-scope local_ops before merging inner module ops.
        let pre_scope_local_ops = ctx.local_ops.clone();
        // Part of #3099: Compute stable scope ids at construction time.
        let local_ops_id = compute_local_ops_scope_id(&local_ops);
        let subs_id = if instance_substitutions.is_empty() {
            0
        } else {
            compute_instance_subs_id(&instance_substitutions)
        };
        {
            let s = ctx.stable_mut();
            s.local_ops = Some(local_ops);
            s.scope_ids.local_ops = local_ops_id;
        }
        // Part of #2991: Push module-scope bindings onto BindingChain instead of
        // mutating env HashMap. Eliminates O(env_size) Arc::make_mut deep clone.
        // The caller (eval_module_ref) rebuilds the BindingChain with INSTANCE
        // substitution bindings via build_binding_chain_from_eager, which replaces
        // these entries. They only need to persist through build_eager_subst_bindings.
        for (name, value) in bindings {
            let name_id = intern_name(name.as_ref());
            ctx.bindings =
                ctx.bindings
                    .cons_local(name_id, BindingValue::eager(value), ctx.binding_depth);
            ctx.binding_depth += 1;
        }
        // Normalize empty substitutions to None so eval_ident's fast path
        // is not blocked by Some(empty_vec).
        {
            let s = ctx.stable_mut();
            s.instance_substitutions = if instance_substitutions.is_empty() {
                None
            } else {
                Some(Arc::new(instance_substitutions))
            };
            s.scope_ids.instance_substitutions = subs_id;
            // eager_subst_bindings and bindings are set separately by eval_module_ref.
            s.eager_subst_bindings = None;
            s.pre_scope_bindings = Some(pre_scope_chain);
            s.pre_scope_local_ops = pre_scope_local_ops;
        }
        // Part of #2991: Do NOT reset chain to empty. Instance param bindings
        // (pushed by module_ref.rs parametrized handler) and operator param
        // bindings (pushed above) must persist through build_eager_subst_bindings.
        // The chain is replaced by build_binding_chain_from_eager after substitution
        // evaluation completes.
        ctx
    }

    /// Create a context with module scope using pre-wrapped Arc for substitutions.
    ///
    /// Fix #2364: Like `with_module_scope_shared`, but accepts an `Arc<Vec<Substitution>>`
    /// directly instead of creating a new Arc wrapper. This preserves the Arc pointer
    /// identity across calls, enabling stable SUBST_CACHE keys for chained INSTANCE refs.
    pub fn with_module_scope_arced_subs(
        &self,
        local_ops: Arc<OpEnv>,
        bindings: impl IntoIterator<Item = (Arc<str>, Value)>,
        instance_substitutions: Arc<Vec<Substitution>>,
    ) -> Self {
        let mut ctx = self.clone();
        // Part of #2991: Save pre-scope chain (see with_module_scope_shared).
        let pre_scope_chain = ctx.bindings.clone();
        // Part of #3056 Phase B: Save pre-scope local_ops (see with_module_scope_shared).
        let pre_scope_local_ops = ctx.local_ops.clone();
        // Part of #3099: Compute stable scope ids at construction time.
        let local_ops_id = compute_local_ops_scope_id(&local_ops);
        let subs_id = if instance_substitutions.is_empty() {
            0
        } else {
            compute_instance_subs_id(&instance_substitutions)
        };
        {
            let s = ctx.stable_mut();
            s.local_ops = Some(local_ops);
            s.scope_ids.local_ops = local_ops_id;
        }
        // Part of #2991: Push module-scope bindings onto BindingChain instead of
        // mutating env HashMap (see with_module_scope_shared for rationale).
        for (name, value) in bindings {
            let name_id = intern_name(name.as_ref());
            ctx.bindings =
                ctx.bindings
                    .cons_local(name_id, BindingValue::eager(value), ctx.binding_depth);
            ctx.binding_depth += 1;
        }
        // Normalize empty substitutions to None (see with_module_scope_shared).
        {
            let s = ctx.stable_mut();
            s.instance_substitutions = if instance_substitutions.is_empty() {
                None
            } else {
                Some(instance_substitutions)
            };
            s.scope_ids.instance_substitutions = subs_id;
            // eager_subst_bindings and bindings are set separately by eval_module_ref after this call
            s.eager_subst_bindings = None;
            s.pre_scope_bindings = Some(pre_scope_chain);
            s.pre_scope_local_ops = pre_scope_local_ops;
        }
        // Part of #2991: Do NOT reset chain (see with_module_scope_shared).
        ctx
    }

    /// Create a context with local ops and INSTANCE substitutions (no bindings).
    ///
    /// Part of #1383: Eliminates the double-clone in the common pattern
    /// `ctx.with_local_ops(ops).with_instance_substitutions(subs)`.
    pub fn with_instance_scope(
        &self,
        local_ops: OpEnv,
        instance_substitutions: Vec<Substitution>,
    ) -> Self {
        let mut ctx = self.clone();
        let pre_scope_chain = ctx.bindings.clone();
        let pre_scope_local_ops = ctx.local_ops.clone();
        // Part of #3099: Compute stable scope ids at construction time.
        let local_ops = Arc::new(local_ops);
        let local_ops_id = compute_local_ops_scope_id(&local_ops);
        let subs_id = if instance_substitutions.is_empty() {
            0
        } else {
            compute_instance_subs_id(&instance_substitutions)
        };
        let s = ctx.stable_mut();
        s.local_ops = Some(local_ops);
        s.scope_ids.local_ops = local_ops_id;
        // Normalize empty substitutions to None (see with_module_scope_shared).
        s.instance_substitutions = if instance_substitutions.is_empty() {
            None
        } else {
            Some(Arc::new(instance_substitutions))
        };
        s.scope_ids.instance_substitutions = subs_id;
        s.eager_subst_bindings = None;
        s.pre_scope_bindings = Some(pre_scope_chain);
        s.pre_scope_local_ops = pre_scope_local_ops;
        ctx.bindings = crate::binding_chain::BindingChain::empty();
        ctx
    }
}
