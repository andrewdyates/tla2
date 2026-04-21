// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! EvalCtx field accessors, shared-ctx convenience delegates, and scope guards.
//! Part of #2764 / #1643.

use crate::cache::bump_hoist_state_generation_ctx;
use crate::var_index::VarRegistry;
use crate::{Env, EvalCtx, HashMap, InstanceInfo, OpEnv, ScopeGuard, StateIdentityGuard, Value};
use std::sync::Arc;
use tla_core::name_intern::NameId;
use tla_core::span::Span;

impl EvalCtx {
    // ---- Field accessor methods (Part of #2739) ----
    // These provide controlled access to EvalCtx fields from downstream crates
    // (tla-check) after the fields are changed from `pub` to `pub(crate)`.

    /// Get a reference to the shared context.
    #[inline]
    pub fn shared(&self) -> &Arc<super::super::SharedCtx> {
        &self.shared
    }

    /// Get a mutable reference to the shared context Arc.
    ///
    /// Used with `Arc::make_mut()` for copy-on-write mutation of SharedCtx.
    #[inline]
    pub fn shared_arc_mut(&mut self) -> &mut Arc<super::super::SharedCtx> {
        &mut self.stable_mut().shared
    }

    /// Get a reference to the variable environment.
    #[inline]
    pub fn env(&self) -> &Env {
        &self.stable.env
    }

    /// Get a mutable reference to the variable environment (copy-on-write via Arc).
    /// Note: Arc::make_mut internally checks refcount — when refcount == 1, it
    /// returns a direct &mut with no clone (just an atomic CAS). The if-let-else
    /// Arc::get_mut pattern can't be used here due to borrow checker limitations
    /// with returning mutable references across branches.
    #[inline]
    pub fn env_mut(&mut self) -> &mut Env {
        Arc::make_mut(&mut self.stable_mut().env)
    }

    /// Get a reference to the next-state environment.
    #[inline]
    pub fn next_state(&self) -> &Option<Arc<Env>> {
        &self.stable.next_state
    }

    /// Get a mutable reference to the next-state environment.
    #[inline]
    pub fn next_state_mut(&mut self) -> &mut Option<Arc<Env>> {
        &mut self.stable_mut().next_state
    }

    /// Get a reference to the local operator definitions.
    #[inline]
    pub fn local_ops(&self) -> &Option<Arc<OpEnv>> {
        &self.stable.local_ops
    }

    /// Get a mutable reference to the local operator definitions.
    ///
    /// Part of #3099: Invalidates `scope_ids.local_ops` so that cache key
    /// builders lazily recompute the scope id from the mutated content.
    #[inline]
    pub fn local_ops_mut(&mut self) -> &mut Option<Arc<OpEnv>> {
        let s = self.stable_mut();
        s.scope_ids.local_ops = crate::cache::scope_ids::INVALIDATED;
        &mut s.local_ops
    }

    /// Check if prime validation should be skipped.
    #[inline]
    pub fn skip_prime_validation(&self) -> bool {
        self.stable.skip_prime_validation
    }

    /// Set whether prime validation should be skipped.
    #[inline]
    pub fn set_skip_prime_validation(&mut self, skip: bool) {
        self.stable_mut().skip_prime_validation = skip;
    }

    /// Get a reference to the variable registry
    #[inline]
    pub fn var_registry(&self) -> &VarRegistry {
        &self.shared.var_registry
    }

    /// Resolve operator name through replacements (for config `CONSTANT Op <- Replacement`)
    ///
    /// This is critical for compiled_guard.rs to properly handle operator replacements
    /// when extracting next-state assignments from actions.
    pub fn resolve_op_name<'a>(&'a self, name: &'a str) -> &'a str {
        self.shared
            .op_replacements
            .get(name)
            .map_or(name, std::string::String::as_str)
    }

    // ---- Scope guards ----

    /// RAII guard that saves `env` and restores on drop. Part of #2738.
    /// Part of #3407: Bumps hoist state generation for scope-level protection.
    pub fn scope_guard(&mut self) -> ScopeGuard {
        let hoist_guard = bump_hoist_state_generation_ctx(self);
        let saved_env = Arc::clone(&self.env);
        ScopeGuard {
            ctx: self as *mut EvalCtx,
            saved_env,
            saved_next_state: None,
            _hoist_guard: hoist_guard,
            _state_identity_guard: None,
        }
    }

    /// Create an RAII guard that saves both `env` and `next_state`, restoring
    /// both on drop.
    ///
    /// Use this variant when the code between save/restore also modifies
    /// `next_state` (common in liveness property checking).
    ///
    /// Part of #2738, #3407.
    pub fn scope_guard_with_next_state(&mut self) -> ScopeGuard {
        let hoist_guard = bump_hoist_state_generation_ctx(self);
        let saved_env = Arc::clone(&self.env);
        let saved_next = self.next_state.clone();
        ScopeGuard {
            ctx: self as *mut EvalCtx,
            saved_env,
            saved_next_state: Some(saved_next),
            _hoist_guard: hoist_guard,
            _state_identity_guard: Some(StateIdentityGuard::restore_only()),
        }
    }

    // ---- Convenience shared-ctx accessors ----

    #[inline]
    pub fn ops(&self) -> &OpEnv {
        &self.shared.ops
    }
    #[inline]
    pub fn instances(&self) -> &HashMap<String, InstanceInfo> {
        &self.shared.instances
    }
    #[inline]
    pub fn instance_ops(&self) -> &HashMap<String, OpEnv> {
        &self.shared.instance_ops
    }
    #[inline]
    pub fn op_replacements(&self) -> &HashMap<String, String> {
        &self.shared.op_replacements
    }
    #[inline]
    pub fn precomputed_constants(&self) -> &HashMap<NameId, Value> {
        self.shared.precomputed_constants()
    }
    #[inline]
    pub fn is_action_subscript_span(&self, span: Span) -> bool {
        self.shared.action_subscript_spans.contains(&span)
    }
}
