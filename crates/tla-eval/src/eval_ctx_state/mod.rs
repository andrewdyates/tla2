// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State/next-state environment lifecycle and TLC configuration accessors for `EvalCtx`.
//!
//! Extracted from `core.rs` as part of #2764 / #1643. Contains:
//! - State env binding and restoration (array-backed fast paths)
//! - RAII guards for state/next-state env (`guards`)
//! - State snapshot utilities
//! - TLC configuration accessors (`config`)
//! - Variable index access
//! - SharedCtx field accessors (`config`)

mod config;
mod guards;

use super::{invalidate_state_identity_tracking_with_ctx, EvalCtx, StateEnvRef, Value};
use std::sync::Arc;

impl EvalCtx {
    // ---- State Env Accessors ----

    /// Check if state_env is set (array-based fast path is active)
    #[inline]
    pub fn has_state_env(&self) -> bool {
        self.state_env.is_some()
    }

    /// Look up the current value of a state variable from either state_env or env.
    ///
    /// When state_env is set (array-based fast path), looks up via VarIndex.
    /// Falls back to env HashMap lookup.
    /// Returns None if the variable is not found in either.
    pub fn lookup_state_var(&self, name: &str) -> Option<Value> {
        if let Some(state_env) = self.state_env {
            if let Some(idx) = self.shared.var_registry.get(name) {
                debug_assert!(idx.as_usize() < state_env.env_len());
                // SAFETY: `idx` comes from this context's VarRegistry and is bounded above.
                return Some(unsafe { state_env.get_value(idx.as_usize()) });
            }
        }
        self.env.get(name).cloned()
    }

    /// Temporarily clear the bound array-backed state environment.
    ///
    /// This is required when evaluating expressions by rebinding variables into `env`
    /// (e.g., property checking over reconstructed `State`s), because `Expr::StateVar`
    /// prefers `state_env` over `env` when `state_env` is present.
    #[inline]
    pub fn take_state_env(&mut self) -> Option<StateEnvRef> {
        invalidate_state_identity_tracking_with_ctx(self);
        self.stable_mut().state_env.take()
    }

    /// Temporarily clear the bound array-backed next-state environment.
    #[inline]
    pub fn take_next_state_env(&mut self) -> Option<StateEnvRef> {
        invalidate_state_identity_tracking_with_ctx(self);
        self.stable_mut().next_state_env.take()
    }

    /// Snapshot the current state as variable-value pairs for enumeration helpers
    /// (e.g. `ENABLED`).
    ///
    /// Returns raw pairs instead of `State` to avoid coupling eval to the checker's
    /// state representation (#1269). The caller (enumerate::eval_enabled) builds a
    /// `State` on its side of the crate boundary.
    ///
    /// When `state_env` is active, the current state's variable values live in an array
    /// and are *not* present in `env`; in that case we read from `state_env`.
    pub fn snapshot_state_pairs(&self, vars: &[Arc<str>]) -> Vec<(Arc<str>, Value)> {
        if let Some(state_env) = self.state_env {
            let mut pairs = Vec::with_capacity(vars.len());
            for name in vars {
                if let Some(idx) = self.var_registry().get(name.as_ref()) {
                    debug_assert!(idx.as_usize() < state_env.env_len());
                    // SAFETY: `idx` originates from this model's VarRegistry, which
                    // defines the layout for the bound `state_env` array.
                    let value = unsafe { state_env.get_value(idx.as_usize()) };
                    pairs.push((Arc::clone(name), value));
                } else if let Some(value) = self.env.get(name.as_ref()) {
                    pairs.push((Arc::clone(name), value.clone()));
                }
            }
            return pairs;
        }

        // Part of #4112: FxHashSet for faster hashing on &str keys.
        let var_set: rustc_hash::FxHashSet<&str> =
            vars.iter().map(std::convert::AsRef::as_ref).collect();
        self.env
            .iter()
            .filter(|(k, _)| var_set.contains(k.as_ref()))
            .map(|(k, v)| (Arc::clone(k), v.clone()))
            .collect()
    }

    // ---- State Env Binding / Restoration ----

    /// Bind state variables from an ArrayState for O(1) access during evaluation.
    ///
    /// This sets `state_env` to point at the provided values slice, enabling fast
    /// state variable lookups via `VarIndex` instead of HashMap-based lookups.
    ///
    /// Returns the previous `state_env` so callers can restore it (supports nesting).
    #[inline]
    pub fn bind_state_array(&mut self, values: &[Value]) -> Option<StateEnvRef> {
        invalidate_state_identity_tracking_with_ctx(self);
        self.stable_mut()
            .state_env
            .replace(StateEnvRef::from_slice(values))
    }

    /// Bind state variables from a pre-constructed `StateEnvRef`.
    ///
    /// This is the storage-agnostic version of `bind_state_array`. Callers construct
    /// the appropriate `StateEnvRef` variant (`Compact` for `[CompactValue]`,
    /// `Legacy` for `[Value]`) and pass it directly.
    ///
    /// Returns the previous `state_env` so callers can restore it (supports nesting).
    #[inline]
    pub fn bind_state_env(&mut self, env_ref: StateEnvRef) -> Option<StateEnvRef> {
        invalidate_state_identity_tracking_with_ctx(self);
        self.stable_mut().state_env.replace(env_ref)
    }

    /// Restore a previous `state_env` returned by `bind_state_array()`.
    #[inline]
    pub fn restore_state_env(&mut self, prev: Option<StateEnvRef>) {
        invalidate_state_identity_tracking_with_ctx(self);
        self.stable_mut().state_env = prev;
    }

    /// Bind next-state variables from a pre-constructed `StateEnvRef`.
    ///
    /// Storage-agnostic version of `bind_next_state_array`.
    #[inline]
    pub fn bind_next_state_env(&mut self, env_ref: StateEnvRef) -> Option<StateEnvRef> {
        invalidate_state_identity_tracking_with_ctx(self);
        self.stable_mut().next_state_env.replace(env_ref)
    }

    /// Bind next-state variables from an ArrayState for O(1) primed variable access.
    ///
    /// This sets `next_state_env` to point at the provided values slice, enabling fast
    /// primed variable lookups via `VarIndex` instead of HashMap-based lookups.
    ///
    /// Returns the previous `next_state_env` so callers can restore it (supports nesting).
    #[inline]
    pub fn bind_next_state_array(&mut self, values: &[Value]) -> Option<StateEnvRef> {
        invalidate_state_identity_tracking_with_ctx(self);
        self.stable_mut()
            .next_state_env
            .replace(StateEnvRef::from_slice(values))
    }

    /// Restore a previous `next_state_env` returned by `bind_next_state_array()`.
    #[inline]
    pub fn restore_next_state_env(&mut self, prev: Option<StateEnvRef>) {
        invalidate_state_identity_tracking_with_ctx(self);
        self.stable_mut().next_state_env = prev;
    }

    // ---- State Snapshots ----

    /// Snapshot the currently bound state arrays (if any) into owned, shareable storage.
    ///
    /// This is used when creating closures like `LazyFuncValue` so later evaluation can
    /// restore the correct `state_env` / `next_state_env` regardless of the caller context.
    ///
    /// Issue #418: When state_env is not set (e.g., trace reconstruction uses HashMap-based
    /// binding via bind_mut), fall back to capturing state variables from the env HashMap.
    /// This ensures SetPredValue captures state at definition time even when not using
    /// array-based state binding.
    #[allow(clippy::type_complexity)]
    pub(crate) fn snapshot_state_envs(&self) -> (Option<Arc<[Value]>>, Option<Arc<[Value]>>) {
        fn snapshot(env: Option<StateEnvRef>) -> Option<Arc<[Value]>> {
            env.map(|env_ref| {
                let len = env_ref.env_len();
                let mut values = Vec::with_capacity(len);
                for idx in 0..len {
                    debug_assert!(idx < len);
                    // SAFETY: loop bounds guarantee `idx < len`, and env_ref
                    // points to a valid values slice for this call.
                    values.push(unsafe { env_ref.get_value(idx) });
                }
                Arc::from(values.into_boxed_slice())
            })
        }

        // Try array-based snapshot first (fast path)
        let state_snap = snapshot(self.state_env);
        let next_state_snap = snapshot(self.next_state_env);

        // Issue #418: Fall back to HashMap-based capture if state_env is not set
        // This handles trace reconstruction and other paths that use bind_mut instead of
        // bind_state_array
        let state_snap = if state_snap.is_none() && !self.shared.var_registry.is_empty() {
            let registry = &self.shared.var_registry;
            let mut values = Vec::with_capacity(registry.len());
            let mut found_all = true;
            for (_, name) in registry.iter() {
                if let Some(v) = self.env.get(name.as_ref()) {
                    values.push(v.clone());
                } else {
                    found_all = false;
                    break;
                }
            }
            if found_all && !values.is_empty() {
                Some(Arc::from(values.into_boxed_slice()))
            } else {
                None
            }
        } else {
            state_snap
        };

        (state_snap, next_state_snap)
    }

    /// Check if next_state_env is currently set (for fast path decisions).
    ///
    /// Used by Fallback evaluation to skip HashMap construction when array-based
    /// next-state lookups are already available.
    #[inline]
    pub fn has_next_state_env(&self) -> bool {
        self.next_state_env.is_some()
    }
}
