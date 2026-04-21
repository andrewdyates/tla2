// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! RAII guards for state/next-state environment binding and restoration.
//!
//! Part of #2764 / #1643. Extracted from `eval_ctx_state.rs` as part of #3463.

use super::super::{
    EvalCtx, NextStateEnvGuard, SkipPrimeValidationGuard, StateEnvGuard, StateEnvRef,
    StateIdentityGuard,
};

impl EvalCtx {
    // ---- RAII Guards ----

    /// Bind next-state variables from an ArrayState, returning an RAII guard.
    ///
    /// The guard restores `next_state_env` to its previous value on drop,
    /// making this panic-safe and early-return-safe.
    ///
    /// # Example
    ///
    /// ```text
    /// let _guard = ctx.bind_next_state_array_guard(values);
    /// let result = eval(ctx, expr); // guard restores on drop
    /// ```
    #[inline]
    pub fn bind_next_state_array_guard(&mut self, values: &[Value]) -> NextStateEnvGuard {
        let hoist_guard = crate::cache::bump_hoist_state_generation_ctx(self);
        let state_identity_guard = StateIdentityGuard::new_with_ctx(self);
        let prev = self
            .stable_mut()
            .next_state_env
            .replace(StateEnvRef::from_slice(values));
        NextStateEnvGuard {
            ctx: self as *mut EvalCtx,
            prev,
            _hoist_guard: hoist_guard,
            _state_identity_guard: state_identity_guard,
        }
    }

    /// Clear next-state variables, returning an RAII guard that restores
    /// the previous value on drop.
    #[inline]
    pub fn take_next_state_env_guard(&mut self) -> NextStateEnvGuard {
        let hoist_guard = crate::cache::bump_hoist_state_generation_ctx(self);
        let state_identity_guard = StateIdentityGuard::new_with_ctx(self);
        let prev = self.stable_mut().next_state_env.take();
        NextStateEnvGuard {
            ctx: self as *mut EvalCtx,
            prev,
            _hoist_guard: hoist_guard,
            _state_identity_guard: state_identity_guard,
        }
    }

    /// Bind state variables from an ArrayState, returning an RAII guard.
    ///
    /// The guard restores `state_env` to its previous value on drop.
    #[inline]
    pub fn bind_state_array_guard(&mut self, values: &[Value]) -> StateEnvGuard {
        let hoist_guard = crate::cache::bump_hoist_state_generation_ctx(self);
        let state_identity_guard = StateIdentityGuard::new_with_ctx(self);
        let prev = self
            .stable_mut()
            .state_env
            .replace(StateEnvRef::from_slice(values));
        StateEnvGuard {
            ctx: self as *mut EvalCtx,
            prev,
            _hoist_guard: hoist_guard,
            _state_identity_guard: state_identity_guard,
        }
    }

    /// Bind state variables from a pre-constructed `StateEnvRef`, returning an RAII guard.
    ///
    /// Storage-agnostic version of `bind_state_array_guard`. Callers construct the
    /// appropriate `StateEnvRef` variant and pass it directly.
    #[inline]
    pub fn bind_state_env_guard(&mut self, env_ref: StateEnvRef) -> StateEnvGuard {
        let hoist_guard = crate::cache::bump_hoist_state_generation_ctx(self);
        let state_identity_guard = StateIdentityGuard::new_with_ctx(self);
        let prev = self.stable_mut().state_env.replace(env_ref);
        StateEnvGuard {
            ctx: self as *mut EvalCtx,
            prev,
            _hoist_guard: hoist_guard,
            _state_identity_guard: state_identity_guard,
        }
    }

    /// Bind next-state variables from a pre-constructed `StateEnvRef`, returning an RAII guard.
    ///
    /// Storage-agnostic version of `bind_next_state_array_guard`.
    #[inline]
    pub fn bind_next_state_env_guard(&mut self, env_ref: StateEnvRef) -> NextStateEnvGuard {
        let hoist_guard = crate::cache::bump_hoist_state_generation_ctx(self);
        let state_identity_guard = StateIdentityGuard::new_with_ctx(self);
        let prev = self.stable_mut().next_state_env.replace(env_ref);
        NextStateEnvGuard {
            ctx: self as *mut EvalCtx,
            prev,
            _hoist_guard: hoist_guard,
            _state_identity_guard: state_identity_guard,
        }
    }

    /// Clear state variables, returning an RAII guard that restores
    /// the previous value on drop.
    #[inline]
    pub fn take_state_env_guard(&mut self) -> StateEnvGuard {
        let hoist_guard = crate::cache::bump_hoist_state_generation_ctx(self);
        let state_identity_guard = StateIdentityGuard::new_with_ctx(self);
        let prev = self.stable_mut().state_env.take();
        StateEnvGuard {
            ctx: self as *mut EvalCtx,
            prev,
            _hoist_guard: hoist_guard,
            _state_identity_guard: state_identity_guard,
        }
    }

    /// Set `skip_prime_validation` conditionally and return an RAII guard that
    /// restores the original value on drop.
    ///
    /// If `should_skip` is true, sets the flag to `true`; otherwise leaves it
    /// unchanged. Either way, the guard restores the original value on drop.
    ///
    /// # Example
    ///
    /// ```text
    /// let guard = ctx.skip_prime_guard(!def.guards_depend_on_prime && !def.contains_prime);
    /// let result = enumerate_unified_inner(ctx, &def.body, p, s);
    /// drop(guard); // or let it drop naturally at scope end
    /// ```
    #[inline]
    pub fn skip_prime_guard(&mut self, should_skip: bool) -> SkipPrimeValidationGuard {
        let prev = self.stable.skip_prime_validation;
        if should_skip {
            self.stable_mut().skip_prime_validation = true;
        }
        SkipPrimeValidationGuard {
            ctx: self as *mut EvalCtx,
            prev,
        }
    }
}

use crate::value::Value;
