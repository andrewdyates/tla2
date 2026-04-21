// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! ENABLED constraint propagation decision procedure.
//!
//! Replaces the enumerate_unified-based ENABLED evaluation with a dedicated
//! constraint propagation approach matching TLC's `enabled()` method.
//!
//! TLC treats ENABLED as a **witness search** with incremental variable binding
//! and short-circuit backtracking. This module implements the same approach:
//!
//! - `WitnessState`: functional linked-list for primed variable bindings (O(1) bind)
//! - `dispatch_enabled`: expression traversal with constraint propagation
//!
//! TLC references:
//! - `Tool.java:2577-3600` (enabled evaluation)
//! - `TLCStateFun.java` (functional successor state)
//! - `ActionItemList.java` (continuation stack)
//!
//! Part of #3004: ENABLED constraint propagation decision procedure.

mod conjunction;
mod dispatch;
mod module_ref;
mod quantifiers;
mod set_enumerate;
mod witness_state;

use crate::enumerate::is_disabled_action_error;
use crate::eval::{enter_enabled_scope_with_ctx, EvalCtx};
use std::sync::Arc;
use tla_core::ast::Expr;
use tla_core::{Spanned, VarRegistry};
use tla_value::error::EvalError;
use witness_state::WitnessState;

/// ENABLED evaluation via constraint propagation.
///
/// Determines whether the action expression has at least one satisfying
/// assignment of primed variables, without building ArrayState, computing
/// fingerprints, or running the full enumeration engine.
///
/// # Arguments
/// * `ctx` - Evaluation context with current state bound
/// * `action` - The action expression inside ENABLED
/// * `vars` - Variable names for the spec
///
/// # Returns
/// `Ok(true)` if the action is enabled, `Ok(false)` otherwise.
///
/// This function matches the signature of `EnabledHook` so it can be installed
/// via `set_enabled_hook()`.
pub(crate) fn eval_enabled_cp(
    ctx: &mut EvalCtx,
    action: &Spanned<Expr>,
    vars: &[Arc<str>],
) -> Result<bool, EvalError> {
    // 1. Snapshot current state bindings.
    let current_state_pairs = ctx.snapshot_state_pairs(vars);

    // 2. Normalize eval context: clear state_env/next_state_env, rebind into env.
    //    Needed because some eval paths read from ctx.env (Part of #261).
    let _state_guard = ctx.take_state_env_guard();
    let _next_guard = ctx.take_next_state_env_guard();
    let _scope_guard = ctx.scope_guard();
    for (name, value) in &current_state_pairs {
        ctx.bind_mut(Arc::clone(name), value.clone());
    }

    // 3. Enter ENABLED scope for cache isolation.
    //    This clears PerState caches (SUBST_CACHE, OP_RESULT_CACHE, etc.)
    //    to prevent contamination from/to the outer scope.
    // Part of #3962: Use ctx-aware variant to sync in_enabled_scope shadow.
    let _enabled_guard = enter_enabled_scope_with_ctx(ctx);

    // 4. Get VarRegistry for primed variable index resolution.
    let registry = if !ctx.var_registry().is_empty() {
        ctx.var_registry().clone()
    } else {
        VarRegistry::from_names(vars.iter().cloned())
    };

    // 5. Run constraint propagation.
    //    NO enumerate_unified, NO ArrayState, NO fingerprint computation.
    let witness = WitnessState::new(registry.len());
    let result = dispatch::dispatch_enabled(ctx, action, &registry, witness);

    match result {
        Ok(Some(_witness)) => Ok(true),
        Ok(None) => Ok(false),
        Err(e) if is_disabled_action_error(&e) => Ok(false),
        Err(e) => Err(e),
    }
}
