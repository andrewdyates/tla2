// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! INSTANCE substitution handling for identifier evaluation.
//!
//! When evaluating inside an INSTANCE scope, identifiers may be mapped to
//! expressions via substitution (e.g., `INSTANCE M WITH x <- expr`). The
//! substitution RHS is evaluated in the OUTER module's context.

#[cfg(debug_assertions)]
use crate::debug_instance_subst;
use crate::{
    current_state_lookup_mode, eval_with_dep_tracking, is_dep_tracking_active, is_subst_guarded,
    propagate_cached_deps, subst_cache_key, EvalCtx, EvalResult, StateLookupMode, SubstCacheEntry,
    SubstGuardEntry, Value, SUBST_STATE,
};
use tla_core::name_intern::intern_name;

/// Check for explicit INSTANCE substitutions during identifier evaluation.
///
/// When evaluating inside an INSTANCE scope, identifiers may be mapped to expressions
/// via substitution (e.g., `INSTANCE M WITH x <- expr`). The substitution RHS is
/// evaluated in the OUTER module's context (without instance substitutions or local_ops).
///
/// Results are cached in `SUBST_CACHE` keyed by `(is_next_state, name)`.
#[inline(never)]
pub(crate) fn eval_ident_explicit_instance_substitution(
    ctx: &EvalCtx,
    resolved_name: &str,
) -> EvalResult<Option<Value>> {
    let Some(subs) = ctx.instance_substitutions() else {
        return Ok(None);
    };
    // Fix #2364: Check the recursion guard before matching. If this name is currently
    // being evaluated (guard active), treat it as a raw variable, not a substitution target.
    let name_id = intern_name(resolved_name);
    if is_subst_guarded(name_id) {
        return Ok(None);
    }
    let Some(sub) = subs.iter().find(|s| s.from.node == resolved_name) else {
        return Ok(None);
    };

    // BUG FIX #295: Use StateLookupMode instead of next_state.is_some() for cache key.
    // When evaluating in UNCHANGED's next context, next_state may be None (fast path
    // uses state_env instead), but StateLookupMode correctly reflects next-state mode.
    let is_next_state = current_state_lookup_mode(ctx) == StateLookupMode::Next;
    let cache_key = subst_cache_key(ctx, is_next_state, name_id);
    if let Some(cached) = SUBST_STATE.with(|s| s.borrow().cache.get(&cache_key).cloned()) {
        debug_eprintln!(
            debug_instance_subst(),
            "[INSTANCE_SUBST] cache hit: name={}, is_next_state={}, cached={:?}",
            resolved_name,
            is_next_state,
            cached.value
        );
        // Fix #2364: Propagate stored deps on cache hit so that enclosing
        // zero-arg operator dep tracking sees the state reads from the
        // substitution RHS evaluation. Without this, operators like `tpos`
        // appear to have no deps and are incorrectly cached as constant.
        if is_dep_tracking_active(ctx) {
            propagate_cached_deps(ctx, &cached.deps);
        }
        return Ok(Some(cached.value));
    }

    // Fix #2364: For chained refs, use a recursion guard instead of creating a filtered
    // Arc<Vec<Substitution>> copy. See eval_statevar.rs for full rationale.
    let _guard = if ctx.chained_ref_eval {
        Some(SubstGuardEntry::new(name_id))
    } else {
        None
    };
    let outer_ctx = if ctx.chained_ref_eval {
        // Chained ref: evaluate in original context. The recursion guard prevents
        // the current name from matching in nested substitution lookups.
        ctx.clone()
    } else {
        // Non-chained: clear INSTANCE resolution metadata per #151. Named instance
        // operators (like Peterson's pc_translation) must not shadow outer module
        // operators (like LockHS's pc_translation) in substitution expressions.
        //
        // Part of #3056 Phase 5: use without_instance_resolution_scope() instead of
        // with_outer_resolution_scope(). This function is reachable when
        // eager_subst_bindings is None (eval_ident.rs line 321), which occurs via:
        //   (a) with_instance_scope() — binding chain is empty, both methods equivalent.
        //   (b) Expr::SubstIn (eval_dispatch.rs) — binding chain is non-empty with
        //       outer local bindings. without_instance_resolution_scope() preserves
        //       the outer chain (correct); with_outer_resolution_scope() would destroy it.
        // Using without_instance_resolution_scope() is correct for both paths.
        ctx.without_instance_resolution_scope()
    };
    debug_eprintln!(
        debug_instance_subst(),
        "[INSTANCE_SUBST] evaluating: name={}, is_next_state={}, state_env={}, next_state={}, chained={}",
        resolved_name,
        is_next_state,
        outer_ctx.state_env.is_some(),
        outer_ctx.next_state.is_some(),
        ctx.chained_ref_eval
    );
    // Fix #2364: Capture deps during substitution RHS evaluation so they can
    // be stored in SUBST_CACHE and propagated on cache hit.
    let (value, deps) = eval_with_dep_tracking(&outer_ctx, &sub.to)?;
    debug_eprintln!(
        debug_instance_subst(),
        "[INSTANCE_SUBST] result: name={}, is_next_state={}, value={:?}",
        resolved_name,
        is_next_state,
        value
    );
    // Part of #3109 (revised): Allow SUBST_CACHE insertion during ENABLED scope.
    // SUBST_CACHE entries are module-structural (INSTANCE chain substitutions)
    // and valid within a single ENABLED scope. The cache is cleared at ENABLED
    // scope boundaries by clear_state_boundary_core_impl(), so entries cannot
    // contaminate cross-scope evaluation. Allowing insertion enables 10x reuse
    // across WF constraints for specs like Huang (10 WF, 81K states).
    // Original guard removed: dep tracking unreliability for SUBST_CACHE entries
    // doesn't cause correctness issues because the cache is cleared at scope
    // boundaries — stale deps never survive to a different evaluation context.
    SUBST_STATE.with(|s| {
        s.borrow_mut().cache.insert(
            cache_key,
            SubstCacheEntry {
                value: value.clone(),
                deps,
            },
        );
    });
    Ok(Some(value))
}
