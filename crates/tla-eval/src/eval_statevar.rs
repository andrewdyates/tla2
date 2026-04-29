// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#[cfg(debug_assertions)]
use super::debug_instance_subst;
use super::{
    current_state_lookup_mode, eval, eval_with_dep_tracking, is_dep_tracking_active,
    is_subst_guarded, propagate_cached_deps, subst_cache_key, EvalCtx, EvalResult, Expr, Span,
    Spanned, StateLookupMode, SubstCacheEntry, SubstGuardEntry, Value, SUBST_STATE,
};
use tla_core::name_intern::intern_name;
// StateVar INSTANCE substitution helpers for eval_expr's Expr::StateVar arm.
// Extracted from core.rs as part of #1219 decomposition.

#[inline(never)]
pub(super) fn eval_statevar_explicit_instance_substitution(
    ctx: &EvalCtx,
    name: &str,
) -> EvalResult<Option<Value>> {
    let Some(subs) = ctx.instance_substitutions() else {
        return Ok(None);
    };
    // Fix #2364: Check the recursion guard before matching. If this name is currently
    // being evaluated (guard active), treat it as a raw variable, not a substitution target.
    // This replaces the previous Arc-filtering approach that broke cache key stability.
    let name_id = intern_name(name);
    if is_subst_guarded(name_id) {
        return Ok(None);
    }
    let Some(sub) = subs.iter().find(|s| s.from.node.as_str() == name) else {
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
            "[INSTANCE_SUBST:StateVar] cache hit: name={}, is_next_state={}, cached={:?}",
            name,
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
    // Arc<Vec<Substitution>> copy. The guard prevents infinite self-referential loops
    // (e.g., `inbox <- expr_that_reads_inbox`) while keeping the parent Arc pointer
    // stable, enabling SUBST_CACHE and ZERO_ARG_OP_CACHE hits across sibling sub
    // evaluations. The previous filter approach created N new Arcs for N subs,
    // causing O(N!) cascading re-evaluations due to cache key instability.
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
        // Part of #3056 Phase 5: use without_instance_resolution_scope() instead of
        // with_outer_resolution_scope(). This function is reachable when
        // eager_subst_bindings is None, which occurs via with_instance_scope()
        // (empty chain) or Expr::SubstIn (non-empty chain with outer bindings).
        // without_instance_resolution_scope() preserves the chain (correct for both).
        ctx.without_instance_resolution_scope()
    };
    debug_eprintln!(
        debug_instance_subst(),
        "[INSTANCE_SUBST:StateVar] evaluating: name={}, is_next_state={}, state_env={}, next_state={}, chained={}",
        name,
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
        "[INSTANCE_SUBST:StateVar] result: name={}, is_next_state={}, value={:?}",
        name,
        is_next_state,
        value
    );
    // Part of #3109 (revised): Allow SUBST_CACHE insertion during ENABLED scope.
    // See eval_ident.rs for rationale — SUBST_CACHE entries are module-structural
    // and cleared at scope boundaries. Allowing insertion enables WF constraint
    // reuse within a single ENABLED evaluation batch.
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

#[inline(never)]
pub(super) fn eval_statevar_implicit_instance_substitution(
    ctx: &EvalCtx,
    name: &str,
    span: Option<&Span>,
) -> EvalResult<Option<Value>> {
    let Some(subs) = ctx.instance_substitutions() else {
        return Ok(None);
    };
    if !subs.iter().any(|sub| sub.from.node == name) {
        return Ok(None);
    }

    // Fast path: only consider implicit substitution when the *outer* module defines an operator
    // with this name. If the outer module defines a state variable, the normal StateVar lookup is
    // already correct and avoids expensive recursive eval() calls.
    if !ctx.shared.ops.contains_key(name) {
        return Ok(None);
    }

    // Part of #3056 Phase 5: rewind to outer resolution scope. Cannot use
    // without_instance_resolution_scope() because the chain contains instance
    // substitution entries that would shadow the outer-scope operator we're about
    // to look up. Example: if INSTANCE M WITH x <- y, and the outer module has an
    // operator named `x`, the instance binding for `x` would be found first,
    // returning `y` instead of the operator body.
    let outer_ctx = ctx.with_outer_resolution_scope();

    debug_eprintln!(
        debug_instance_subst(),
        "[INSTANCE_SUBST:StateVar:check] name={}, has_op={}, has_var={}",
        name,
        outer_ctx.get_op(name).is_some(),
        outer_ctx.var_registry().get(name).is_some()
    );

    // Check if outer context has an operator with this name
    if outer_ctx.get_op(name).is_some() {
        // NOTE: Do NOT cache implicit substitutions! See comment in Ident handler (#295).
        debug_block!(debug_instance_subst(), {
            let is_next_state = current_state_lookup_mode(ctx) == StateLookupMode::Next;
            eprintln!(
                "[INSTANCE_SUBST:StateVar:Implicit] evaluating: name={name}, is_next_state={is_next_state}"
            );
        });

        // Create implicit substitution: evaluate Ident(name) in outer context
        // Part of #2993: Pre-intern the name to avoid runtime lookup_name_id().
        let implicit_expr = Spanned {
            node: Expr::Ident(name.to_string(), intern_name(name)),
            span: span.copied().unwrap_or_default(),
        };
        let value = eval(&outer_ctx, &implicit_expr)?;

        debug_block!(debug_instance_subst(), {
            let is_next_state = current_state_lookup_mode(ctx) == StateLookupMode::Next;
            eprintln!(
                "[INSTANCE_SUBST:StateVar:Implicit] result: name={name}, is_next_state={is_next_state}, value={value:?}"
            );
        });

        return Ok(Some(value));
    }

    Ok(None)
}
