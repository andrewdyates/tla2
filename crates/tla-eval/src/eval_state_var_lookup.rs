// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! State variable resolution: lazy binding evaluation, O(1) slot lookup,
//! and overlay-based resolution cascade.
//!
//! Part of #3214: Split from eval_expr_helpers.rs for focused profiling
//! of the BFS hot path (eval_state_var is called for every state variable
//! read during model checking).

use super::core::EvalCtx;
use super::{
    current_state_lookup_mode, eval, eval_statevar_explicit_instance_substitution,
    eval_statevar_implicit_instance_substitution, is_dep_tracking_active, mark_instance_lazy_read,
    propagate_cached_deps, record_local_read, record_next_read, record_state_read, EvalError,
    EvalResult, StateLookupMode,
};
use crate::value::Value;
use tla_core::name_intern::{intern_name, lookup_name_id, NameId};
use tla_core::Span;

// Part of #4114: Cache debug env var with OnceLock instead of calling
// std::env::var on every lazy binding force.
debug_flag!(debug_3147_svl, "TLA2_DEBUG_3147");

/// Handle a lazy binding cache hit: propagate deps and return.
///
/// Part of #3056: Consolidates the triplicated cache-hit dep-propagation
/// pattern from eval_ident (fast + slow paths) and eval_state_var_lookup (StateVar).
pub(super) fn lazy_binding_cache_hit_deps(
    ctx: &EvalCtx,
    lazy: &crate::binding_chain::LazyBinding,
    source: crate::binding_chain::BindingSourceRef<'_>,
    cached: &Value,
    name_id: NameId,
    mode: super::StateLookupMode,
) {
    match source {
        crate::binding_chain::BindingSourceRef::Instance(_) => {
            if is_dep_tracking_active(ctx) {
                if let Some(forced) = lazy.get_forced_deps(mode) {
                    propagate_cached_deps(ctx, forced);
                    // Fix #3447: Only taint if the forced deps are non-constant.
                    // Constant INSTANCE bindings propagate no state dependency.
                    if forced.instance_lazy_read {
                        mark_instance_lazy_read(ctx);
                    }
                } else {
                    // No forced deps available - conservative taint.
                    mark_instance_lazy_read(ctx);
                }
            }
        }
        crate::binding_chain::BindingSourceRef::Local(stack_idx)
        | crate::binding_chain::BindingSourceRef::Liveness(stack_idx) => {
            record_local_read(ctx, stack_idx, name_id, cached);
        }
        crate::binding_chain::BindingSourceRef::None => {}
    }
}

/// Force a lazy binding: evaluate the deferred expression and cache the result.
///
/// Handles context construction (Instance source clears current INSTANCE
/// resolution metadata while keeping the definition-site binding chain), dep
/// tracking, caching, and dep propagation.
///
/// Part of #3056: Consolidates the triplicated forcing pattern from eval_ident
/// (fast + slow paths) and eval_state_var_lookup (StateVar).
pub(super) fn force_lazy_binding(
    ctx: &EvalCtx,
    lazy: &crate::binding_chain::LazyBinding,
    source: crate::binding_chain::BindingSourceRef<'_>,
    name_id: NameId,
    mode: super::StateLookupMode,
) -> EvalResult<Value> {
    let is_instance = matches!(source, crate::binding_chain::BindingSourceRef::Instance(_));
    let mut eval_ctx = if is_instance {
        // Instance source: evaluate substitution RHS against the definition-site
        // binding chain while clearing current INSTANCE resolution metadata.
        // Part of #3056 Phase B: Restore pre-scope local_ops instead of clearing
        // entirely. This matches TLC's evalImplSubstInKind which evaluates sub RHS
        // with `c` (the context at SubstIn entry, before inner module ops are merged).
        // - Clearing ALL local_ops (old behavior) breaks nested instances: the
        //   enclosing module's operators become invisible to substitution RHS.
        // - Keeping POST-merge local_ops breaks shadowing: inner module operators
        //   can shadow the outer module's operator that the substitution targets.
        // - Restoring PRE-merge local_ops is correct: substitution RHS sees the
        //   enclosing module's operators without inner module shadowing.
        let mut c = ctx.clone();
        let s = c.stable_mut();
        s.instance_substitutions = None;
        s.scope_ids.instance_substitutions = 0;
        s.eager_subst_bindings = None;
        s.skip_prime_validation = false;
        // Restore pre-scope local_ops (before inner module merge).
        // Falls back to clearing local_ops if no pre-scope snapshot exists
        // (backward compatibility with non-module-scope SubstIn evaluation).
        s.local_ops = s.pre_scope_local_ops.take();
        // Part of #3099: Invalidate scope_ids.local_ops since we restored pre-scope
        // local_ops, diverging from the id computed for the merged module scope.
        s.scope_ids.local_ops = crate::cache::scope_ids::INVALIDATED;
        c
    } else {
        ctx.clone()
    };
    eval_ctx.bindings = lazy.enclosing.clone();

    // Capture deps for INSTANCE lazy bindings on first force even when the first
    // access is outside an enclosing dep-tracking frame. Later zero-arg operator
    // evaluations may only see the cached lazy binding; if we fail to retain the
    // substitution RHS deps here, those operators can be misclassified as constant.
    let parent_dep_tracking_active = is_instance && is_dep_tracking_active(ctx);
    let guard = if is_instance {
        let base_stack_len = if parent_dep_tracking_active {
            let stack = ctx.runtime_state.op_dep_stack.borrow();
            stack.last().map_or(0, |f| f.base_stack_len)
        } else {
            ctx.binding_depth
        };
        Some(crate::cache::dep_tracking::OpDepGuard::from_ctx(
            ctx,
            base_stack_len,
        ))
    } else {
        None
    };

    let value = eval(&eval_ctx, lazy.expr())?;

    // #3147 debug: trace INSTANCE lazy binding forcing
    if is_instance && debug_3147_svl() {
        let name_str = tla_core::name_intern::resolve_name_id(name_id);
        eprintln!(
            "[DEBUG_3147] force_lazy_binding: name={}, mode={:?}, state_env_id={}, value={:?}, expr={:?}",
            name_str,
            mode,
            eval_ctx.state_env.map_or(0, |s| s.identity()),
            &value,
            lazy.expr().node,
        );
    }

    // Part of #3465: Store in thread-local cache for within-state reuse.
    // The OnceLock in LazyBinding persists across states, but this cache is
    // cleared at every state/scope boundary.
    if is_instance {
        let lazy_ptr = lazy as *const crate::binding_chain::LazyBinding as usize;
        crate::cache::small_caches::instance_lazy_cache_store(lazy_ptr, mode as u8, value.clone());
    } else {
        lazy.set_cached(value.clone(), mode);
    }

    if let Some(guard) = guard {
        if let Some(mut deps) = guard.try_take_deps() {
            // Fix #3447: Taint the stored deps so future cache hits propagate
            // the INSTANCE lazy read marker to enclosing dep-tracking frames.
            // Perf fix: Only taint when the forced deps are non-constant.
            // Constant INSTANCE bindings (empty state/next/local deps) don't need
            // the taint - their values are state-independent and can be persistently
            // cached. This prevents constant operators accessed through INSTANCE
            // (e.g., Block/SignedBlock in MCNano N == INSTANCE Nano) from being
            // evicted on every state boundary.
            let is_constant_binding = deps.state.is_empty()
                && deps.next.is_empty()
                && deps.local.is_empty()
                && !deps.inconsistent
                && deps.tlc_level.is_none();
            if !is_constant_binding {
                deps.instance_lazy_read = true;
            }
            lazy.set_forced_deps(deps.clone(), mode);
            if parent_dep_tracking_active {
                propagate_cached_deps(ctx, &deps);
                if !is_constant_binding {
                    mark_instance_lazy_read(ctx);
                }
            }
        }
    } else if let crate::binding_chain::BindingSourceRef::Local(stack_idx)
    | crate::binding_chain::BindingSourceRef::Liveness(stack_idx) = source
    {
        record_local_read(ctx, stack_idx, name_id, &value);
    }

    Ok(value)
}

/// Borrow a `StateVar` value directly from the state array when no overlays are active.
///
/// Part of #3168: shared fast path for the common BFS case where bindings are
/// empty and no INSTANCE or call-by-name substitutions are present. Both
/// `eval_state_var` and `try_borrow_materialized_state_var` use this to avoid
/// per-access overlay checks that TLC does not pay (TLC uses direct slot lookup
/// via `TLCStateMut.lookup` → `values[loc]`).
///
/// Returns `Some(&Value)` only when all overlays are empty AND `state_env` is
/// available. Returns `None` otherwise so the caller falls through to the full
/// overlay-checking path.
fn try_borrow_plain_state_var_slot(
    ctx: &EvalCtx,
    resolved_idx: crate::var_index::VarIndex,
) -> Option<Value> {
    if ctx.bindings.is_empty()
        && ctx.instance_substitutions().is_none()
        && ctx.eager_subst_bindings.is_none()
        && ctx.call_by_name_subs().is_none()
    {
        if let Some(state_env) = ctx.state_env {
            debug_assert!(resolved_idx.as_usize() < state_env.env_len());
            // SAFETY: `resolved_idx` is validated against the current VarRegistry
            // by `resolve_state_var_slot`.
            let v = unsafe { state_env.get_value(resolved_idx.as_usize()) };
            record_state_read(ctx, resolved_idx, &v);
            return Some(v);
        }
    }
    None
}

/// Borrow a `StateVar` value only when the winning lookup source is already materialized.
///
/// Part of #3168: this mirrors the ready-value branches of `eval_state_var` so
/// `eval_func_apply` can preserve borrows through `StateVar -> apply` without
/// changing the public `eval(...) -> Value` ownership boundary. Any path that
/// would force a lazy binding or evaluate a substitution returns `None` so the
/// caller can fall back to the existing owned path.
pub(crate) fn try_borrow_materialized_state_var(
    ctx: &EvalCtx,
    name: &str,
    idx: u16,
    name_id: NameId,
) -> Option<Value> {
    let resolved_idx = ctx.resolve_state_var_slot(name, idx, name_id);
    let lookup_name_id = if name_id != NameId::INVALID {
        name_id
    } else {
        lookup_name_id(name).unwrap_or_else(|| intern_name(name))
    };

    // Part of #3168: direct state-array fast path for the common BFS case.
    // When no binding/substitution overlays are active, skip straight to the
    // state array — matching TLC's direct slot lookup in TLCStateMut.lookup().
    if let Some(v) = try_borrow_plain_state_var_slot(ctx, resolved_idx) {
        return Some(v);
    }

    if let Some((bv, source)) = ctx.bindings.lookup(lookup_name_id) {
        if !matches!(source, crate::binding_chain::BindingSourceRef::Liveness(_)) {
            let mode = current_state_lookup_mode(ctx);
            if let Some(v) = bv.get_if_ready(mode, source) {
                if let Some(lazy) = bv.as_lazy() {
                    lazy_binding_cache_hit_deps(ctx, lazy, source, &v, lookup_name_id, mode);
                } else if let crate::binding_chain::BindingSourceRef::Instance(deps) = source {
                    if is_dep_tracking_active(ctx) {
                        propagate_cached_deps(ctx, deps);
                    }
                }
                return Some(v);
            }
            return None;
        }
    }

    if let Some(subs) = ctx.call_by_name_subs() {
        if subs.iter().any(|sub| sub.from.node.as_str() == name) {
            return None;
        }
    }

    if ctx.instance_substitutions().is_some() {
        let has_explicit_instance_target = ctx.eager_subst_bindings.as_ref().is_some_and(|subs| {
            subs.iter()
                .any(|(target_id, _value, _deps)| *target_id == lookup_name_id)
        }) || ctx
            .instance_substitutions()
            .is_some_and(|subs| subs.iter().any(|sub| sub.from.node.as_str() == name));
        if has_explicit_instance_target || ctx.shared.ops.contains_key(name) {
            return None;
        }
    }

    if let Some(state_env) = ctx.state_env {
        debug_assert!(resolved_idx.as_usize() < state_env.env_len());
        // SAFETY: `resolved_idx` is validated against the current VarRegistry above.
        let v = unsafe { state_env.get_value(resolved_idx.as_usize()) };
        record_state_read(ctx, resolved_idx, &v);
        return Some(v);
    }

    if let Some(v) = ctx.env.get(name) {
        record_state_read(ctx, resolved_idx, v);
        return Some(v.clone());
    }

    None
}

/// Evaluate a pre-resolved state variable with O(1) lookup.
/// Part of #188, #232: StateVar has pre-computed index AND NameId.
pub(super) fn eval_state_var(
    ctx: &EvalCtx,
    name: &str,
    idx: u16,
    name_id: NameId,
    span: Option<Span>,
) -> EvalResult<Value> {
    let resolved_idx = ctx.resolve_state_var_slot(name, idx, name_id);
    let lookup_name_id = if name_id != NameId::INVALID {
        name_id
    } else {
        lookup_name_id(name).unwrap_or_else(|| intern_name(name))
    };

    // Part of #3168: shared plain-case array fast path for the common BFS case.
    // Uses the same `try_borrow_plain_state_var_slot` helper as the borrowing
    // `try_borrow_materialized_state_var` path, ensuring one audited definition
    // for the "no overlays → direct state array" boundary.
    if let Some(v) = try_borrow_plain_state_var_slot(ctx, resolved_idx) {
        return Ok(v);
    }

    // 0) Distinguish liveness replay bindings from ordinary evaluator locals.
    //
    // Fix #3135: `StateVar` nodes encode a lexical choice that should survive
    // liveness replay. Liveness-installed bindings must shadow `Ident`, but must
    // not override an already-resolved `StateVar`. Ordinary evaluator locals and
    // INSTANCE substitutions keep their existing behavior.

    // 1.5) Part of #2364 Phase 3: BindingChain lookup for INSTANCE substitution bindings.
    //
    // Fix #3135: After #2955, the chain holds INSTANCE, Local, and Liveness
    // bindings. `StateVar` should ignore only the liveness-installed source class.
    if let Some((bv, source)) = ctx.bindings.lookup(lookup_name_id) {
        if !matches!(source, crate::binding_chain::BindingSourceRef::Liveness(_)) {
            let mode = current_state_lookup_mode(ctx);
            if let Some(v) = bv.get_if_ready(mode, source) {
                if let Some(lazy) = bv.as_lazy() {
                    lazy_binding_cache_hit_deps(ctx, lazy, source, &v, lookup_name_id, mode);
                    return Ok(v);
                }
                if let crate::binding_chain::BindingSourceRef::Instance(deps) = source {
                    if is_dep_tracking_active(ctx) {
                        propagate_cached_deps(ctx, deps);
                    }
                }
                return Ok(v);
            }
            if let crate::binding_chain::BindingSourceRef::Instance(_) = source {
                if let Some(lazy) = bv.as_lazy() {
                    let lazy_ptr = lazy as *const crate::binding_chain::LazyBinding as usize;
                    if let Some(cached) =
                        crate::cache::small_caches::instance_lazy_cache_get(lazy_ptr, mode as u8)
                    {
                        lazy_binding_cache_hit_deps(
                            ctx,
                            lazy,
                            source,
                            &cached,
                            lookup_name_id,
                            mode,
                        );
                        return Ok(cached);
                    }
                }
            }
            // Part of #3046: Lazy binding evaluation for StateVar nodes.
            // When INSTANCE...WITH substitutions are lazy-bound in the BindingChain,
            // and the AST node is StateVar (from resolve_state_vars_in_loaded_ops)
            // instead of Ident, the lazy binding must still be evaluated. Without this,
            // the code falls through to direct state-array access (step 4), bypassing
            // the substitution entirely — causing false positives for specs like
            // Peterson and EWD998ChanID that use INSTANCE...WITH property checking.
            if let Some(lazy) = bv.as_lazy() {
                return force_lazy_binding(ctx, lazy, source, lookup_name_id, mode);
            }
        }
    }

    // 2) Apply INSTANCE substitutions if present (must precede state/env lookup)
    //
    // Fix #2364: Eager value bypass — use pre-evaluated substitution bindings.
    // If the name matches, return the pre-computed value directly (bypassing SUBST_CACHE).
    // If the name is NOT in the set, skip SUBST_CACHE entirely.
    if let Some(ref eager_subs) = ctx.eager_subst_bindings {
        for (id, value, deps) in eager_subs.iter() {
            if *id == lookup_name_id {
                if is_dep_tracking_active(ctx) {
                    propagate_cached_deps(ctx, deps);
                }
                return Ok(value.clone());
            }
        }
        // Name not in substitution targets → skip SUBST_CACHE entirely.
    } else if let Some(value) = eval_statevar_explicit_instance_substitution(ctx, name)? {
        return Ok(value);
    }

    // 3) Apply call-by-name substitutions (operators with primed parameters)
    if let Some(subs) = ctx.call_by_name_subs() {
        if let Some(sub) = subs.iter().find(|s| s.from.node.as_str() == name) {
            let inner_ctx = ctx.without_call_by_name_subs();
            return eval(&inner_ctx, &sub.to);
        }
    }

    // 3.5) BUG FIX #295: Implicit substitution for INSTANCE without explicit WITH.
    if let Some(value) = eval_statevar_implicit_instance_substitution(ctx, name, span.as_ref())? {
        return Ok(value);
    }

    // 3.8) Part of #3365: Sparse next-state overlay from ENABLED WitnessState.
    // In Next mode, bound sparse slots override current-state values.
    if current_state_lookup_mode(ctx) == StateLookupMode::Next {
        if let Some(sparse_env) = ctx.sparse_next_state_env {
            // SAFETY: resolved_idx bounded by VarRegistry.
            let slot = unsafe { sparse_env.get_unchecked(resolved_idx.as_usize()) };
            if let Some(v) = slot {
                record_next_read(ctx, resolved_idx, v);
                return Ok(v.clone());
            }
            // None = unbound in witness, fall through to current state
        }
    }

    // 4) O(1) state_env access using pre-computed index
    if let Some(state_env) = ctx.state_env {
        debug_assert!(resolved_idx.as_usize() < state_env.env_len());
        // SAFETY: `resolved_idx` is validated against the current VarRegistry above.
        let v = unsafe { state_env.get_value(resolved_idx.as_usize()) };
        record_state_read(ctx, resolved_idx, &v);
        return Ok(v);
    }

    // 5) Fallback to env (for cases where state_env isn't set, e.g., property checking)
    // BUG FIX #295: Must record state read even when state vars are in env!
    if let Some(v) = ctx.env.get(name) {
        record_state_read(ctx, resolved_idx, v);
        return Ok(v.clone());
    }

    Err(EvalError::UndefinedVar {
        name: name.to_string(),
        span,
    })
}
