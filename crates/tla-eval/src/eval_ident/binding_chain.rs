// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BindingChain resolution for identifier evaluation.
//!
//! Resolves identifiers via chain lookup, handling dependency tracking
//! and lazy thunk forcing.

use crate::{
    current_state_lookup_mode, force_lazy_binding, force_lazy_thunk_if_needed,
    is_dep_tracking_active, lazy_binding_cache_hit_deps, propagate_cached_deps, record_local_read,
    EvalCtx, EvalResult, Value,
};
use tla_core::name_intern::NameId;

/// Resolve an identifier via BindingChain lookup, handling dep tracking and lazy thunks.
///
/// Returns `Ok(Some(value))` if resolved, `Ok(None)` if not found in chain.
///
/// Part of #3260: extracted from duplicated fast-path and slow-path blocks in `eval_ident`.
/// Part of #3963: restructured to fast-path Eager+None bindings (the common case for
/// quantifier variables, LET bindings, function parameters) — avoids redundant as_lazy()
/// check, source dispatch, and thunk forcing for simple resolved values.
#[inline]
pub(crate) fn resolve_binding_chain(ctx: &EvalCtx, lookup_id: NameId) -> EvalResult<Option<Value>> {
    let Some((bv, source)) = ctx.bindings.lookup(lookup_id) else {
        return Ok(None);
    };

    // Fast path: Eager value with no dependency metadata (BindingSourceRef::None).
    // This is the overwhelmingly common case — quantifier variables, LET bindings,
    // and function parameters are all Eager+None. Skips as_lazy() check, source
    // dispatch, and thunk forcing for non-closure values.
    //
    // Part of #3963: Split into inline vs heap sub-paths. Inline CompactValues
    // (Bool, SmallInt — tag != TAG_HEAP) cannot be Closures, so we skip the
    // force_lazy_thunk_if_needed check entirely. This eliminates a function call,
    // a Value::Closure match, and a clone for the most common binding types.
    if let crate::binding_chain::BindingValueRef::Eager(cv) = bv {
        if let crate::binding_chain::BindingSourceRef::None = source {
            if !cv.is_heap() {
                // Inline value (Bool/SmallInt): cannot be a Closure thunk.
                // Use to_value_inline() which skips the heap check — we already
                // verified !is_heap() above. This eliminates one branch from
                // the hottest eval path (quantifier variable resolution).
                return Ok(Some(cv.to_value_inline()));
            }
            // Heap value: peek at the discriminant to check if it's a zero-arg
            // Closure (lazy thunk) without converting to Value first. Most heap
            // values are strings, sets, records, etc. — not closures.
            // This eliminates a Value conversion + clone for the common case.
            if !cv.is_zero_arg_closure() {
                return Ok(Some(Value::from(cv)));
            }
            // Confirmed zero-arg closure: must force the thunk.
            // force_lazy_thunk_if_needed takes Value by value — no redundant clone.
            return Ok(Some(force_lazy_thunk_if_needed(ctx, Value::from(cv))?));
        }
    }

    resolve_binding_chain_slow(ctx, lookup_id, bv, source)
}

/// Non-inlined slow path for binding chain resolution.
///
/// Handles Eager+Instance, Eager+Local/Liveness (dep tracking), and all Lazy bindings.
/// Separated from the inlined fast path to keep code size small at call sites.
///
/// Part of #3963: extracted from resolve_binding_chain to reduce inlined code size.
#[inline(never)]
fn resolve_binding_chain_slow(
    ctx: &EvalCtx,
    lookup_id: NameId,
    bv: crate::binding_chain::BindingValueRef<'_>,
    source: crate::binding_chain::BindingSourceRef<'_>,
) -> EvalResult<Option<Value>> {
    // Eager path: value is immediately available.
    if let crate::binding_chain::BindingValueRef::Eager(cv) = bv {
        let v = Value::from(cv);
        match source {
            crate::binding_chain::BindingSourceRef::Instance(deps) => {
                if is_dep_tracking_active(ctx) {
                    propagate_cached_deps(ctx, deps);
                }
            }
            crate::binding_chain::BindingSourceRef::Local(stack_idx)
            | crate::binding_chain::BindingSourceRef::Liveness(stack_idx) => {
                record_local_read(ctx, stack_idx, lookup_id, &v);
            }
            crate::binding_chain::BindingSourceRef::None => {}
        }
        // Part of #3963: Skip thunk check for inline (non-heap) CompactValues.
        // Only heap-allocated values can be Closures (lazy thunks).
        // Extended: also skip for heap values that aren't zero-arg closures.
        if !cv.is_zero_arg_closure() {
            return Ok(Some(v));
        }
        // force_lazy_thunk_if_needed takes Value by value — no redundant clone.
        return Ok(Some(force_lazy_thunk_if_needed(ctx, v)?));
    }

    // Lazy path: check INSTANCE lazy cache, then force.
    // Defer mode lookup to here — Eager path above doesn't need it.
    let mode = current_state_lookup_mode(ctx);
    let lazy = match bv.as_lazy() {
        Some(lazy) => lazy,
        None => return Ok(None),
    };

    if let crate::binding_chain::BindingSourceRef::Instance(_) = source {
        let lazy_ptr = lazy as *const crate::binding_chain::LazyBinding as usize;
        if let Some(cached) =
            crate::cache::small_caches::instance_lazy_cache_get(lazy_ptr, mode as u8)
        {
            lazy_binding_cache_hit_deps(ctx, lazy, source, &cached, lookup_id, mode);
            return Ok(Some(cached));
        }
    }

    force_lazy_binding(ctx, lazy, source, lookup_id, mode).map(Some)
}
