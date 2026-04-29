// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Quantifier subexpression hoisting cache.
//!
//! Before a quantifier loop starts, `mark_hoistable` identifies which
//! subexpressions of the body are bound-variable-invariant (don't reference
//! any bound variable). Their evaluated results are cached by AST pointer
//! in a thread-local stack frame. On subsequent loop iterations, the cached
//! result is returned without re-evaluation.
//!
//! Part of #3128: Eliminates redundant computation in `eval_exists`,
//! `eval_forall`, `eval_choose`, and set builders.
//!
//! Analysis logic (mark_hoistable AST walk) is in `mark_hoistable.rs`.

use crate::value::Value;
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::Cell;
use std::cell::RefCell;
use std::rc::Rc;
use tla_core::ast::Expr;

/// Part of #3128: Double-evaluation verification mode.
/// When `true` AND `cfg!(debug_assertions)`, every hoist cache hit is verified
/// by re-evaluating the expression fresh. A mismatch panics with the expression
/// kind, cached value, and fresh value. Use to confirm the Stage 1 allowlist
/// is correct. MUST be `false` in production/CI.
#[cfg(debug_assertions)]
#[allow(dead_code)]
pub(crate) const HOIST_VERIFY: bool = false;

/// Per-quantifier cache for bound-variable-independent subexpressions.
struct QuantifierHoistCache {
    /// Set of AST node pointers that are safe to cache (Rc-shared with
    /// MARK_HOISTABLE_CACHE to avoid cloning — Part of #3100).
    hoistable: Rc<FxHashSet<usize>>,
    /// Cached evaluation results for hoistable nodes.
    values: FxHashMap<usize, Value>,
    /// State-generation at frame creation. Cache hits/stores are only valid
    /// while the evaluator stays in the same state context.
    creation_gen: u32,
}

// Part of #3962: Consolidated 3 quantifier-hoist thread_locals into a single struct.
// Previously each was a separate `thread_local!` declaration, requiring 3 separate
// `_tlv_get_addr` calls on macOS. Now a single TLS access covers all hoist state.
// The `active` and `state_generation` fields are Cell<> for non-borrowing access;
// `stack` is RefCell<> because push/pop needs mutable borrow.
// Wave 25: MARK_HOISTABLE_CACHE consolidated here (from mark_hoistable.rs) —
// 1 more thread_local eliminated. The mark_hoistable cache is accessed at
// quantifier entry and its lifecycle is tied to quantifier_hoist_cache clearing.
struct HoistState {
    stack: RefCell<Vec<QuantifierHoistCache>>,
    /// Part of #3073: Fast boolean flag tracking whether stack is non-empty.
    active: Cell<bool>,
    /// Part of #3147: Bumped whenever eval switches from current-state to
    /// next-state evaluation for the same AST node.
    state_generation: Cell<u32>,
    /// Part of #3962 Wave 25: Consolidated from mark_hoistable.rs MARK_HOISTABLE_CACHE.
    /// Cache `mark_hoistable` results by (body_ptr, bounds_ptr).
    /// The hoistable set depends on BOTH the quantifier body AND which bound
    /// variables are in scope. For multi-bound quantifiers like `\A x \in S, y \in T : body`,
    /// eval_forall recurses with bounds[1..], producing different bound name sets
    /// for the same body.
    mark_hoistable_cache: RefCell<FxHashMap<(usize, usize), Rc<FxHashSet<usize>>>>,
}

thread_local! {
    static HOIST_STATE: HoistState = HoistState {
        stack: RefCell::new(Vec::new()),
        active: Cell::new(false),
        state_generation: Cell::new(0),
        mark_hoistable_cache: RefCell::new(FxHashMap::default()),
    };
}

/// RAII guard for a quantifier hoist scope. Pops the frame on drop.
pub(crate) struct QuantifierHoistScopeGuard {
    _private: (),
}

/// RAII guard that temporarily advances the hoist state generation.
/// When no hoist scope is active, the guard is a no-op (previous_generation
/// is None) and Drop skips the thread-local restore.
///
/// Part of #3962: Optionally holds a raw pointer to the `hoist_state_generation`
/// shadow Cell on `EvalRuntimeState`, so that Drop can restore the shadow
/// alongside the TLS value. Without this, ctx-aware hoist lookups
/// (`quantifier_hoist_lookup_ctx`, `tir_hoist_lookup_ctx`) would see stale
/// generation values until the next 64-eval sync, causing incorrect cache hits
/// during next-state evaluation within quantifier loops.
#[must_use]
pub(crate) struct HoistGenerationGuard {
    previous_generation: Option<u32>,
    /// Raw pointer to the `Cell<u32>` shadow in `EvalRuntimeState`. Null when
    /// created without ctx (no-op guard or non-ctx callers).
    /// SAFETY: Same lifetime argument as `EnabledScopeGuard::shadow_ptr` — the
    /// shadow Cell lives in `EvalRuntimeState` which is alive for the duration
    /// of the enclosing scope.
    shadow_ptr: *const Cell<u32>,
}

impl Drop for QuantifierHoistScopeGuard {
    fn drop(&mut self) {
        // Part of #3962: Single TLS access for both stack pop and active flag update.
        HOIST_STATE.with(|hs| {
            let mut s = hs.stack.borrow_mut();
            s.pop();
            if s.is_empty() {
                hs.active.set(false);
            }
        });
    }
}

impl Drop for HoistGenerationGuard {
    fn drop(&mut self) {
        if let Some(prev) = self.previous_generation {
            HOIST_STATE.with(|hs| hs.state_generation.set(prev));
            // Part of #3962: Restore the shadow so ctx-aware lookups see the
            // correct generation value immediately, not after the next 64-eval sync.
            if !self.shadow_ptr.is_null() {
                // SAFETY: shadow_ptr points to a Cell<u32> in EvalRuntimeState
                // which is alive for the duration of the enclosing scope.
                unsafe { &*self.shadow_ptr }.set(prev);
            }
        }
    }
}

/// Push a new hoist cache frame. Returns `Some(guard)` if a frame was pushed,
/// `None` if no frame is needed.
///
/// Part of #3128: Always pushes a shield frame when nested inside an existing
/// hoist scope, even if this quantifier has no hoistable expressions. Without
/// this, the outer frame's hoistable set would be consulted during the inner
/// quantifier's loop iterations, incorrectly caching subexpressions that
/// depend on the inner bound variable.
pub(crate) fn enter_quantifier_hoist_scope(
    hoistable: Rc<FxHashSet<usize>>,
) -> Option<QuantifierHoistScopeGuard> {
    // Part of #3962: Single TLS access for dominated check, generation read,
    // stack push, and active flag set.
    HOIST_STATE.with(|hs| {
        let dominated = hs.active.get();
        if hoistable.is_empty() && !dominated {
            return None;
        }
        let creation_gen = hs.state_generation.get();
        hs.stack.borrow_mut().push(QuantifierHoistCache {
            hoistable,
            values: FxHashMap::default(),
            creation_gen,
        });
        hs.active.set(true);
        Some(QuantifierHoistScopeGuard { _private: () })
    })
}

/// Look up a cached value for the given expression. Checks the top frame only.
/// Returns `None` when the suppress flag is active (used by HOIST_VERIFY).
/// Part of #3128, #3364: Runtime guard — only return cached values for
/// hoist-safe expressions (Stage-1 structural + Stage-2 set construction).
#[inline]
#[allow(dead_code)] // Used by tests; production hot path uses quantifier_hoist_lookup_ctx
pub(crate) fn quantifier_hoist_lookup(expr: &Expr) -> Option<Value> {
    #[cfg(debug_assertions)]
    if HOIST_LOOKUP_SUPPRESSED.with(std::cell::Cell::get) {
        return None;
    }
    if !super::mark_hoistable::is_hoist_cacheable(expr) {
        return None;
    }
    let key = expr as *const Expr as usize;
    // Part of #3962: Single TLS access for generation read + stack lookup.
    HOIST_STATE.with(|hs| {
        let current_gen = hs.state_generation.get();
        let stack = hs.stack.borrow();
        let frame = stack.last()?;
        if frame.creation_gen != current_gen {
            return None;
        }
        frame.values.get(&key).cloned()
    })
}

/// Part of #3962: Ctx-aware variant of `quantifier_hoist_lookup` that reads
/// `hoist_state_generation` from the `EvalRuntimeState` shadow instead of
/// the `HOIST_STATE` thread-local for the generation. Eliminates the generation
/// read from TLS. The shadow is synced every 64 evals in `eval()` and at
/// hoist scope entry/exit/bump boundaries.
#[inline]
pub(crate) fn quantifier_hoist_lookup_ctx(ctx: &crate::EvalCtx, expr: &Expr) -> Option<Value> {
    #[cfg(debug_assertions)]
    if HOIST_LOOKUP_SUPPRESSED.with(std::cell::Cell::get) {
        return None;
    }
    if !super::mark_hoistable::is_hoist_cacheable(expr) {
        return None;
    }
    let key = expr as *const Expr as usize;
    let current_gen = ctx.runtime_state.hoist_state_generation.get();
    HOIST_STATE.with(|hs| {
        let stack = hs.stack.borrow();
        let frame = stack.last()?;
        if frame.creation_gen != current_gen {
            return None;
        }
        frame.values.get(&key).cloned()
    })
}

// === HOIST_VERIFY support ===

#[cfg(debug_assertions)]
thread_local! {
    /// When `true`, `quantifier_hoist_lookup` returns `None` unconditionally.
    /// Used by the HOIST_VERIFY path to force fresh evaluation while the
    /// hoist frame is still active (so the store path still records values).
    static HOIST_LOOKUP_SUPPRESSED: Cell<bool> = const { Cell::new(false) };
}

/// RAII guard that suppresses hoist lookups for the duration of its lifetime.
/// Clears the suppress flag on drop.
#[cfg(debug_assertions)]
#[allow(dead_code)]
pub(crate) struct SuppressHoistLookupGuard;

#[cfg(debug_assertions)]
impl Drop for SuppressHoistLookupGuard {
    fn drop(&mut self) {
        HOIST_LOOKUP_SUPPRESSED.with(|s| s.set(false));
    }
}

/// Temporarily suppress hoist cache lookups. Returns an RAII guard.
/// While the guard is alive, `quantifier_hoist_lookup` returns `None`,
/// forcing fresh evaluation of expressions that would otherwise be served
/// from the hoist cache.
#[cfg(debug_assertions)]
#[allow(dead_code)]
pub(crate) fn suppress_hoist_lookup() -> SuppressHoistLookupGuard {
    HOIST_LOOKUP_SUPPRESSED.with(|s| s.set(true));
    SuppressHoistLookupGuard
}

/// Store a value in the hoist cache if the expression is hoistable.
/// Part of #3128, #3364: Belt-and-suspenders runtime guard — only store if
/// the expression is hoist-safe (Stage-1 structural + Stage-2 set
/// construction). This catches cases where the hoistable set contains pointers
/// that shouldn't be cached (e.g., FuncApply nodes incorrectly included due
/// to pointer aliasing or cache-key collisions in MARK_HOISTABLE_CACHE).
#[inline]
#[allow(dead_code)] // Used by tests; production hot path uses quantifier_hoist_store_ctx
pub(crate) fn quantifier_hoist_store(expr: &Expr, value: &Value) {
    let key = expr as *const Expr as usize;
    // Part of #3962: Single TLS access for generation read + stack store.
    HOIST_STATE.with(|hs| {
        let current_gen = hs.state_generation.get();
        let mut stack = hs.stack.borrow_mut();
        if let Some(frame) = stack.last_mut() {
            if frame.creation_gen != current_gen {
                return;
            }
            if frame.hoistable.contains(&key) && super::mark_hoistable::is_hoist_cacheable(expr) {
                frame.values.insert(key, value.clone());
            }
        }
    });
}

/// Part of #3962: Ctx-aware variant of `quantifier_hoist_store` that reads
/// `hoist_state_generation` from the `EvalRuntimeState` shadow instead of
/// the `HOIST_STATE` thread-local for the generation. Eliminates 1 TLS read per
/// eval_expr call when hoist is active.
#[inline]
pub(crate) fn quantifier_hoist_store_ctx(ctx: &crate::EvalCtx, expr: &Expr, value: &Value) {
    let key = expr as *const Expr as usize;
    let current_gen = ctx.runtime_state.hoist_state_generation.get();
    HOIST_STATE.with(|hs| {
        let mut stack = hs.stack.borrow_mut();
        if let Some(frame) = stack.last_mut() {
            if frame.creation_gen != current_gen {
                return;
            }
            if frame.hoistable.contains(&key) && super::mark_hoistable::is_hoist_cacheable(expr) {
                frame.values.insert(key, value.clone());
            }
        }
    });
}

/// Look up a cached value for a TIR expression by its pointer address.
/// Uses the same hoist stack as AST lookups — keys don't collide because
/// TIR and AST nodes occupy different memory.
///
/// Part of #3392: Closes the hoist-cache gap between AST and TIR evaluation.
#[inline]
#[allow(dead_code)] // Used by tests; production hot path uses tir_hoist_lookup_ctx
pub(crate) fn tir_hoist_lookup(key: usize) -> Option<Value> {
    // Part of #3962: Single TLS access for generation read + stack lookup.
    HOIST_STATE.with(|hs| {
        let current_gen = hs.state_generation.get();
        let stack = hs.stack.borrow();
        let frame = stack.last()?;
        if frame.creation_gen != current_gen {
            return None;
        }
        frame.values.get(&key).cloned()
    })
}

/// Part of #3962: Ctx-aware variant of `tir_hoist_lookup` that reads
/// `hoist_state_generation` from the `EvalRuntimeState` shadow instead of
/// the `HOIST_STATE` thread-local. Eliminates 1 TLS read per
/// eval_tir_expr call when hoist is active.
#[inline]
pub(crate) fn tir_hoist_lookup_ctx(ctx: &crate::EvalCtx, key: usize) -> Option<Value> {
    let current_gen = ctx.runtime_state.hoist_state_generation.get();
    HOIST_STATE.with(|hs| {
        let stack = hs.stack.borrow();
        let frame = stack.last()?;
        if frame.creation_gen != current_gen {
            return None;
        }
        frame.values.get(&key).cloned()
    })
}

/// Store a value in the hoist cache for a TIR expression by its pointer address.
///
/// Part of #3392.
#[inline]
#[allow(dead_code)] // Used by tests; production hot path uses tir_hoist_store_ctx
pub(crate) fn tir_hoist_store(key: usize, value: &Value) {
    // Part of #3962: Single TLS access for generation read + stack store.
    HOIST_STATE.with(|hs| {
        let current_gen = hs.state_generation.get();
        let mut stack = hs.stack.borrow_mut();
        if let Some(frame) = stack.last_mut() {
            if frame.creation_gen != current_gen {
                return;
            }
            if frame.hoistable.contains(&key) {
                frame.values.insert(key, value.clone());
            }
        }
    });
}

/// Part of #3962: Ctx-aware variant of `tir_hoist_store` that reads
/// `hoist_state_generation` from the `EvalRuntimeState` shadow instead of
/// the `HOIST_STATE` thread-local. Eliminates 1 TLS read per
/// eval_tir_expr call when hoist is active.
#[inline]
pub(crate) fn tir_hoist_store_ctx(ctx: &crate::EvalCtx, key: usize, value: &Value) {
    let current_gen = ctx.runtime_state.hoist_state_generation.get();
    HOIST_STATE.with(|hs| {
        let mut stack = hs.stack.borrow_mut();
        if let Some(frame) = stack.last_mut() {
            if frame.creation_gen != current_gen {
                return;
            }
            if frame.hoistable.contains(&key) {
                frame.values.insert(key, value.clone());
            }
        }
    });
}

/// Check whether a hoist scope is currently active.
/// Part of #3073: Uses a Cell<bool> flag instead of RefCell<Vec>::borrow().is_empty().
/// Called 2x per eval_expr — this is the hottest check in the evaluator.
/// Part of #3962: Now reads from consolidated HOIST_STATE (single TLS access).
#[inline]
pub(crate) fn is_hoist_active() -> bool {
    HOIST_STATE.with(|hs| hs.active.get())
}

/// Part of #3962: Read the current hoist state generation from TLS.
/// Used by eval()'s 64-eval sync to update the `EvalRuntimeState` shadow.
#[inline]
pub(crate) fn hoist_state_generation_tls() -> u32 {
    HOIST_STATE.with(|hs| hs.state_generation.get())
}

/// Advance the hoist state generation for a next-state evaluation and restore
/// the previous generation when the returned guard is dropped.
///
/// When no hoist scope is active (`is_hoist_active()` returns false), this is
/// a no-op: no thread-local generation counter is touched, and the returned
/// guard skips restoration on drop. This avoids 12 unnecessary thread-local
/// accesses per eval_prime invocation when HOIST_ENABLED=false (Part of #3392).
///
/// For callers without ctx access. Prefer `bump_hoist_state_generation_ctx`
/// when ctx is available (all production callers) to keep the shadow in sync.
#[inline(always)]
#[allow(dead_code)] // Kept for callers without ctx; production uses bump_hoist_state_generation_ctx
pub(crate) fn bump_hoist_state_generation() -> HoistGenerationGuard {
    if !is_hoist_active() {
        return HoistGenerationGuard {
            previous_generation: None,
            shadow_ptr: std::ptr::null(),
        };
    }
    // Part of #3962: Single TLS access for generation read + bump.
    let previous_generation = HOIST_STATE.with(|hs| {
        let previous = hs.state_generation.get();
        hs.state_generation.set(previous.wrapping_add(1));
        previous
    });
    HoistGenerationGuard {
        previous_generation: Some(previous_generation),
        shadow_ptr: std::ptr::null(),
    }
}

/// Part of #3962: Ctx-aware variant of `bump_hoist_state_generation` that also
/// syncs the `hoist_state_generation` shadow on `EvalRuntimeState`. The guard's
/// Drop restores both TLS and shadow to the previous generation.
///
/// This prevents stale cache hits during next-state evaluation within quantifier
/// loops: without shadow sync, `quantifier_hoist_lookup_ctx` and
/// `tir_hoist_lookup_ctx` would see the pre-bump generation and match against
/// `creation_gen`, returning stale current-state values.
#[inline(always)]
pub(crate) fn bump_hoist_state_generation_ctx(ctx: &crate::EvalCtx) -> HoistGenerationGuard {
    // Use TLS `is_hoist_active()` for the guard condition, not the shadow,
    // because the shadow is only synced every 64 evals and may be stale at
    // hoist scope entry. The guard condition must always be correct.
    if !is_hoist_active() {
        return HoistGenerationGuard {
            previous_generation: None,
            shadow_ptr: std::ptr::null(),
        };
    }
    let shadow_cell = &ctx.runtime_state.hoist_state_generation;
    // Part of #3962: Single TLS access for generation read + bump + shadow sync.
    let previous_generation = HOIST_STATE.with(|hs| {
        let previous = hs.state_generation.get();
        let bumped = previous.wrapping_add(1);
        hs.state_generation.set(bumped);
        // Sync shadow immediately so ctx-aware lookups see the bumped generation.
        shadow_cell.set(bumped);
        previous
    });
    HoistGenerationGuard {
        previous_generation: Some(previous_generation),
        // SAFETY: shadow_cell points to a Cell<u32> in EvalRuntimeState which
        // is alive for the duration of the enclosing scope (the caller holds a
        // reference to EvalCtx which owns EvalRuntimeState via Rc).
        shadow_ptr: shadow_cell as *const Cell<u32>,
    }
}

/// Permanently advance the hoist state generation (no RAII restore).
/// Used by `set_next_state()` where the state change is not temporary.
///
/// Part of #3407: When no hoist scope is active, this is a no-op.
#[inline(always)]
#[allow(dead_code)] // Kept for callers without ctx; production uses advance_hoist_state_generation_ctx
pub(crate) fn advance_hoist_state_generation() {
    if !is_hoist_active() {
        return;
    }
    HOIST_STATE.with(|hs| {
        hs.state_generation
            .set(hs.state_generation.get().wrapping_add(1));
    });
}

/// Part of #3962: Ctx-aware variant of `advance_hoist_state_generation` that
/// also syncs the `hoist_state_generation` shadow on `EvalRuntimeState`.
#[inline(always)]
pub(crate) fn advance_hoist_state_generation_ctx(ctx: &crate::EvalCtx) {
    // Use TLS `is_hoist_active()` for the guard condition (see
    // bump_hoist_state_generation_ctx comment for rationale).
    if !is_hoist_active() {
        return;
    }
    HOIST_STATE.with(|hs| {
        let bumped = hs.state_generation.get().wrapping_add(1);
        hs.state_generation.set(bumped);
        ctx.runtime_state.hoist_state_generation.set(bumped);
    });
}

/// Clear the entire hoist stack and mark_hoistable cache (used by lifecycle reset).
/// Hoist stack is cleared first so no frames hold dangling Rc references
/// when mark_hoistable_cache entries are dropped.
pub(crate) fn clear_quantifier_hoist_cache() {
    // Part of #3962 Wave 25: Single TLS access for all hoist state clearing,
    // including mark_hoistable_cache (consolidated from separate thread_local).
    HOIST_STATE.with(|hs| {
        hs.stack.borrow_mut().clear();
        hs.active.set(false);
        hs.state_generation.set(0);
        hs.mark_hoistable_cache.borrow_mut().clear();
    });
}

/// Part of #3962 Wave 25: Look up a cached mark_hoistable result by cache key.
/// Returns `Some(Rc<...>)` if a matching entry exists, `None` otherwise.
/// Consolidated from the standalone `MARK_HOISTABLE_CACHE` thread_local.
#[inline]
pub(crate) fn mark_hoistable_cache_get(cache_key: &(usize, usize)) -> Option<Rc<FxHashSet<usize>>> {
    HOIST_STATE.with(|hs| {
        hs.mark_hoistable_cache
            .borrow()
            .get(cache_key)
            .map(Rc::clone)
    })
}

/// Part of #3962 Wave 25: Store a mark_hoistable result in the consolidated cache.
/// Consolidated from the standalone `MARK_HOISTABLE_CACHE` thread_local.
#[inline]
pub(crate) fn mark_hoistable_cache_insert(cache_key: (usize, usize), result: Rc<FxHashSet<usize>>) {
    HOIST_STATE.with(|hs| {
        hs.mark_hoistable_cache
            .borrow_mut()
            .insert(cache_key, result);
    });
}

/// Part of #3962 Wave 25: Get current mark_hoistable_cache length (for tests).
#[cfg(test)]
pub(crate) fn mark_hoistable_cache_len() -> usize {
    HOIST_STATE.with(|hs| hs.mark_hoistable_cache.borrow().len())
}
