// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cache lifecycle orchestration: CacheEvent dispatch, clear/trim functions.
//!
//! This module owns no storage — it imports clear functions from all other cache
//! modules and orchestrates lifecycle transitions.
//!
//! Part of #2744 decomposition from eval_cache.rs.

use super::lifecycle_trim::trim_eval_entry_caches;
use super::op_result_cache::{clear_nary_all_partitions, clear_nary_state_partition};
use super::small_caches::SMALL_CACHES;
use super::subst_cache::{
    clear_subst_cache, clear_subst_guard, evict_next_state_subst_entries, SUBST_STATE,
};
use super::zero_arg_cache::{clear_zero_arg_all_partitions, clear_zero_arg_state_partition};
use std::cell::Cell;

// Part of #3099: Reduce trim_eval_entry_caches from every eval exit to every
// TRIM_INTERVAL exits. The soft caps are large enough (10K-50K) that checking
// less frequently doesn't cause meaningful extra memory use, but saves
// 9 thread-local accesses per eval_entry call on the common (under-cap) path.
const TRIM_INTERVAL: u32 = 128;

// Part of #3962: Consolidated EVAL_EXIT_COUNT and IN_ENABLED_SCOPE into a single
// thread-local struct. Previously 2 separate `thread_local!` declarations — each
// access was a separate `_tlv_get_addr` call on macOS. Now a single TLS access
// covers both lifecycle tracking fields.
struct LifecycleState {
    eval_exit_count: Cell<u32>,
    /// Part of #2998: Thread-local flag tracking whether we are inside ENABLED evaluation.
    /// TLC disables LazyValue caching within ENABLED scope via EvalControl.Enabled bitflag
    /// (EvalControl.java:22-25, Tool.java:1949-1953). TLA2 uses this flag to clear PerState
    /// caches at ENABLED scope boundaries, preventing cross-scope cache contamination.
    in_enabled_scope: Cell<bool>,
    /// Part of #3805: State generation at last eval_scope_boundary clear.
    /// Used to deduplicate `clear_for_eval_scope_boundary()` calls within a single
    /// state's evaluation. When multiple `N!Op` references (nested INSTANCE bodies)
    /// are evaluated within the same state, only the first triggers the expensive
    /// cache clear. Subsequent calls within the same state generation are no-ops.
    ///
    /// This fixes the MCNanoMedium performance outlier where every `N!Op` reference
    /// flushed all state-dependent caches, causing O(instance_refs * operators)
    /// re-evaluations per state instead of O(operators).
    last_scope_boundary_gen: Cell<u64>,
}

thread_local! {
    static LIFECYCLE_STATE: LifecycleState = const { LifecycleState {
        eval_exit_count: Cell::new(0),
        in_enabled_scope: Cell::new(false),
        last_scope_boundary_gen: Cell::new(u64::MAX),
    } };
}

/// RAII guard for ENABLED evaluation scope. On entry (first non-nested call) and
/// on exit, clears state-dependent caches while retaining proven-constant entries
/// in ZERO_ARG_OP_CACHE and NARY_OP_CACHE.
///
/// Part of #3109: Cache insertion is skipped during ENABLED scope (guarded by
/// `in_enabled_scope()` at each insertion point). This prevents the #3055
/// misclassification bug (ENABLED dep tracking through env, not state_env).
/// Since no new entries are created during ENABLED, only pre-ENABLED entries
/// exist at scope boundaries — constant entries are reliably classified and
/// safe to retain.
///
/// Part of #2998: TLC's `semanticallyEquivalent()` treats `Clear` and `Enabled`
/// as cache-incompatible (EvalControl.java:108-128). This guard achieves the
/// same isolation by (1) skipping cache insertion during ENABLED and (2)
/// clearing non-constant caches at scope transitions.
///
/// Part of #4027: Optionally holds a pointer to the `EvalRuntimeState.in_enabled_scope`
/// shadow Cell, so that `Drop` can clear the shadow alongside the TLS flag. Without
/// this, the shadow stays stale (true) for up to 64 evals after ENABLED scope exit,
/// causing missed cache insertions at sites that read via `in_enabled_scope_ctx()`.
pub struct EnabledScopeGuard {
    /// Raw pointer to the `Cell<bool>` shadow in `EvalRuntimeState`. Set by
    /// `enter_enabled_scope_with_ctx()`, null for the base `enter_enabled_scope()`.
    /// SAFETY: The shadow Cell lives in `EvalRuntimeState` which is borrowed by
    /// the caller of `enter_enabled_scope_with_ctx()`. The guard is always dropped
    /// before that borrow ends (it's stored in a local variable in the same scope).
    shadow_ptr: *const Cell<bool>,
}

impl Drop for EnabledScopeGuard {
    fn drop(&mut self) {
        // Part of #3109: On ENABLED scope exit, clear state-dependent caches but
        // retain proven-constant entries. Since Step 1 (skip caching) prevents new
        // entries during ENABLED, only pre-ENABLED entries exist — constants are
        // reliably classified and safe to retain across scope transitions.
        clear_enabled_scope_impl();
        LIFECYCLE_STATE.with(|ls| ls.in_enabled_scope.set(false));
        // Part of #4027: Clear the shadow immediately on scope exit so cache
        // insertion sites reading via `in_enabled_scope_ctx()` see the correct
        // value without waiting for the next 64-eval sync.
        if !self.shadow_ptr.is_null() {
            // SAFETY: shadow_ptr points to a Cell<bool> in EvalRuntimeState which
            // is alive for the duration of the enclosing scope (the caller holds a
            // reference to EvalCtx which owns EvalRuntimeState). The guard is always
            // dropped before that borrow ends.
            unsafe { &*self.shadow_ptr }.set(false);
        }
    }
}

/// Enter ENABLED evaluation scope. On the outermost entry, clears state-dependent
/// caches while retaining proven-constant entries. Returns `Some(guard)` if this is
/// the outermost entry, `None` if already in scope. The guard clears caches again
/// on drop, retaining constants.
///
/// Part of #3109: Combined with Step 1 (skip caching during ENABLED), only pre-ENABLED
/// entries exist at scope boundaries. Pre-ENABLED constant entries have reliable dep
/// tracking and are safe to retain, avoiding expensive re-computation of module-constant
/// operators (e.g., DyadicRationals `Zero`/`Add`/`Half`/`Reduce` in Huang).
///
/// Part of #2998: Matches TLC's EvalControl.Enabled cache isolation.
/// TLC reference: EvalControl.java:22-25, Tool.java:1949-1953.
pub fn enter_enabled_scope() -> Option<EnabledScopeGuard> {
    // Part of #3962: Use consolidated LIFECYCLE_STATE for in_enabled_scope check.
    LIFECYCLE_STATE.with(|ls| {
        if !ls.in_enabled_scope.get() {
            ls.in_enabled_scope.set(true);
            // Part of #3109: Retain proven-constant entries. Step 1 prevents
            // ENABLED-scope entries, so pre-ENABLED constants are safe.
            clear_enabled_scope_impl();
            Some(EnabledScopeGuard {
                shadow_ptr: std::ptr::null(),
            })
        } else {
            // Already in ENABLED scope (nested call): no-op.
            None
        }
    })
}

/// Part of #3962: Context-aware variant of `enter_enabled_scope` that also syncs
/// the `in_enabled_scope` shadow field on `EvalRuntimeState`. This ensures cache
/// insertion guards read the correct value from the shadow without a 64-eval
/// sync delay. Use this when `ctx` is available (all production callers).
///
/// Part of #4027: The returned guard stores a pointer to the shadow Cell so that
/// `Drop` clears the shadow alongside the TLS flag, preventing stale shadow
/// values from suppressing cache insertions after ENABLED scope exit.
pub fn enter_enabled_scope_with_ctx(ctx: &crate::EvalCtx) -> Option<EnabledScopeGuard> {
    let mut guard = enter_enabled_scope()?;
    // Sync shadow immediately so cache insertion checks see the correct value.
    ctx.runtime_state.in_enabled_scope.set(true);
    // Store pointer so Drop can clear the shadow.
    guard.shadow_ptr = &ctx.runtime_state.in_enabled_scope as *const Cell<bool>;
    Some(guard)
}

/// Core PerState cache clearing: clears SUBST_CACHE, THUNK_DEP_CACHE,
/// and evicts next-state EAGER_BINDINGS entries. Does NOT retain constant entries in
/// ZERO_ARG_OP_CACHE or NARY_OP_CACHE — callers that need the retain step should use
/// `clear_state_boundary_impl()` instead.
///
/// Part of #3025: OP_RESULT_CACHE clear removed — cache had zero insertions.
/// Part of #3055: Extracted to avoid redundant retain-then-clear in
/// `clear_enabled_scope_impl()`, which calls this and then full-clears the caches
/// that `clear_state_boundary_impl()` would have retained.
#[inline]
fn clear_state_boundary_core_impl() {
    // Part of #3805: Single TLS access for both subst cache + guard clearing.
    SUBST_STATE.with(|s| {
        let mut s = s.borrow_mut();
        s.cache.clear();
        s.eval_guard.clear();
    });
    // Part of #3962: Single TLS access to clear all PerState fields in SMALL_CACHES.
    // Previously 4 separate thread_local accesses (THUNK_DEP_CACHE, INSTANCE_LAZY_CACHE,
    // CHOOSE_CACHE, CHOOSE_DEEP_CACHE).
    SMALL_CACHES.with(|sc| {
        let mut sc = sc.borrow_mut();
        // Fix #1498: Clear thunk dep cache — thunk results may depend on state.
        sc.thunk_dep_cache.clear();
        // Part of #3465: Clear INSTANCE lazy binding cache — forced values are state-dependent.
        sc.instance_lazy_cache.clear();
        // Clear CHOOSE memoization caches — CHOOSE results depend on state.
        sc.choose_cache.clear();
        // Part of #3905: Clear deep CHOOSE cache (binding_depth > 0 entries).
        sc.choose_deep_cache.clear();
    });
    // Fix #2928: Evict next-state eager bindings. The EAGER_BINDINGS_CACHE key
    // uses state_ptr and next_state_ptr for identity, but in eval_unchanged's
    // Tier 2 (HashMap) path, both are 0 (state_env=None, next_state_env=None).
    // Without eviction, cached substitution values from a previous successor
    // contaminate evaluations for subsequent successors from the same parent,
    // causing false action-property violations (e.g., UNCHANGED RAF!vars).
    crate::helpers::evict_next_state_eager_bindings();
}

/// Part of #3100: With partitioned caches, state boundary just clears the state
/// partitions. Persistent entries (empty deps) survive in their own partition.
/// Replaces the old O(cache_size) retain scans.
#[inline]
fn clear_state_boundary_impl() {
    clear_state_boundary_core_impl();
    clear_zero_arg_state_partition();
    clear_nary_state_partition();
}

/// Clear caches at ENABLED scope boundaries.
///
/// Part of #3109: ENABLED scope preserves ALL entries in ZERO_ARG_OP_CACHE and
/// NARY_OP_CACHE — not just constants. This matches TLC's approach where ENABLED
/// scope never evicts cached LazyValue entries (EvalControl.java:108-128).
///
/// Safety argument for preserving non-constant entries:
/// - During ENABLED, `eval_enabled_cp` takes `state_env` (sets it to None) and
///   rebinds state variables into `env`. Entries with state deps fail validation
///   via `op_cache_entry_valid` (line 102: `let Some(state_env) = ctx.state_env`
///   returns false when None). Entries with local-only deps pass validation and
///   return correct results (same local bindings). Constant entries always pass.
/// - After ENABLED exit, `take_state_env_guard` restores the same `Arc` (pointer
///   identity preserved). All entries become valid again — no re-evaluation needed.
/// - Cache insertion is guarded by `in_enabled_scope()` (Step 1 of #3109), so no
///   new entries contaminate caches during ENABLED.
///
/// Only clears SUBST_CACHE (no dep validation on lookup), THUNK_DEP_CACHE
/// (store_thunk_deps not guarded by in_enabled_scope), and next-state eager
/// bindings. Part of #3025: OP_RESULT_CACHE removed (zero insertions).
///
/// Preserves (unlike clear_run_reset_impl):
/// - LITERAL_CACHE, module_ref_caches, TLC registers
/// - ALL ZERO_ARG_OP_CACHE entries (dep validation self-invalidates during ENABLED)
/// - ALL NARY_OP_CACHE entries (dep validation self-invalidates during ENABLED)
/// - All LET caches (CONST_LET, NON_CONST_LET_SET, PARAM_LET_*)
#[inline]
fn clear_enabled_scope_impl() {
    clear_state_boundary_core_impl();
    // Part of #3109: Do NOT call retain_only_zero_arg_constant_entries() or
    // retain_only_nary_constant_entries(). Non-constant entries self-invalidate
    // during ENABLED (state_env=None → op_cache_entry_valid returns false) and
    // become valid again after ENABLED exit (state_env restored, same Arc).
    // Evicting them forced re-evaluation of operators like Nbrs(n) on every
    // ENABLED check — O(states × operators) wasted work.
}

#[inline]
fn clear_run_reset_impl() {
    // Full clear of all evaluation caches — this is the strongest clear level
    // (used by phase boundary, run reset, test reset). Unlike clear_enabled_scope_impl()
    // (which retains constants per #3109), run reset needs a complete wipe.
    // Part of #3100: Clear both state and persistent partitions.
    clear_state_boundary_core_impl();
    clear_zero_arg_all_partitions();
    clear_nary_all_partitions();
    // Part of #3962: Single TLS access to clear all PerRun fields in SMALL_CACHES.
    // Previously 7 separate thread_local accesses.
    SMALL_CACHES.with(|sc| {
        let mut sc = sc.borrow_mut();
        sc.const_let_cache.clear();
        sc.non_const_let_set.clear();
        sc.param_let_deps.clear();
        sc.param_let_cache.clear();
        sc.raw_subst_scope_cache.clear();
        // BUG FIX #359/#360: Clear literal cache to prevent span collisions.
        sc.literal_cache.clear();
        // Part of #3465: Clear persistent INSTANCE taint set on run reset.
        sc.thunk_taint_set.clear();
    });
    // Fix #2364: Clear module reference scope caches for test isolation.
    crate::helpers::clear_module_ref_caches();
    // Clear operator/closure param-name caches so reused operator pointers or
    // deterministic closure ids cannot replay stale bindings across resets.
    crate::helpers::clear_param_name_caches();
    // Part of #1331: Clear TLC registers (TLCSet/TLCGet thread-local storage).
    crate::eval_debug::clear_tlc_registers();
    // Clear intern tables: cross-type equality (Func == Tuple for empty values)
    // causes {<<>>} to silently replace {Func(empty)}, failing as_func() asserts.
    crate::value::clear_set_intern_table();
    crate::value::clear_int_func_intern_table();
    crate::value::clear_tlc_norm_cache();
    super::quantifier_hoist::clear_quantifier_hoist_cache(); // Part of #3128
    crate::eval_ctx_ops::clear_action_ctx_cache(); // Part of #3364
    crate::tir::reset_current_tir_program(); // Part of #3402: defense-in-depth
                                             // Note: clear_diagnostic_counters() is NOT called here — bytecode VM stats
                                             // must survive liveness-phase cache resets within a single model checking run.
                                             // Stats are cleared by TestReset (test isolation) and reset_global_state().
    crate::helpers::clear_fold_cache(); // Fold result memoization for recursive operators
    crate::eval_cache_lifecycle::reset_state_generation_counters(); // Fix #3447: reset gen counters
    crate::eval_control_eq::clear_enabled_result_cache(); // #3387
}

/// Cache lifecycle events consumed by the lifecycle manager.
///
/// Part of #2413 U3: All cache lifecycle transitions route through `on_cache_event`.
/// External callers use thin wrappers (`clear_for_phase_boundary`, etc.) that dispatch
/// to the appropriate event.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CacheEvent {
    /// Top-level eval entry lifecycle dispatch from `eval_entry()`.
    EvalEntry {
        state_ptr: usize,
        next_state_ptr: usize,
        state_changed: bool,
        next_state_changed: bool,
    },
    /// Top-level eval exit lifecycle dispatch from `eval_entry()`.
    EvalExit,
    /// Phase boundary (e.g., safety → liveness). Clears all state and run caches.
    PhaseBoundary,
    /// Run reset between independent checker runs. Clears all state and run caches.
    RunReset,
    /// Strongest reset used by tests and global teardown.
    TestReset,
}

/// Unified lifecycle manager for evaluator caches.
///
/// Part of #2413 U3: Single dispatch point for all cache lifecycle events.
/// Public wrappers (`clear_for_phase_boundary`, etc.) route through this function.
pub(crate) fn on_cache_event(event: CacheEvent) {
    match event {
        CacheEvent::EvalEntry {
            state_ptr,
            next_state_ptr,
            state_changed,
            next_state_changed,
        } => {
            // Track pointers in the event payload for diagnostics and future tracker migration.
            let _ = (state_ptr, next_state_ptr);
            if state_changed {
                // Part of #2413 U3: PerState caches — all invalidated when state changes.
                // Part of #3100: Clear state partitions only (persistent entries survive).
                clear_zero_arg_state_partition();
                clear_nary_state_partition();
                clear_subst_cache();
                // Part of #3025: OP_RESULT_CACHE clear removed — zero insertions.
                // Fix #1498: Thunk results may depend on state.
                SMALL_CACHES.with(|sc| sc.borrow_mut().thunk_dep_cache.clear());
                crate::helpers::clear_eager_bindings_cache();
                // Part of #3805: Reset INSTANCE scope boundary dedup so the next
                // eval_module_ref call triggers a fresh clear. Without this, ABA
                // (allocator address reuse) could cause the dedup to skip clearing
                // when a new logical state reuses the same state_env pointer.
                LIFECYCLE_STATE.with(|ls| ls.last_scope_boundary_gen.set(u64::MAX));
            } else if next_state_changed {
                // Fix #2364: Selective eviction — retain entries with is_next_state=false.
                // These only depend on state_env (unchanged). Entries with is_next_state=true
                // depend on next_state_env (changed) and must be evicted.
                //
                // For grouped liveness transitions sharing the same from_state, this
                // preserves INSTANCE chain substitutions across successor iterations,
                // reducing SUBST_CACHE rebuilds from N_transitions to N_from_states.
                evict_next_state_subst_entries();
                // Fix #2364: Selective EAGER_BINDINGS_CACHE eviction — retain entries
                // with is_next_mode=false. Their keys use next_state_ptr=0 and their
                // values only depend on current state (unchanged). Entries with
                // is_next_mode=true depend on next_state and must be evicted.
                crate::helpers::evict_next_state_eager_bindings();
            }
        }
        CacheEvent::EvalExit => {
            // Part of #3099/#3962: Only trim periodically instead of every eval exit.
            // Uses consolidated LIFECYCLE_STATE for single TLS access.
            let count = LIFECYCLE_STATE.with(|ls| {
                let v = ls.eval_exit_count.get().wrapping_add(1);
                ls.eval_exit_count.set(v);
                v
            });
            if count % TRIM_INTERVAL == 0 {
                trim_eval_entry_caches();
            }
        }
        CacheEvent::PhaseBoundary => {
            clear_run_reset_impl();
            // Reset so the next EvalExit after a phase boundary triggers trim.
            // Also reset scope boundary dedup gen so the next INSTANCE ref clears.
            LIFECYCLE_STATE.with(|ls| {
                ls.eval_exit_count.set(TRIM_INTERVAL - 1);
                ls.last_scope_boundary_gen.set(u64::MAX);
            });
        }
        CacheEvent::RunReset => {
            clear_run_reset_impl();
            LIFECYCLE_STATE.with(|ls| {
                ls.eval_exit_count.set(TRIM_INTERVAL - 1);
                ls.last_scope_boundary_gen.set(u64::MAX);
            });
        }
        CacheEvent::TestReset => {
            clear_run_reset_impl();
            clear_diagnostic_counters();
            LIFECYCLE_STATE.with(|ls| {
                ls.eval_exit_count.set(TRIM_INTERVAL - 1);
                ls.last_scope_boundary_gen.set(u64::MAX);
            });
        }
    }
}

// === Cache lifecycle boundary matrix ===
//
// | Boundary              | Function                       | Behavior                                     |
// |-----------------------|--------------------------------|----------------------------------------------|
// | State transition      | clear_for_state_boundary()     | Clears per-state data, retains constants      |
// | Eval-scope switch     | clear_for_eval_scope_boundary()| Clears state + scope-sensitive LET caches     |
// | Phase boundary        | clear_for_phase_boundary()     | Full reset at safety/liveness boundary         |
// | Run reset             | clear_for_run_reset()          | Full reset between independent runs            |
// | Test reset            | clear_for_test_reset()         | Strongest reset for tests/global teardown      |
// | ENABLED scope (RAII)  | enter_enabled_scope()          | Scope guard, not a one-shot clear              |

/// Clear caches that are invalid across state transitions.
pub fn clear_for_state_boundary() {
    clear_state_boundary_impl();
}

/// Lightweight variant of `clear_for_eval_scope_boundary()` for repeated
/// INSTANCE body evaluation (`eval_module_ref`) within the same state.
///
/// MCNanoMedium (and similar INSTANCE-heavy specs) evaluate dozens of `N!Op`
/// references per state, each calling `clear_for_eval_scope_boundary()`. The
/// expensive operation is clearing zero_arg/nary STATE partitions, which forces
/// re-evaluation of every state-dependent operator. For repeated `eval_module_ref`
/// calls within the same state, these scope_id-keyed cache entries ARE valid
/// (same scope, same state) and clearing them is wasteful.
///
/// This function performs the full clear on the first call per-state (identified
/// by `state_env_id`), then on subsequent calls within the same state preserves
/// zero_arg/nary state partitions while clearing per-evaluation volatile caches
/// (SUBST_CACHE, thunk deps, instance lazy cache, CHOOSE caches, eager bindings).
///
/// Fix #4170: The edb62fe75 no-op path was UNSOUND — different INSTANCE modules
/// within the same state have different substitution bindings, so SUBST_CACHE
/// entries from one INSTANCE scope can return wrong results for another.
///
/// Part of #3805: MCNanoMedium 174s->95s (1.8x) by preserving zero_arg/nary
/// state partition entries across INSTANCE-ref calls within the same state.
#[inline]
pub fn clear_for_eval_scope_boundary_if_needed(state_env_id: usize) {
    let same_state = LIFECYCLE_STATE.with(|ls| {
        let last = ls.last_scope_boundary_gen.get();
        let id = state_env_id as u64;
        if last == id {
            true
        } else {
            ls.last_scope_boundary_gen.set(id);
            false
        }
    });
    if same_state {
        // Same state as last clear: lightweight scope reset. Preserves zero_arg/nary
        // state partitions (scope_id-keyed, stable within same state) but clears
        // per-evaluation volatile caches that may leak across INSTANCE scopes.
        //
        // Fix #4170: The no-op path introduced in edb62fe75 caused VoteProof false
        // positives because SUBST_CACHE, thunk_dep_cache, instance_lazy_cache,
        // CHOOSE caches, and eager_bindings_cache CAN leak between different
        // INSTANCE scopes within the same state. The "naturally keyed" argument
        // was WRONG — different INSTANCE modules can evaluate the same name_id
        // with different substitution bindings.
        //
        // PRESERVED (same state → entries are valid):
        // - zero_arg/nary state partitions: scope_id-keyed, stable
        // - module_ref_caches: preserves Arc stability for recursive scope_ids
        // - quantifier_hoist: subexpressions unchanged within same state
        // - LET caches: keyed by span, no cross-operator collision
        //
        // CLEARED (per-evaluation volatile state):
        // - SUBST_CACHE: different INSTANCE scopes have different substitution bindings
        // - thunk_dep_cache: dep tracking state is per-evaluation
        // - instance_lazy_cache: forced lazy bindings may be re-entered from new scope
        // - choose/choose_deep: CHOOSE results need fresh eval context per scope
        // - eager_bindings (next-state): successor-specific bindings
        // Part of #3805: Preserve SUBST_CACHE on same-state path. SUBST_CACHE
        // is keyed by (is_next_state, name_id, shared_id, local_ops_id,
        // instance_subs_id, chained_ref_eval). Different INSTANCE scopes produce
        // different instance_subs_id values via #3099 content-based fingerprints,
        // so entries cannot collide across INSTANCE scopes. Preserving these
        // entries avoids re-evaluating INSTANCE substitution chains (e.g.,
        // MCNanoMedium's 3-level EWD998ChanID chain) on every N!Op call.
        //
        // Still clear other volatile caches that lack full scope keying.
        // SUBST_CACHE guard is RAII-managed and must not be cleared mid-eval.
        SMALL_CACHES.with(|sc| {
            let mut sc = sc.borrow_mut();
            sc.thunk_dep_cache.clear();
            sc.instance_lazy_cache.clear();
            sc.choose_cache.clear();
            sc.choose_deep_cache.clear();
        });
        crate::helpers::evict_next_state_eager_bindings();
        crate::helpers::clear_eager_bindings_cache();
    } else {
        // Different state: full clear including zero_arg/nary state partitions.
        clear_for_eval_scope_boundary();
    }
}

/// Clear evaluation caches at scope boundaries (e.g., INSTANCE property evaluation).
///
/// Clears all evaluation caches including "constant" entries in ZERO_ARG_OP_CACHE
/// and NARY_OP_CACHE. Preserves LITERAL_CACHE (parsed values), the structural
/// module-ref caches (CHAINED_REF_CACHE / MODULE_REF_SCOPE_CACHE), and TLC
/// registers (user-visible state). Also clears the PerState eager bindings cache:
/// INSTANCE substitution RHS values are state-dependent even in Current mode.
///
/// This is the correct clearing level when switching evaluation context (module scope,
/// substitution context) within a single state — stronger than `clear_for_state_boundary()`
/// (which retains constant entries that may still alias across scopes) but lighter than
/// `clear_for_run_reset()` (which also clears literals, module-ref caches, and intern tables).
///
/// Part of #3120: Uses the semantic `clear_for_*` boundary vocabulary.
pub fn clear_for_eval_scope_boundary() {
    clear_state_boundary_core_impl();
    // Part of #3391: Successor invariant evaluation can switch to a logically new
    // state even when LAST_STATE_PTR lazy detection misses allocator address reuse.
    // In that case, Current-mode eager substitution bindings are stale too, not just
    // next-state ones. Mirror EvalEntry(state_changed=true) by fully clearing the
    // PerState EAGER_BINDINGS_CACHE while preserving the structural module-ref caches.
    crate::helpers::clear_eager_bindings_cache();
    // Part of #3805: Clear only the STATE partitions — persistent entries survive.
    //
    // The #3447 comment originally justified clearing BOTH partitions because
    // INSTANCE-scoped operators could appear persistent (empty deps) when their
    // state reads flow through lazy INSTANCE substitution bindings. However,
    // the `instance_lazy_read` taint mechanism (also #3447) now properly catches
    // these operators: `force_lazy_binding()` in eval_state_var_lookup.rs checks
    // whether forced deps have state/next/local dependencies and sets
    // `deps.instance_lazy_read = true` if so. `deps_are_persistent()` rejects
    // entries with this taint, routing them to the state partition. Persistent
    // entries are genuinely constant — safe to retain across scope boundaries.
    //
    // This matches `clear_for_inline_liveness_boundary()` which already preserves
    // persistent partitions with the same safety argument (Part of #3792).
    //
    // Impact: MCNanoMedium constant operators (Hash, Key, Node, AllNodes, etc.)
    // are evaluated once and cached persistently instead of re-evaluated per-state.
    clear_zero_arg_state_partition();
    clear_nary_state_partition();
    // Part of #3447: Clear all module-ref caches (CHAINED_REF_CACHE,
    // MODULE_REF_SCOPE_CACHE, EAGER_BINDINGS_CACHE, PARAM_SUBS_CACHE).
    // MODULE_REF_SCOPE_CACHE alone is insufficient — CHAINED_REF_CACHE holds
    // pre-resolved INSTANCE chain contexts with stable Arc pointers that serve
    // as identity keys in EAGER_BINDINGS_CACHE. Stale Arc pointers from prior
    // states cause EAGER_BINDINGS_CACHE hits to return substitution bindings
    // evaluated against the wrong state.
    crate::helpers::clear_module_ref_caches();
    // Part of #3962: Single TLS access to clear scope-boundary fields in SMALL_CACHES.
    SMALL_CACHES.with(|sc| {
        let mut sc = sc.borrow_mut();
        // Part of #3447: Clear RAW_SUBST_SCOPE_CACHE — stores (Arc<Vec<Substitution>>,
        // scope_id) pairs for SubstIn expressions. Same stale-Arc-pointer risk.
        sc.raw_subst_scope_cache.clear();
        sc.const_let_cache.clear();
        sc.non_const_let_set.clear();
        sc.param_let_deps.clear();
        sc.param_let_cache.clear();
    });
    // Part of #3447: Invalidate state identity tracking to force the next eval_entry
    // call to treat incoming state as changed.
    crate::eval_cache_lifecycle::invalidate_state_identity_tracking();
    // Part of #3447: Clear quantifier hoist cache to prevent stale subexpression
    // values from leaking across state boundaries in INSTANCE-heavy specs.
    super::quantifier_hoist::clear_quantifier_hoist_cache();
    // Part of #3805: Reset scope boundary dedup counter so the next
    // eval_module_ref call performs a full clear. Without this, a full scope
    // clear from clear_for_bound_state_eval_scope() (called by checker between
    // init and invariant phases, or between state binding and eval) would not
    // reset the dedup, causing subsequent eval_module_ref calls to incorrectly
    // skip clearing when the state_env_id matches the previous (now-stale) value.
    LIFECYCLE_STATE.with(|ls| ls.last_scope_boundary_gen.set(u64::MAX));
}

/// Clear caches at inline liveness evaluation boundaries.
///
/// Like `clear_for_eval_scope_boundary()` but preserves the persistent partitions
/// of ZERO_ARG_OP_CACHE and NARY_OP_CACHE. Persistent entries have empty deps
/// (no state/next/local/tlc_level dependencies, not inconsistent, no
/// instance_lazy_read taint) — they are truly constant and their results are
/// valid regardless of which BFS state triggered the evaluation.
///
/// Part of #3792: SpanTreeRandom's `Edges` operator (which calls
/// RandomElement(SUBSET ...)) takes O(2^n) fingerprinting per evaluation.
/// Previously, `InlineEvalScope` called `clear_for_eval_scope_boundary()` which
/// wiped persistent entries after every liveness batch, forcing full
/// re-evaluation of constant operators for every BFS state. With 87K states
/// this caused a >120s timeout. Preserving persistent entries across liveness
/// boundaries reduces `Edges` from O(states × 2^n) to O(2^n) total.
///
/// Safety argument: persistent entries pass `deps_are_persistent()` which
/// rejects instance_lazy_read (the #3447 INSTANCE dep tracking concern).
/// The #3447 comment about INSTANCE-scoped operators with empty deps flowing
/// through lazy substitution bindings is already handled by the
/// `instance_lazy_read` flag — those entries are routed to the state partition,
/// not the persistent partition.
pub fn clear_for_inline_liveness_boundary() {
    clear_state_boundary_core_impl();
    crate::helpers::clear_eager_bindings_cache();
    // Clear only the STATE partitions — persistent entries survive.
    clear_zero_arg_state_partition();
    clear_nary_state_partition();
    crate::helpers::clear_module_ref_caches();
    // Part of #3962: Single TLS access for liveness boundary clears in SMALL_CACHES.
    SMALL_CACHES.with(|sc| {
        let mut sc = sc.borrow_mut();
        sc.raw_subst_scope_cache.clear();
        sc.const_let_cache.clear();
        sc.non_const_let_set.clear();
        sc.param_let_deps.clear();
        sc.param_let_cache.clear();
    });
    crate::eval_cache_lifecycle::invalidate_state_identity_tracking();
    super::quantifier_hoist::clear_quantifier_hoist_cache();
    // Part of #3805: Reset scope boundary dedup for consistency with
    // clear_for_eval_scope_boundary(). Full boundary clears must reset the
    // dedup counter so subsequent eval_module_ref calls don't skip clearing.
    LIFECYCLE_STATE.with(|ls| ls.last_scope_boundary_gen.set(u64::MAX));
}

/// Clear caches at phase boundaries (e.g., safety → liveness).
///
/// Part of #2413 U3: Routes through `on_cache_event(PhaseBoundary)`.
pub fn clear_for_phase_boundary() {
    on_cache_event(CacheEvent::PhaseBoundary);
}

/// Clear caches between independent checker runs.
///
/// Part of #2413 U3: Routes through `on_cache_event(RunReset)`.
pub fn clear_for_run_reset() {
    on_cache_event(CacheEvent::RunReset);
}

/// Clear caches for test isolation and hard resets.
///
/// Part of #2413 U3: Routes through `on_cache_event(TestReset)`.
pub fn clear_for_test_reset() {
    on_cache_event(CacheEvent::TestReset);
}

/// Returns true if currently inside ENABLED evaluation scope.
///
/// Used by cache insertion points to skip caching during ENABLED scope,
/// matching TLC's EvalControl.Enabled behavior (Tool.java:1949-1953).
/// During ENABLED, state_env is None and state variables are in env — dep
/// tracking may misclassify state-dependent results as "constant". Skipping
/// cache insertion prevents contamination of non-ENABLED evaluation.
///
/// Part of #3109: TLC never caches within ENABLED scope. LazyValue entries
/// computed in non-ENABLED context remain cached; new values computed during
/// ENABLED are simply not cached (EvalControl.semanticallyEquivalent returns
/// MAYBE for Enabled vs Clear, preventing LazyValue reuse).
#[inline]
pub fn in_enabled_scope() -> bool {
    // Part of #3962: Use consolidated LIFECYCLE_STATE.
    LIFECYCLE_STATE.with(|ls| ls.in_enabled_scope.get())
}

/// Part of #3962: Context-aware ENABLED scope check that reads from the
/// `EvalRuntimeState` shadow field instead of the `IN_ENABLED_SCOPE`
/// thread-local. The shadow is synced every 64 evals in `eval()` (same
/// cadence as `hoist_active`) and at ENABLED scope entry/exit boundaries.
///
/// Use this at cache insertion/lookup sites where `ctx` is available.
/// Falls back to the TLS version for callers without ctx.
#[inline]
pub fn in_enabled_scope_ctx(ctx: &crate::EvalCtx) -> bool {
    ctx.runtime_state.in_enabled_scope.get()
}

/// Reset evaluator diagnostics counters.
pub fn clear_diagnostic_counters() {
    crate::tir::clear_bytecode_vm_stats();
}

/// Print SUBST_CACHE statistics for #2364 diagnosis.
///
/// Hit/miss counters were removed; this now reports entry count only.
pub fn print_subst_cache_stats() {
    let _entries = SUBST_STATE.with(|s| s.borrow().cache.len());
    // Counters removed — function retained for API compatibility.
}

#[cfg(test)]
#[path = "lifecycle_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "lifecycle_enabled_scope_tests.rs"]
mod enabled_scope_tests;

#[cfg(test)]
#[path = "lifecycle_cache_clearing_tests.rs"]
mod cache_clearing_tests;

#[cfg(test)]
#[path = "lifecycle_trim_tests.rs"]
mod trim_tests;
