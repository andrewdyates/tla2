// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Evaluator cache subsystem.
//!
//! Contains 5 independent cache systems, dependency tracking infrastructure,
//! RAII guards, and lifecycle orchestration. Decomposed from eval_cache.rs as
//! part of #2744.
//!
//! Module structure:
//! - dep_tracking: OpEvalDeps, OpDepFrame, guards, eval_with_dep_tracking
//! - subst_cache: SUBST_CACHE, SubstCacheGuard, SubstGuardEntry
//! - op_result_cache: CachedOpResult, validation (Part of #3025: OP_RESULT_CACHE removed)
//! - zero_arg_cache: ZERO_ARG_CACHES (Part of #4053: consolidated from 2 TLS into 1)
//! - small_caches: LITERAL_CACHE, THUNK_DEP_CACHE
//! - lifecycle: CacheEvent, on_cache_event, clear_* wrappers

pub(crate) mod dep_tracking;
pub(crate) mod lifecycle;
pub(crate) mod lifecycle_trim;
pub(crate) mod mark_hoistable;
pub(crate) mod mark_hoistable_tir;
pub(crate) mod mark_hoistable_walkers;
pub(crate) mod op_result_cache;
pub(crate) mod quantifier_hoist;
pub(crate) mod scope_ids;
pub(crate) mod small_caches;
pub(crate) mod subst_cache;
pub(crate) mod zero_arg_cache;

// === pub(crate) re-exports for sibling modules (eval_prime.rs, core.rs, etc.) ===
// These were originally pub(super) in eval_cache.rs, making them visible to lib.rs.
// In the new structure, pub(crate) re-exports from mod.rs achieve the same visibility
// via `use self::cache::*;` in lib.rs.

// dep_tracking
#[cfg(test)]
pub(crate) use dep_tracking::VarDepMap;
pub(crate) use dep_tracking::{
    current_state_lookup_mode, is_dep_tracking_active, mark_instance_lazy_read,
    propagate_cached_deps, record_local_read, record_next_read, record_state_read,
    EvalRuntimeState, OpEvalDeps, StateLookupMode,
};

// subst_cache — Part of #3805: SUBST_CACHE + SUBST_EVAL_GUARD consolidated into SUBST_STATE
pub(crate) use subst_cache::{
    is_subst_guarded, subst_cache_key, SubstCacheEntry, SubstGuardEntry, SUBST_STATE,
};

// op_result_cache
// Part of #3000: OpResultCacheKey and OP_RESULT_CACHE removed from re-exports.
// OP_RESULT_CACHE has zero insertion points after Phase 1 (unified lazy args).
// Lifecycle code imports directly from op_result_cache module. CachedOpResult and
// op_cache_entry_valid are still used by ZERO_ARG_OP_CACHE and NARY_OP_CACHE.
pub(crate) use op_result_cache::{op_cache_entry_valid, CachedOpResult};
// Part of #2991, #3070, #3100: N-ary operator result cache re-exports.
pub(crate) use op_result_cache::{
    hash_args, nary_insert, nary_lookup, NaryOpCacheEntry, NaryOpCacheKey,
};

// zero_arg_cache
// Part of #3100: Partitioned into state + persistent caches.
pub(crate) use zero_arg_cache::{zero_arg_insert, zero_arg_lookup};

// small_caches — Part of #3962: consolidated into SMALL_CACHES struct
pub(crate) use small_caches::{
    choose_cache_lookup, choose_cache_store, choose_deep_cache_lookup, choose_deep_cache_store,
    hash_bindings_for_choose, hash_value_for_choose, propagate_thunk_deps, raw_subst_scope_key,
    store_thunk_deps, thunk_has_instance_lazy_taint, ChooseDeepKey, SMALL_CACHES,
};

// quantifier_hoist + mark_hoistable
pub(crate) use mark_hoistable::mark_hoistable;
pub(crate) use mark_hoistable_tir::{
    enter_tir_hoist_scope, enter_tir_hoist_scope_single, is_tir_hoist_cacheable,
};
pub(crate) use quantifier_hoist::{
    advance_hoist_state_generation, advance_hoist_state_generation_ctx,
    bump_hoist_state_generation, bump_hoist_state_generation_ctx, enter_quantifier_hoist_scope,
    is_hoist_active, quantifier_hoist_lookup, quantifier_hoist_lookup_ctx, quantifier_hoist_store,
    quantifier_hoist_store_ctx, tir_hoist_lookup, tir_hoist_lookup_ctx, tir_hoist_store,
    tir_hoist_store_ctx, HoistGenerationGuard, QuantifierHoistScopeGuard,
};
#[cfg(debug_assertions)]
pub(crate) use quantifier_hoist::{suppress_hoist_lookup, HOIST_VERIFY};

// === pub(crate) re-exports for guards and lifecycle ===

pub(crate) use dep_tracking::{
    eval_with_dep_tracking, eval_with_dep_tracking_unpropagated, OpDepGuard, StateLookupModeGuard,
};
pub(crate) use lifecycle::{on_cache_event, CacheEvent};
pub(crate) use lifecycle_trim::trim_eval_entry_caches;
pub(crate) use subst_cache::SubstCacheGuard;

// === pub re-exports (external API surface) ===

pub use dep_tracking::try_eval_const_level;
pub use lifecycle::{
    clear_diagnostic_counters, clear_for_eval_scope_boundary, clear_for_inline_liveness_boundary,
    clear_for_phase_boundary, clear_for_run_reset, clear_for_state_boundary, clear_for_test_reset,
    enter_enabled_scope, enter_enabled_scope_with_ctx, print_subst_cache_stats, EnabledScopeGuard,
};
// Part of #3025: op_result_cache_clear/op_result_cache_len removed — cache was dead.
pub use subst_cache::{clear_subst_cache, evict_next_state_subst_entries};

// === #[cfg(test)] re-exports ===

#[cfg(test)]
pub(crate) use quantifier_hoist::clear_quantifier_hoist_cache;

#[cfg(test)]
pub(crate) use subst_cache::{clear_subst_guard, SubstCacheKey};
#[cfg(test)]
pub(crate) use zero_arg_cache::{zero_arg_op_cache_clear, zero_arg_op_cache_entry_count};
