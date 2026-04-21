// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for module-ref cache lifecycle (#2376).
//!
//! Verifies that CHAINED_REF_CACHE, MODULE_REF_SCOPE_CACHE, and
//! EAGER_BINDINGS_CACHE are properly wired into the unified cache
//! lifecycle manager (CacheEvent dispatch).

use super::*;
use crate::cache::lifecycle::{
    clear_for_eval_scope_boundary, clear_for_test_reset, on_cache_event, CacheEvent,
};
use crate::InstanceInfo;

fn dummy_chained_ref_entry() -> ChainedRefCacheEntry {
    ChainedRefCacheEntry {
        instance_info: InstanceInfo {
            module_name: "TestModule".to_string(),
            substitutions: Vec::new(),
        },
        merged_local_ops: Arc::new(OpEnv::default()),
        instance_subs_arc: Arc::new(Vec::new()),
    }
}

fn dummy_chained_ref_key(i: u64) -> ChainedRefCacheKey {
    ChainedRefCacheKey {
        shared_id: i,
        local_ops_id: 0,
        instance_subs_id: 0,
        chain_key: format!("chain_{i}"),
    }
}

/// Part of #2376: Verify CHAINED_REF_CACHE is cleared on TestReset.
#[test]
fn test_chained_ref_cache_cleared_on_test_reset() {
    clear_for_test_reset();
    MODULE_REF_CACHES.with(|c| {
        c.borrow_mut()
            .chained_ref
            .insert(dummy_chained_ref_key(1), dummy_chained_ref_entry());
    });
    assert_eq!(MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len()), 1);
    on_cache_event(CacheEvent::TestReset);
    assert_eq!(
        MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len()),
        0,
        "CHAINED_REF_CACHE must be cleared on TestReset"
    );
}

/// Part of #2376: Verify CHAINED_REF_CACHE is cleared on RunReset.
#[test]
fn test_chained_ref_cache_cleared_on_run_reset() {
    clear_for_test_reset();
    MODULE_REF_CACHES.with(|c| {
        c.borrow_mut()
            .chained_ref
            .insert(dummy_chained_ref_key(1), dummy_chained_ref_entry());
    });
    assert_eq!(MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len()), 1);
    on_cache_event(CacheEvent::RunReset);
    assert_eq!(
        MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len()),
        0,
        "CHAINED_REF_CACHE must be cleared on RunReset"
    );
}

/// Part of #2376: Verify CHAINED_REF_CACHE is cleared on PhaseBoundary.
#[test]
fn test_chained_ref_cache_cleared_on_phase_boundary() {
    clear_for_test_reset();
    MODULE_REF_CACHES.with(|c| {
        c.borrow_mut()
            .chained_ref
            .insert(dummy_chained_ref_key(1), dummy_chained_ref_entry());
    });
    assert_eq!(MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len()), 1);
    on_cache_event(CacheEvent::PhaseBoundary);
    assert_eq!(
        MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len()),
        0,
        "CHAINED_REF_CACHE must be cleared on PhaseBoundary"
    );
}

/// Part of #2376: Verify CHAINED_REF_CACHE survives EvalEntry (PerRun lifecycle).
#[test]
fn test_chained_ref_cache_survives_eval_entry() {
    clear_for_test_reset();
    MODULE_REF_CACHES.with(|c| {
        c.borrow_mut()
            .chained_ref
            .insert(dummy_chained_ref_key(1), dummy_chained_ref_entry());
    });
    assert_eq!(MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len()), 1);
    // State change should NOT clear CHAINED_REF_CACHE (it is PerRun, not PerState).
    on_cache_event(CacheEvent::EvalEntry {
        state_ptr: 100,
        next_state_ptr: 200,
        state_changed: true,
        next_state_changed: true,
    });
    assert_eq!(
        MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len()),
        1,
        "CHAINED_REF_CACHE is PerRun and must survive state transitions"
    );
}

/// Part of #2376: Verify CHAINED_REF_CACHE cliff-clears when above soft cap on EvalExit.
#[test]
fn test_chained_ref_cache_soft_cap_on_eval_exit() {
    clear_for_test_reset();
    const SOFT_CAP: usize = 10_000;
    MODULE_REF_CACHES.with(|c| {
        let mut caches = c.borrow_mut();
        for i in 0..(SOFT_CAP + 100) {
            caches
                .chained_ref
                .insert(dummy_chained_ref_key(i as u64), dummy_chained_ref_entry());
        }
    });
    let before = MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len());
    assert!(
        before > SOFT_CAP,
        "precondition: cache should exceed soft cap, got {before}"
    );
    on_cache_event(CacheEvent::EvalExit);
    let after = MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len());
    assert_eq!(
        after, 0,
        "CHAINED_REF_CACHE should cliff-clear on EvalExit when above soft cap"
    );
}

/// Part of #2376: Verify CHAINED_REF_CACHE is NOT cleared by EvalExit when below soft cap.
#[test]
fn test_chained_ref_cache_below_soft_cap_survives_eval_exit() {
    clear_for_test_reset();
    MODULE_REF_CACHES.with(|c| {
        let mut caches = c.borrow_mut();
        for i in 0..5u64 {
            caches
                .chained_ref
                .insert(dummy_chained_ref_key(i), dummy_chained_ref_entry());
        }
    });
    assert_eq!(MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len()), 5);
    on_cache_event(CacheEvent::EvalExit);
    assert_eq!(
        MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len()),
        5,
        "CHAINED_REF_CACHE should survive EvalExit when below soft cap"
    );
}

/// Part of #2376: Verify MODULE_REF_SCOPE_CACHE lifecycle parallels CHAINED_REF_CACHE.
#[test]
fn test_module_ref_scope_cache_cleared_on_run_reset() {
    clear_for_test_reset();
    MODULE_REF_CACHES.with(|c| {
        c.borrow_mut().module_ref_scope.insert(
            ModuleRefScopeKey {
                shared_id: 1,
                instance_name_id: tla_core::name_intern::intern_name("M"),
                outer_subs_id: 0,
                outer_local_ops_id: 0,
            },
            ModuleRefScopeEntry {
                effective_subs_arc: Arc::new(Vec::new()),
                local_ops_arc: Arc::new(OpEnv::default()),
            },
        );
    });
    assert_eq!(MODULE_REF_CACHES.with(|c| c.borrow().module_ref_scope.len()), 1);
    on_cache_event(CacheEvent::RunReset);
    assert_eq!(
        MODULE_REF_CACHES.with(|c| c.borrow().module_ref_scope.len()),
        0,
        "MODULE_REF_SCOPE_CACHE must be cleared on RunReset"
    );
}

/// Part of #2376: Verify EAGER_BINDINGS_CACHE is cleared on RunReset.
#[test]
fn test_eager_bindings_cache_cleared_on_run_reset() {
    clear_for_test_reset();
    MODULE_REF_CACHES.with(|c| {
        c.borrow_mut().eager_bindings.insert(
            EagerBindingsKey {
                subs_ptr: 1,
                local_ops_ptr: 2,
                state_gen: 3,
                next_state_gen: 0,

                is_next_mode: false,
                param_args_hash: 0,
            },
            Arc::new(Vec::new()),
        );
    });
    assert_eq!(MODULE_REF_CACHES.with(|c| c.borrow().eager_bindings.len()), 1);
    on_cache_event(CacheEvent::RunReset);
    assert_eq!(
        MODULE_REF_CACHES.with(|c| c.borrow().eager_bindings.len()),
        0,
        "EAGER_BINDINGS_CACHE must be cleared on RunReset"
    );
}

/// Regression #3391: `clear_for_eval_scope_boundary()` must clear current-mode
/// eager bindings too. INSTANCE substitution RHS values are PerState, so when
/// successor invariant evaluation crosses into a logically new state without an
/// `EvalEntry(state_changed=true)` event, retaining current-mode eager bindings
/// reuses stale substitution results across successors.
#[test]
fn test_eager_bindings_cache_cleared_on_eval_scope_boundary() {
    clear_for_test_reset();
    MODULE_REF_CACHES.with(|c| {
        c.borrow_mut().eager_bindings.insert(
            EagerBindingsKey {
                subs_ptr: 1,
                local_ops_ptr: 2,
                state_gen: 3,
                next_state_gen: 0,
                is_next_mode: false,
                param_args_hash: 0,
            },
            Arc::new(Vec::new()),
        );
    });
    assert_eq!(MODULE_REF_CACHES.with(|c| c.borrow().eager_bindings.len()), 1);

    clear_for_eval_scope_boundary();

    assert_eq!(
        MODULE_REF_CACHES.with(|c| c.borrow().eager_bindings.len()),
        0,
        "#3391: clear_for_eval_scope_boundary must clear EAGER_BINDINGS_CACHE"
    );
}

/// Regression #3447: `clear_for_eval_scope_boundary()` must clear the full
/// module-ref cache family used to derive eager-binding identity keys.
/// `CHAINED_REF_CACHE` and `MODULE_REF_SCOPE_CACHE` both retain stable Arc
/// pointers across evaluations, so both must be flushed at eval-scope
/// boundaries alongside the eager-binding cache.
#[test]
fn test_eval_scope_boundary_clears_module_ref_caches() {
    clear_for_test_reset();
    MODULE_REF_CACHES.with(|c| {
        c.borrow_mut()
            .chained_ref
            .insert(dummy_chained_ref_key(1), dummy_chained_ref_entry());
    });
    MODULE_REF_CACHES.with(|c| {
        c.borrow_mut().module_ref_scope.insert(
            ModuleRefScopeKey {
                shared_id: 1,
                instance_name_id: tla_core::name_intern::intern_name("ScopeOnly"),
                outer_subs_id: 0,
                outer_local_ops_id: 0,
            },
            ModuleRefScopeEntry {
                effective_subs_arc: Arc::new(Vec::new()),
                local_ops_arc: Arc::new(OpEnv::default()),
            },
        );
    });

    assert_eq!(MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len()), 1);
    assert_eq!(MODULE_REF_CACHES.with(|c| c.borrow().module_ref_scope.len()), 1);

    clear_for_eval_scope_boundary();

    assert_eq!(
        MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len()),
        0,
        "#3447: clear_for_eval_scope_boundary must clear CHAINED_REF_CACHE"
    );
    assert_eq!(
        MODULE_REF_CACHES.with(|c| c.borrow().module_ref_scope.len()),
        0,
        "#3447: clear_for_eval_scope_boundary must clear MODULE_REF_SCOPE_CACHE"
    );
}

/// Part of #2376: Verify clear_module_ref_caches clears all three module-ref caches.
#[test]
fn test_clear_module_ref_caches_clears_all() {
    clear_for_test_reset();
    MODULE_REF_CACHES.with(|c| {
        c.borrow_mut()
            .chained_ref
            .insert(dummy_chained_ref_key(1), dummy_chained_ref_entry());
    });
    MODULE_REF_CACHES.with(|c| {
        c.borrow_mut().module_ref_scope.insert(
            ModuleRefScopeKey {
                shared_id: 1,
                instance_name_id: tla_core::name_intern::intern_name("N"),
                outer_subs_id: 0,
                outer_local_ops_id: 0,
            },
            ModuleRefScopeEntry {
                effective_subs_arc: Arc::new(Vec::new()),
                local_ops_arc: Arc::new(OpEnv::default()),
            },
        );
    });
    MODULE_REF_CACHES.with(|c| {
        c.borrow_mut().eager_bindings.insert(
            EagerBindingsKey {
                subs_ptr: 1,
                local_ops_ptr: 2,
                state_gen: 3,
                next_state_gen: 0,

                is_next_mode: false,
                param_args_hash: 0,
            },
            Arc::new(Vec::new()),
        );
    });
    assert_eq!(MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len()), 1);
    assert_eq!(MODULE_REF_CACHES.with(|c| c.borrow().module_ref_scope.len()), 1);
    assert_eq!(MODULE_REF_CACHES.with(|c| c.borrow().eager_bindings.len()), 1);

    clear_module_ref_caches();

    assert_eq!(
        MODULE_REF_CACHES.with(|c| c.borrow().chained_ref.len()),
        0,
        "clear_module_ref_caches must clear CHAINED_REF_CACHE"
    );
    assert_eq!(
        MODULE_REF_CACHES.with(|c| c.borrow().module_ref_scope.len()),
        0,
        "clear_module_ref_caches must clear MODULE_REF_SCOPE_CACHE"
    );
    assert_eq!(
        MODULE_REF_CACHES.with(|c| c.borrow().eager_bindings.len()),
        0,
        "clear_module_ref_caches must clear EAGER_BINDINGS_CACHE"
    );
}
