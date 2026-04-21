// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for cache lifecycle orchestration.
//!
//! Part of #2744 decomposition from eval_cache.rs.

use super::{clear_for_test_reset, on_cache_event, CacheEvent};
use crate::cache::dep_tracking::OpEvalDeps;
use crate::cache::small_caches::SMALL_CACHES;
use crate::cache::subst_cache::{SubstCacheEntry, SubstCacheKey, SUBST_STATE};
use crate::var_index::VarIndex;
use tla_core::name_intern::intern_name;
use tla_value::Value;

#[test]
fn test_op_eval_deps_record_deduplicates_and_detects_conflicts() {
    let mut deps = OpEvalDeps::default();
    let local_id = intern_name("local");
    let state_idx = VarIndex::new(0);
    let next_idx = VarIndex::new(1);

    deps.record_local(local_id, &Value::int(1));
    deps.record_local(local_id, &Value::int(1));
    assert_eq!(deps.local.len(), 1);
    assert!(!deps.inconsistent);

    deps.record_state(state_idx, &Value::int(10));
    deps.record_state(state_idx, &Value::int(10));
    assert_eq!(deps.state.len(), 1);
    assert!(!deps.inconsistent);

    deps.record_next(next_idx, &Value::int(20));
    deps.record_next(next_idx, &Value::int(20));
    assert_eq!(deps.next.len(), 1);
    assert!(!deps.inconsistent);

    deps.record_local(local_id, &Value::int(2));
    assert!(deps.inconsistent);
}

#[test]
fn test_op_eval_deps_merge_from_preserves_entries_and_conflict_detection() {
    let local_id = intern_name("local");
    let state_idx = VarIndex::new(0);
    let next_idx = VarIndex::new(1);

    let mut base = OpEvalDeps::default();
    base.record_local(local_id, &Value::int(1));
    base.record_state(state_idx, &Value::int(10));

    let mut compatible = OpEvalDeps::default();
    compatible.record_local(local_id, &Value::int(1));
    compatible.record_next(next_idx, &Value::int(20));
    base.merge_from(&compatible);

    assert_eq!(base.local.len(), 1);
    assert_eq!(base.state.len(), 1);
    assert_eq!(base.next.len(), 1);
    assert!(!base.inconsistent);

    let mut conflicting = OpEvalDeps::default();
    conflicting.record_state(state_idx, &Value::int(999));
    base.merge_from(&conflicting);
    assert!(base.inconsistent);
}

#[test]
fn test_cache_event_eval_entry_only_clears_subst_cache_on_epoch_change() {
    clear_for_test_reset();
    let key = SubstCacheKey {
        is_next_state: false,
        name_id: intern_name("x"),
        shared_id: 1,
        local_ops_id: 0,
        instance_subs_id: 0,
        chained_ref_eval: false,
    };
    SUBST_STATE.with(|s| {
        s.borrow_mut().cache.insert(
            key,
            SubstCacheEntry {
                value: Value::int(1),
                deps: OpEvalDeps::default(),
            },
        );
    });

    on_cache_event(CacheEvent::EvalEntry {
        state_ptr: 10,
        next_state_ptr: 20,
        state_changed: false,
        next_state_changed: false,
    });
    let unchanged_len = SUBST_STATE.with(|s| s.borrow().cache.len());
    assert_eq!(
        unchanged_len, 1,
        "SUBST_CACHE should persist when epoch pointers are unchanged"
    );

    on_cache_event(CacheEvent::EvalEntry {
        state_ptr: 11,
        next_state_ptr: 20,
        state_changed: true,
        next_state_changed: false,
    });
    let changed_len = SUBST_STATE.with(|s| s.borrow().cache.len());
    assert_eq!(
        changed_len, 0,
        "SUBST_CACHE should clear when state_changed"
    );
}

#[test]
fn test_cache_event_selective_eviction_on_next_state_change() {
    clear_for_test_reset();
    // Insert a current-state entry (is_next_state=false).
    let current_key = SubstCacheKey {
        is_next_state: false,
        name_id: intern_name("inbox"),
        shared_id: 1,
        local_ops_id: 0,
        instance_subs_id: 0,
        chained_ref_eval: false,
    };
    // Insert a next-state entry (is_next_state=true).
    let next_key = SubstCacheKey {
        is_next_state: true,
        name_id: intern_name("inbox"),
        shared_id: 1,
        local_ops_id: 0,
        instance_subs_id: 0,
        chained_ref_eval: false,
    };
    SUBST_STATE.with(|s| {
        let mut state = s.borrow_mut();
        state.cache.insert(
            current_key,
            SubstCacheEntry {
                value: Value::int(1),
                deps: OpEvalDeps::default(),
            },
        );
        state.cache.insert(
            next_key,
            SubstCacheEntry {
                value: Value::int(2),
                deps: OpEvalDeps::default(),
            },
        );
    });
    assert_eq!(SUBST_STATE.with(|s| s.borrow().cache.len()), 2);

    // Only next_state_changed: should evict next-state entries, retain current-state.
    on_cache_event(CacheEvent::EvalEntry {
        state_ptr: 10,
        next_state_ptr: 21,
        state_changed: false,
        next_state_changed: true,
    });
    let after_next_change = SUBST_STATE.with(|s| s.borrow().cache.len());
    assert_eq!(
        after_next_change, 1,
        "Only current-state entry should survive next_state_changed"
    );
    // Verify the surviving entry is the current-state one.
    let has_current = SUBST_STATE.with(|s| s.borrow().cache.contains_key(&current_key));
    assert!(has_current, "current-state entry should be retained");
    let has_next = SUBST_STATE.with(|s| s.borrow().cache.contains_key(&next_key));
    assert!(!has_next, "next-state entry should be evicted");
}

/// Part of #2413 U3: Verify THUNK_DEP_CACHE is cleared by
/// on_cache_event(EvalEntry) when state_changed=true.
/// Part of #3025: OP_RESULT_CACHE removed (zero insertions).
#[test]
fn test_cache_event_eval_entry_clears_thunk_on_state_change() {
    clear_for_test_reset();

    // Populate THUNK_DEP_CACHE with a dummy entry (keyed by u64).
    SMALL_CACHES.with(|sc| {
        sc.borrow_mut().thunk_dep_cache.insert(42u64, OpEvalDeps::default());
    });
    assert_eq!(
        SMALL_CACHES.with(|sc| sc.borrow().thunk_dep_cache.len()),
        1,
        "THUNK_DEP_CACHE should have one entry"
    );

    // No state change — cache should survive.
    on_cache_event(CacheEvent::EvalEntry {
        state_ptr: 10,
        next_state_ptr: 20,
        state_changed: false,
        next_state_changed: false,
    });
    assert_eq!(
        SMALL_CACHES.with(|sc| sc.borrow().thunk_dep_cache.len()),
        1,
        "THUNK_DEP_CACHE should survive when state unchanged"
    );

    // State changed — should clear.
    on_cache_event(CacheEvent::EvalEntry {
        state_ptr: 11,
        next_state_ptr: 20,
        state_changed: true,
        next_state_changed: false,
    });
    assert_eq!(
        SMALL_CACHES.with(|sc| sc.borrow().thunk_dep_cache.len()),
        0,
        "THUNK_DEP_CACHE should clear on state_changed"
    );
}

/// Part of #2413 U3: Verify PhaseBoundary and RunReset events clear all caches
/// (same behavior as TestReset — all route through clear_run_reset_impl).
#[test]
fn test_cache_event_phase_boundary_and_run_reset_clear_all() {
    for event in [CacheEvent::PhaseBoundary, CacheEvent::RunReset] {
        clear_for_test_reset();

        // Populate SUBST_CACHE.
        SUBST_STATE.with(|s| {
            s.borrow_mut().cache.insert(
                SubstCacheKey {
                    is_next_state: false,
                    name_id: intern_name("x"),
                    shared_id: 1,
                    local_ops_id: 0,
                    instance_subs_id: 0,
                    chained_ref_eval: false,
                },
                SubstCacheEntry {
                    value: Value::int(1),
                    deps: OpEvalDeps::default(),
                },
            );
        });
        assert_eq!(SUBST_STATE.with(|s| s.borrow().cache.len()), 1);

        on_cache_event(event);

        assert_eq!(
            SUBST_STATE.with(|s| s.borrow().cache.len()),
            0,
            "{event:?} should clear SUBST_CACHE"
        );
    }
}
