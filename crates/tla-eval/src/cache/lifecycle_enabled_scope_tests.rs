// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for ENABLED scope guard behavior and cache retention.
//!
//! Part of #3442: extracted from lifecycle_tests.rs.

use super::clear_for_test_reset;
use crate::cache::dep_tracking::OpEvalDeps;
use crate::cache::op_result_cache::{
    CachedOpResult, NaryOpCacheEntry, NaryOpCacheKey, NARY_CACHES,
};
use crate::cache::small_caches::{LetScopeKey, SMALL_CACHES};
use crate::cache::subst_cache::{SubstCacheEntry, SubstCacheKey, SUBST_STATE};
use crate::cache::zero_arg_cache::ZERO_ARG_CACHES;
use crate::var_index::VarIndex;
use tla_core::name_intern::intern_name;
use tla_value::Value;

// === Part of #2998: EnabledScopeGuard unit tests per P1-9 finding ===

/// Part of #2998 / P1-9: `enter_enabled_scope()` returns `Some(guard)` on first call.
#[test]
fn test_enabled_scope_guard_returns_some_on_first_entry() {
    clear_for_test_reset();
    let guard = super::enter_enabled_scope();
    assert!(
        guard.is_some(),
        "first enter_enabled_scope() should return Some(guard)"
    );
    // guard drops here, resetting IN_ENABLED_SCOPE
}

/// Part of #2998 / P1-9: nested `enter_enabled_scope()` returns `None`.
#[test]
fn test_enabled_scope_guard_nested_returns_none() {
    clear_for_test_reset();
    let guard = super::enter_enabled_scope();
    assert!(guard.is_some(), "first entry should return Some");

    let nested = super::enter_enabled_scope();
    assert!(
        nested.is_none(),
        "nested enter_enabled_scope() should return None (already in scope)"
    );

    drop(guard);
}

/// Part of #2998 / P1-9: guard `Drop` resets scope flag — subsequent call returns Some.
#[test]
fn test_enabled_scope_guard_drop_resets_flag() {
    clear_for_test_reset();
    {
        let guard = super::enter_enabled_scope();
        assert!(guard.is_some());
        // guard drops at end of block
    }
    // After drop, we should be outside ENABLED scope
    let guard2 = super::enter_enabled_scope();
    assert!(
        guard2.is_some(),
        "after guard drop, enter_enabled_scope() should return Some again"
    );
    // guard2 drops here
}

/// Part of #2998 / P1-9: entering ENABLED scope clears PerState caches.
/// Part of #3025: OP_RESULT_CACHE removed (zero insertions).
#[test]
fn test_enabled_scope_guard_clears_caches_on_entry() {
    clear_for_test_reset();

    // Populate caches with dummy entries.
    SUBST_STATE.with(|s| {
        s.borrow_mut().cache.insert(
            SubstCacheKey {
                is_next_state: false,
                name_id: intern_name("enabled_entry_test"),
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
    SMALL_CACHES.with(|sc| {
        sc.borrow_mut().thunk_dep_cache.insert(99u64, OpEvalDeps::default());
    });

    assert_eq!(SUBST_STATE.with(|s| s.borrow().cache.len()), 1);
    assert_eq!(SMALL_CACHES.with(|sc| sc.borrow().thunk_dep_cache.len()), 1);

    // Enter ENABLED scope — should clear PerState caches.
    let guard = super::enter_enabled_scope();
    assert!(guard.is_some());

    assert_eq!(
        SUBST_STATE.with(|s| s.borrow().cache.len()),
        0,
        "SUBST_CACHE should be cleared on ENABLED scope entry"
    );
    assert_eq!(
        SMALL_CACHES.with(|sc| sc.borrow().thunk_dep_cache.len()),
        0,
        "THUNK_DEP_CACHE should be cleared on ENABLED scope entry"
    );
    // guard drops here
}

/// Part of #2998 / P1-9: guard drop clears PerState caches (entries from ENABLED scope).
#[test]
fn test_enabled_scope_guard_clears_caches_on_exit() {
    clear_for_test_reset();

    let guard = super::enter_enabled_scope();
    assert!(guard.is_some());

    // Populate caches while in ENABLED scope (simulating ENABLED eval).
    SUBST_STATE.with(|s| {
        s.borrow_mut().cache.insert(
            SubstCacheKey {
                is_next_state: false,
                name_id: intern_name("enabled_exit_test"),
                shared_id: 2,
                local_ops_id: 0,
                instance_subs_id: 0,
                chained_ref_eval: false,
            },
            SubstCacheEntry {
                value: Value::int(99),
                deps: OpEvalDeps::default(),
            },
        );
    });
    // Part of #3025: OP_RESULT_CACHE removed (zero insertions).

    assert_eq!(SUBST_STATE.with(|s| s.borrow().cache.len()), 1);

    // Drop guard — should clear caches to prevent ENABLED entries from leaking.
    drop(guard);

    assert_eq!(
        SUBST_STATE.with(|s| s.borrow().cache.len()),
        0,
        "SUBST_CACHE should be cleared on ENABLED scope exit"
    );
}

// === Shared helpers for ENABLED scope retention tests ===

/// Populate all constant-entry caches with dummy entries for ENABLED scope clearing tests.
/// Part of #3100: constant operator entries live in persistent partitions.
fn populate_constant_caches(suffix: &str) {
    let name_id = intern_name(suffix);
    ZERO_ARG_CACHES.with(|caches| {
        caches.borrow_mut().persistent.insert(
            (1, 0, 0, name_id, 0, false),
            vec![CachedOpResult {
                value: Value::int(42),
                deps: OpEvalDeps::default(),
            }],
        );
    });
    NARY_CACHES.with(|caches| {
        caches.borrow_mut().persistent.insert(
            NaryOpCacheKey {
                shared_id: 1,
                local_ops_id: 0,
                instance_subs_id: 0,
                op_name: name_id,
                def_loc: 0,
                is_next_state: false,
                args_hash: 0,
                param_args_hash: 0,
            },
            vec![NaryOpCacheEntry {
                args: std::sync::Arc::from(Vec::<Value>::new().into_boxed_slice()),
                result: CachedOpResult {
                    value: Value::int(99),
                    deps: OpEvalDeps::default(),
                },
            }],
        );
    });
    // Fix #3095: Use LetScopeKey instead of raw body_ptr.
    let let_key_1 = LetScopeKey {
        body_ptr: 0x1000,
        local_ops_id: 0,
        instance_subs_id: 0,
    };
    let let_key_2 = LetScopeKey {
        body_ptr: 0x2000,
        local_ops_id: 0,
        instance_subs_id: 0,
    };
    let let_key_3 = LetScopeKey {
        body_ptr: 0x3000,
        local_ops_id: 0,
        instance_subs_id: 0,
    };
    SMALL_CACHES.with(|sc| {
        let mut sc = sc.borrow_mut();
        sc.const_let_cache.insert(let_key_1, Value::int(1));
        sc.non_const_let_set.insert(let_key_2);
        sc.param_let_deps.insert(let_key_3, vec![name_id]);
        sc.param_let_cache
            .insert(let_key_3, vec![(0, vec![Value::int(1)], Value::int(2))]);
    });
}

/// Populate state-partitioned operator caches with dummy entries for ENABLED
/// scope retention tests. Part of #3109/#3100: these entries should survive
/// ENABLED entry/exit because they are self-validating and no new operator
/// cache entries are created while ENABLED is active.
fn populate_operator_state_caches(suffix: &str) {
    let name_id = intern_name(suffix);
    let mut deps = OpEvalDeps::default();
    deps.record_state(VarIndex::new(0), &Value::int(7));

    ZERO_ARG_CACHES.with(|caches| {
        caches.borrow_mut().state.insert(
            (1, 0, 0, name_id, 0, false),
            vec![CachedOpResult {
                value: Value::int(7),
                deps: deps.clone(),
            }],
        );
    });
    NARY_CACHES.with(|caches| {
        caches.borrow_mut().state.insert(
            NaryOpCacheKey {
                shared_id: 1,
                local_ops_id: 0,
                instance_subs_id: 0,
                op_name: name_id,
                def_loc: 0,
                is_next_state: false,
                args_hash: 0,
                param_args_hash: 0,
            },
            vec![NaryOpCacheEntry {
                args: std::sync::Arc::from(Vec::<Value>::new().into_boxed_slice()),
                result: CachedOpResult {
                    value: Value::int(8),
                    deps,
                },
            }],
        );
    });
}

/// Assert operator state partitions have the expected key count.
fn assert_operator_state_caches_len(expected: usize, context: &str) {
    assert_eq!(
        ZERO_ARG_CACHES.with(|c| c.borrow().state.len()),
        expected,
        "ZERO_ARG_CACHES state partition {context}"
    );
    assert_eq!(
        NARY_CACHES.with(|c| c.borrow().state.len()),
        expected,
        "NARY_CACHES state partition {context}"
    );
}

/// Assert all constant-entry caches have the expected length.
fn assert_constant_caches_len(expected: usize, context: &str) {
    assert_operator_constant_caches_len(expected, context);
    assert_let_caches_len(expected, context);
}

/// Assert operator constant caches (persistent partitions) have expected length.
/// Part of #3109/#3100: These retain proven-constant entries across ENABLED and state boundaries.
fn assert_operator_constant_caches_len(expected: usize, context: &str) {
    assert_eq!(
        ZERO_ARG_CACHES.with(|c| c.borrow().persistent.len()),
        expected,
        "ZERO_ARG_CACHES persistent partition {context}"
    );
    assert_eq!(
        NARY_CACHES.with(|c| c.borrow().persistent.len()),
        expected,
        "NARY_CACHES persistent partition {context}"
    );
}

/// Assert LET caches have expected length.
/// Part of #3109: LET caches are retained across ENABLED scope transitions.
/// Step 1 prevents new entries during ENABLED, so all entries are pre-ENABLED
/// with reliable dep tracking. Consistent with state boundary behavior.
fn assert_let_caches_len(expected: usize, context: &str) {
    SMALL_CACHES.with(|sc| {
        let sc = sc.borrow();
        assert_eq!(sc.const_let_cache.len(), expected, "CONST_LET_CACHE {context}");
        assert_eq!(sc.non_const_let_set.len(), expected, "NON_CONST_LET_SET {context}");
        assert_eq!(sc.param_let_deps.len(), expected, "PARAM_LET_DEPS {context}");
        assert_eq!(sc.param_let_cache.len(), expected, "PARAM_LET_CACHE {context}");
    });
}

// === ENABLED scope retention tests ===

/// Part of #3109: Verify that ENABLED scope entry RETAINS proven-constant entries
/// in ALL caches (operator caches AND LET caches). Pre-ENABLED entries have reliable
/// dep tracking and are safe to retain. Step 1 (skip caching during ENABLED) prevents
/// new entries with unreliable deps.
#[test]
fn test_enabled_scope_retains_constant_caches_on_entry() {
    clear_for_test_reset();
    populate_constant_caches("enabled_const_entry");
    assert_constant_caches_len(1, "should be populated before ENABLED scope entry");

    let guard = super::enter_enabled_scope();
    assert!(guard.is_some());
    // Part of #3109: Operator constant entries survive ENABLED scope entry — they
    // are genuinely constant (created in non-ENABLED context with reliable dep tracking).
    assert_operator_constant_caches_len(
        1,
        "operator constant entries must survive ENABLED scope entry",
    );
    // Part of #3109: LET caches retained across ENABLED scope (consistent with state
    // boundaries). Step 1 prevents new entries during ENABLED, so all entries are
    // pre-ENABLED with reliable dep tracking.
    assert_let_caches_len(1, "LET caches retained across ENABLED scope entry");

    drop(guard);
}

/// Part of #3109: Verify that ENABLED scope exit retains ALL constant entries
/// (operator caches AND LET caches). With Step 1 (skip caching during ENABLED),
/// no new entries are created during ENABLED scope. All pre-ENABLED entries are
/// retained because they have reliable dep tracking.
#[test]
fn test_enabled_scope_retains_constant_caches_on_exit() {
    clear_for_test_reset();
    populate_constant_caches("enabled_const_pre");
    assert_constant_caches_len(1, "should be populated before ENABLED scope");

    let guard = super::enter_enabled_scope();
    assert!(guard.is_some());
    // Pre-ENABLED constant entries survive entry.
    assert_operator_constant_caches_len(1, "operator constant entries survive ENABLED scope entry");
    assert_let_caches_len(1, "LET caches survive ENABLED scope entry");

    drop(guard);
    // Pre-ENABLED constant entries survive exit.
    assert_operator_constant_caches_len(
        1,
        "operator constant entries must survive ENABLED scope exit",
    );
    // LET caches retained after exit (consistent with state boundary behavior).
    assert_let_caches_len(1, "LET caches retained after ENABLED scope exit");
}

/// Part of #3109/#3100: ENABLED scope entry must retain operator state partitions.
/// These entries self-invalidate during ENABLED lookup because `state_env=None`,
/// but they become valid again after the same state/next arrays are restored.
#[test]
fn test_enabled_scope_retains_operator_state_caches_on_entry() {
    clear_for_test_reset();
    populate_operator_state_caches("enabled_state_entry");
    assert_operator_state_caches_len(
        1,
        "state-partition operator entries should exist before ENABLED entry",
    );

    let guard = super::enter_enabled_scope();
    assert!(guard.is_some());
    assert_operator_state_caches_len(
        1,
        "state-partition operator entries must survive ENABLED scope entry",
    );

    drop(guard);
}

/// Part of #3109/#3100: ENABLED scope exit must retain operator state partitions.
/// Clearing them on exit would force recomputation when evaluation resumes in the
/// same BFS state after the ENABLED check returns.
#[test]
fn test_enabled_scope_retains_operator_state_caches_on_exit() {
    clear_for_test_reset();
    populate_operator_state_caches("enabled_state_exit");
    assert_operator_state_caches_len(
        1,
        "state-partition operator entries should exist before ENABLED scope",
    );

    let guard = super::enter_enabled_scope();
    assert!(guard.is_some());
    assert_operator_state_caches_len(
        1,
        "state-partition operator entries should survive ENABLED scope entry",
    );

    drop(guard);
    assert_operator_state_caches_len(
        1,
        "state-partition operator entries must survive ENABLED scope exit",
    );
}

/// Part of #4027: Verify that `enter_enabled_scope_with_ctx` clears the shadow
/// `in_enabled_scope` field on `EvalRuntimeState` when the guard is dropped.
/// Before this fix, the shadow stayed stale (true) for up to 64 evals after
/// ENABLED scope exit, causing missed cache insertions at sites reading via
/// `in_enabled_scope_ctx()`.
#[test]
fn test_enabled_scope_shadow_cleared_on_ctx_guard_drop() {
    clear_for_test_reset();
    let ctx = crate::EvalCtx::new();

    // Shadow should start false.
    assert!(
        !super::in_enabled_scope_ctx(&ctx),
        "shadow should be false before entering ENABLED scope"
    );

    {
        let guard = super::enter_enabled_scope_with_ctx(&ctx);
        assert!(guard.is_some(), "first entry should return Some");
        // Shadow should be true while in scope.
        assert!(
            super::in_enabled_scope_ctx(&ctx),
            "shadow should be true inside ENABLED scope"
        );
        // TLS should also be true.
        assert!(
            super::in_enabled_scope(),
            "TLS should be true inside ENABLED scope"
        );
        // guard drops here
    }

    // After drop, both TLS and shadow should be false.
    assert!(
        !super::in_enabled_scope(),
        "TLS should be false after ENABLED scope exit"
    );
    assert!(
        !super::in_enabled_scope_ctx(&ctx),
        "shadow should be false after ENABLED scope exit (Part of #4027)"
    );
}

/// Part of #4027: Verify that the base `enter_enabled_scope()` (without ctx)
/// does not crash or misbehave — the shadow_ptr is null and is safely skipped.
#[test]
fn test_enabled_scope_base_guard_no_shadow_ptr() {
    clear_for_test_reset();
    let ctx = crate::EvalCtx::new();

    // Shadow starts false.
    assert!(!super::in_enabled_scope_ctx(&ctx));

    {
        // Use base enter_enabled_scope (no ctx) — shadow_ptr is null.
        let guard = super::enter_enabled_scope();
        assert!(guard.is_some());
        // TLS is true.
        assert!(super::in_enabled_scope());
        // Shadow is NOT synced (base guard doesn't touch it).
        assert!(
            !super::in_enabled_scope_ctx(&ctx),
            "base guard should not set shadow"
        );
        // guard drops here
    }

    // TLS is cleared.
    assert!(!super::in_enabled_scope());
    // Shadow was never set, still false.
    assert!(!super::in_enabled_scope_ctx(&ctx));
}
