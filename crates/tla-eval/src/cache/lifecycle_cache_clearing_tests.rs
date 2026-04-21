// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for zero-arg cache discrimination and intern table clearing.
//!
//! Part of #3442: extracted from lifecycle_tests.rs.

use super::{clear_for_test_reset, on_cache_event, CacheEvent};
use crate::cache::dep_tracking::OpEvalDeps;
use crate::cache::op_result_cache::CachedOpResult;
use crate::cache::zero_arg_cache::ZERO_ARG_CACHES;
use crate::var_index::VarIndex;
use std::sync::Arc;
use tla_core::name_intern::intern_name;
use tla_value::{FuncValue, IntIntervalFunc, SortedSet, Value};

/// Regression: run/test reset must clear zero-arg entries from both lifecycle
/// partitions. Constant entries live in the persistent partition after #3100.
#[test]
fn test_zero_arg_op_cache_fully_cleared_on_test_reset() {
    clear_for_test_reset();

    let name_id = intern_name("const_op");
    ZERO_ARG_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        c.persistent.insert(
            (1, 0, 0, name_id, 0, false),
            vec![CachedOpResult {
                value: Value::int(42),
                deps: OpEvalDeps::default(),
            }],
        );
    });
    ZERO_ARG_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        let mut deps = OpEvalDeps::default();
        deps.record_state(VarIndex::new(0), &Value::int(7));
        c.state.insert(
            (1, 0, 0, name_id, 1, false),
            vec![CachedOpResult {
                value: Value::int(99),
                deps,
            }],
        );
    });
    assert_eq!(ZERO_ARG_CACHES.with(|c| c.borrow().persistent.len()), 1);
    assert_eq!(ZERO_ARG_CACHES.with(|c| c.borrow().state.len()), 1);

    // TestReset must fully clear both the state and persistent partitions.
    on_cache_event(CacheEvent::TestReset);

    let after_state = ZERO_ARG_CACHES.with(|c| c.borrow().state.len());
    let after_persistent = ZERO_ARG_CACHES.with(|c| c.borrow().persistent.len());
    assert_eq!(
        after_state, 0,
        "ZERO_ARG_CACHES state entries must be cleared on TestReset"
    );
    assert_eq!(
        after_persistent, 0,
        "ZERO_ARG_CACHES persistent entries must be cleared on TestReset"
    );
}

/// Regression #3097: Zero-arg cache entries from different scopes (different
/// local_ops_id / instance_subs_id) must not alias each other. Before #3097,
/// the zero-arg key omitted scope ids, so a constant entry from scope A could
/// be reused for scope B. After #3100, constant entries live in the persistent
/// partition and must still remain scope-discriminated there.
///
/// This test verifies that after the key expansion, entries with different
/// scope ids are stored separately and do not collide even with matching
/// shared_id, op_name, def_loc, and is_next_state.
#[test]
fn test_zero_arg_cache_scope_discrimination() {
    clear_for_test_reset();

    let name_id = intern_name("scope_test_op");
    let scope_a: u64 = 0x1000; // simulates content-based scope id
    let scope_b: u64 = 0x2000; // simulates content-based scope id

    // Insert a constant entry from scope A in the persistent partition.
    ZERO_ARG_CACHES.with(|caches| {
        caches.borrow_mut().persistent.insert(
            (1, scope_a, 0, name_id, 0, false),
            vec![CachedOpResult {
                value: Value::int(42),
                deps: OpEvalDeps::default(), // constant (empty deps)
            }],
        );
    });

    // Insert a different value from scope B (same shared_id, name, def_loc, is_next_state).
    ZERO_ARG_CACHES.with(|caches| {
        caches.borrow_mut().persistent.insert(
            (1, scope_b, 0, name_id, 0, false),
            vec![CachedOpResult {
                value: Value::int(99),
                deps: OpEvalDeps::default(), // constant (empty deps)
            }],
        );
    });

    // Both entries should coexist — 2 keys, not 1.
    assert_eq!(
        ZERO_ARG_CACHES.with(|c| c.borrow().persistent.len()),
        2,
        "different scope ids must produce different cache keys"
    );

    // After clear_for_state_boundary(), both constant entries survive in the persistent partition.
    super::clear_for_state_boundary();

    let scope_a_val = ZERO_ARG_CACHES.with(|caches| {
        caches
            .borrow()
            .persistent
            .get(&(1, scope_a, 0, name_id, 0, false))
            .and_then(|entries| entries.first().map(|e| e.value.clone()))
    });
    let scope_b_val = ZERO_ARG_CACHES.with(|caches| {
        caches
            .borrow()
            .persistent
            .get(&(1, scope_b, 0, name_id, 0, false))
            .and_then(|entries| entries.first().map(|e| e.value.clone()))
    });

    assert_eq!(
        scope_a_val,
        Some(Value::int(42)),
        "scope A entry should retain its original value (42)"
    );
    assert_eq!(
        scope_b_val,
        Some(Value::int(99)),
        "scope B entry should retain its original value (99), not alias scope A"
    );

    clear_for_test_reset();
}

/// Regression #3097: Verify that instance_subs_id also discriminates cache entries.
/// A zero-arg operator evaluated through INSTANCE WITH substitution_1 must not
/// return a cached result from substitution_2.
#[test]
fn test_zero_arg_cache_instance_subs_discrimination() {
    clear_for_test_reset();

    let name_id = intern_name("inst_subs_op");
    let inst_a: u64 = 0xA000; // simulates content-based instance_subs id
    let inst_b: u64 = 0xB000; // simulates content-based instance_subs id

    ZERO_ARG_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        c.persistent.insert(
            (1, 0, inst_a, name_id, 0, false),
            vec![CachedOpResult {
                value: Value::int(10),
                deps: OpEvalDeps::default(),
            }],
        );
        c.persistent.insert(
            (1, 0, inst_b, name_id, 0, false),
            vec![CachedOpResult {
                value: Value::int(20),
                deps: OpEvalDeps::default(),
            }],
        );
    });

    assert_eq!(
        ZERO_ARG_CACHES.with(|c| c.borrow().persistent.len()),
        2,
        "different instance_subs_id must produce different cache keys"
    );

    // Verify no cross-contamination after state-boundary clear.
    super::clear_for_state_boundary();

    let inst_a_val = ZERO_ARG_CACHES.with(|caches| {
        caches
            .borrow()
            .persistent
            .get(&(1, 0, inst_a, name_id, 0, false))
            .and_then(|entries| entries.first().map(|e| e.value.clone()))
    });
    assert_eq!(
        inst_a_val,
        Some(Value::int(10)),
        "instance A entry should retain value 10"
    );

    clear_for_test_reset();
}

/// Part of #3805/#4158: `clear_for_eval_scope_boundary()` preserves the persistent
/// partition but clears the state partition. Persistent entries have genuinely empty
/// deps (no state/next/local, not inconsistent, no instance_lazy_read taint). The
/// `instance_lazy_read` taint mechanism (#3447) and the LazyFunc state capture guard
/// (#4158) ensure that state-dependent entries are routed to the state partition,
/// so persistent entries are truly constant and safe to retain across scope boundaries.
///
/// Previously (#3447) this test expected both partitions to be cleared; updated for
/// the #3805 optimization (persistent partition preserved for MCNanoMedium perf).
#[test]
fn test_eval_scope_boundary_preserves_persistent_clears_state_partition() {
    clear_for_test_reset();

    let name_id = intern_name("instance_votes_op");

    // Persistent partition entry with genuinely empty deps (truly constant).
    ZERO_ARG_CACHES.with(|caches| {
        caches.borrow_mut().persistent.insert(
            (1, 0, 0, name_id, 0, false),
            vec![CachedOpResult {
                value: Value::int(42),
                deps: OpEvalDeps::default(), // empty deps = "constant" = persistent partition
            }],
        );
    });

    // State partition entry with state deps.
    ZERO_ARG_CACHES.with(|caches| {
        let mut deps = OpEvalDeps::default();
        deps.record_state(VarIndex::new(0), &Value::int(7));
        caches.borrow_mut().state.insert(
            (1, 0, 0, name_id, 1, false),
            vec![CachedOpResult {
                value: Value::int(99),
                deps,
            }],
        );
    });

    assert_eq!(ZERO_ARG_CACHES.with(|c| c.borrow().persistent.len()), 1);
    assert_eq!(ZERO_ARG_CACHES.with(|c| c.borrow().state.len()), 1);

    // clear_for_eval_scope_boundary preserves persistent, clears state.
    // Part of #3805: persistent entries are genuinely constant (guarded by
    // instance_lazy_read taint and LazyFunc state capture check).
    super::clear_for_eval_scope_boundary();

    assert_eq!(
        ZERO_ARG_CACHES.with(|c| c.borrow().persistent.len()),
        1,
        "#3805: clear_for_eval_scope_boundary preserves persistent partition"
    );
    assert_eq!(
        ZERO_ARG_CACHES.with(|c| c.borrow().state.len()),
        0,
        "clear_for_eval_scope_boundary must clear state partition"
    );

    clear_for_test_reset();
}

/// Part of #3805/#4158: `clear_for_eval_scope_boundary()` preserves the nary
/// persistent partition but clears the nary state partition. Same rationale as
/// the zero-arg test above: persistent entries are genuinely constant (empty deps,
/// no instance_lazy_read taint, no LazyFunc state capture).
#[test]
fn test_eval_scope_boundary_preserves_nary_persistent_clears_state_partition() {
    use crate::cache::op_result_cache::{NaryOpCacheEntry, NaryOpCacheKey, NARY_CACHES};

    clear_for_test_reset();

    let name_id = intern_name("instance_shows_safe_at");

    // Persistent nary entry with genuinely empty deps (truly constant).
    NARY_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        c.persistent.insert(
            NaryOpCacheKey {
                shared_id: 1,
                local_ops_id: 0,
                instance_subs_id: 0,
                op_name: name_id,
                def_loc: 0,
                is_next_state: false,
                args_hash: 0xDEAD,
                param_args_hash: 0,
            },
            vec![NaryOpCacheEntry {
                args: Arc::from(vec![Value::int(1)]),
                result: CachedOpResult {
                    value: Value::Bool(true),
                    deps: OpEvalDeps::default(),
                },
            }],
        );

        let mut deps = OpEvalDeps::default();
        deps.record_state(VarIndex::new(0), &Value::int(1));
        c.state.insert(
            NaryOpCacheKey {
                shared_id: 1,
                local_ops_id: 0,
                instance_subs_id: 0,
                op_name: name_id,
                def_loc: 1,
                is_next_state: false,
                args_hash: 0xBEEF,
                param_args_hash: 0,
            },
            vec![NaryOpCacheEntry {
                args: Arc::from(vec![Value::int(2)]),
                result: CachedOpResult {
                    value: Value::Bool(false),
                    deps,
                },
            }],
        );
    });

    assert_eq!(NARY_CACHES.with(|c| c.borrow().persistent.len()), 1);
    assert_eq!(NARY_CACHES.with(|c| c.borrow().state.len()), 1);

    super::clear_for_eval_scope_boundary();

    assert_eq!(
        NARY_CACHES.with(|c| c.borrow().persistent.len()),
        1,
        "#3805: clear_for_eval_scope_boundary preserves nary persistent partition"
    );
    assert_eq!(
        NARY_CACHES.with(|c| c.borrow().state.len()),
        0,
        "clear_for_eval_scope_boundary must clear nary state partition"
    );

    clear_for_test_reset();
}

/// Contrast test: `clear_for_state_boundary()` must NOT clear persistent partitions.
/// Persistent entries with genuinely empty deps (true constants) should survive state
/// transitions for performance. Only eval-scope boundaries need the aggressive clear.
#[test]
fn test_state_boundary_preserves_persistent_partition() {
    clear_for_test_reset();

    let name_id = intern_name("true_constant_op");

    ZERO_ARG_CACHES.with(|caches| {
        caches.borrow_mut().persistent.insert(
            (1, 0, 0, name_id, 0, false),
            vec![CachedOpResult {
                value: Value::int(42),
                deps: OpEvalDeps::default(),
            }],
        );
    });

    super::clear_for_state_boundary();

    assert_eq!(
        ZERO_ARG_CACHES.with(|c| c.borrow().persistent.len()),
        1,
        "clear_for_state_boundary must preserve persistent partition entries"
    );

    clear_for_test_reset();
}

/// Regression: `clear_run_reset_impl()` must clear the global set intern table,
/// not just eval caches. Otherwise a tuple-seeded test can leak an interned
/// `{<<>>}` entry into the next test and silently substitute it for
/// `{Func(empty)}` due to cross-type equality.
#[test]
fn test_clear_for_test_reset_clears_set_intern_table_variant_pollution() {
    clear_for_test_reset();

    let _tuple_seed = SortedSet::from_iter(vec![Value::Tuple(Vec::<Value>::new().into())]);

    clear_for_test_reset();

    let empty_func = Value::Func(Arc::new(FuncValue::from_sorted_entries(vec![])));
    let func_set = SortedSet::from_iter(vec![empty_func]);
    let element = func_set
        .iter()
        .next()
        .expect("function set should contain one element");
    assert!(
        matches!(element, Value::Func(_)),
        "clear_for_test_reset must clear SET_INTERN_TABLE; expected Func(empty), got {element:?}"
    );

    clear_for_test_reset();
}

/// Regression: `clear_run_reset_impl()` must clear the IntIntervalFunc intern
/// table so TestReset/RunReset release retained `Arc<Vec<Value>>` references.
///
/// Note: The intern table is global (`OnceLock<DashMap>`), so parallel tests may
/// clear it between our `except()` and our refcount check.  We therefore use
/// `>=` for the pre-clear assertion and verify the post-clear refcount drops to
/// exactly 1 (our local `modified` is the sole remaining owner).
#[test]
fn test_clear_for_test_reset_releases_int_func_interned_array_reference() {
    clear_for_test_reset();

    let modified = IntIntervalFunc::new(1, 2, vec![Value::int(10), Value::int(20)])
        .except(Value::int(1), Value::int(99));
    let rc_before = modified.values_refcount();
    // Normally 2 (local + intern table), but a concurrent test may have cleared the
    // table between `except()` and this check, leaving refcount == 1.  The critical
    // property we verify is that clear_for_test_reset *releases* the table reference.
    assert!(
        rc_before >= 1,
        "refcount must be at least 1 (held by modified); got {rc_before}"
    );

    clear_for_test_reset();

    assert_eq!(
        modified.values_refcount(),
        1,
        "clear_for_test_reset must release the INT_FUNC_INTERN_TABLE reference"
    );
}

/// Part of #4158: LazyFunc entries with `instance_lazy_read` taint must be routed
/// to the state partition (not persistent) by `zero_arg_insert`. This ensures that
/// LazyFuncs that capture state (via `snapshot_state_envs()`) are cleared on every
/// state boundary, preventing stale captured state from leaking across BFS states.
///
/// The `instance_lazy_read` flag is set by:
/// - Fix #3447: INSTANCE lazy binding reads
/// - Fix #4145: Self-referential FuncDef operators (e.g., VoteProof's SA[bb])
/// - Fix #4158: Non-self-referential FuncDef operators that capture state
///
/// All three paths use `instance_lazy_read = true` to prevent persistent partition
/// placement even when dep tracking shows empty state/next/local deps.
#[test]
fn test_instance_lazy_read_taint_routes_to_state_partition() {
    use crate::cache::zero_arg_cache::{deps_are_persistent, zero_arg_insert};

    clear_for_test_reset();

    let name_id = intern_name("lazy_func_with_state_capture");

    // Entry with instance_lazy_read = true (simulates LazyFunc capturing state).
    let mut deps = OpEvalDeps::default();
    deps.instance_lazy_read = true;

    // Verify deps_are_persistent rejects this.
    assert!(
        !deps_are_persistent(&deps),
        "deps with instance_lazy_read must NOT be classified as persistent"
    );

    // Insert via zero_arg_insert — should route to state partition.
    zero_arg_insert(
        (1, 0, 0, name_id, 0, false),
        CachedOpResult {
            value: Value::int(42),
            deps,
        },
    );

    // Verify: state partition has the entry, persistent does not.
    let (state_count, persistent_count) = ZERO_ARG_CACHES.with(|c| {
        let c = c.borrow();
        (c.state.len(), c.persistent.len())
    });
    assert_eq!(
        state_count, 1,
        "instance_lazy_read entry must be in state partition"
    );
    assert_eq!(
        persistent_count, 0,
        "instance_lazy_read entry must NOT be in persistent partition"
    );

    // After state boundary clear, the entry should be gone.
    super::clear_for_state_boundary();

    let after_state = ZERO_ARG_CACHES.with(|c| c.borrow().state.len());
    assert_eq!(
        after_state, 0,
        "instance_lazy_read entry must be cleared on state boundary"
    );

    clear_for_test_reset();
}
