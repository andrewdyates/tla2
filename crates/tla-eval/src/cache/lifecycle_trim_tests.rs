// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for cache trim behavior at EvalExit soft-cap boundaries.
//! Part of #3100: Updated for partitioned cache architecture.
//! Part of #4053: Updated for consolidated ZERO_ARG_CACHES struct.

use super::{clear_for_test_reset, on_cache_event, CacheEvent};
use crate::cache::dep_tracking::OpEvalDeps;
use crate::cache::op_result_cache::{
    CachedOpResult, NaryOpCacheEntry, NaryOpCacheKey, NARY_CACHES,
};
use crate::cache::zero_arg_cache::ZERO_ARG_CACHES;
use crate::var_index::VarIndex;
use std::sync::Arc;
use tla_core::name_intern::{intern_name, NameId};
use tla_value::Value;

const ZERO_ARG_SOFT_CAP: usize = 10_000;
const NARY_SOFT_CAP: usize = 50_000;
const ZERO_ARG_PERSISTENT_SOFT_CAP: usize = 50_000;
const NARY_PERSISTENT_SOFT_CAP: usize = 50_000;

type ZeroArgKey = (u64, u64, u64, NameId, u32, bool);

fn zero_arg_key(shared_id: u64, name_id: NameId) -> ZeroArgKey {
    (shared_id, 0, 0, name_id, 0, false)
}

fn nary_key(shared_id: u64, op_name: NameId, args_hash: u64) -> NaryOpCacheKey {
    NaryOpCacheKey {
        shared_id,
        local_ops_id: 0,
        instance_subs_id: 0,
        op_name,
        def_loc: 0,
        is_next_state: false,
        args_hash,
        param_args_hash: 0,
    }
}

fn state_dep(value: i64) -> OpEvalDeps {
    let mut deps = OpEvalDeps::default();
    deps.record_state(VarIndex::new(0), &Value::int(value));
    deps
}

/// Part of #3100: State partition exceeds soft cap -> trimmed on EvalExit.
/// Part of #3025: Retain-half replaces cliff-clear.
/// Persistent partition is not affected.
#[test]
fn test_zero_arg_state_partition_soft_cap_on_eval_exit() {
    clear_for_test_reset();

    let name_id = intern_name("op_state");
    // Fill state partition above soft cap with non-constant entries
    ZERO_ARG_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        for i in 0..=ZERO_ARG_SOFT_CAP {
            c.state.insert(
                zero_arg_key(i as u64, name_id),
                vec![CachedOpResult {
                    value: Value::int(i as i64),
                    deps: state_dep(i as i64),
                }],
            );
        }
    });

    // Also put a constant entry in persistent partition
    let persistent_name_id = intern_name("op_const_p");
    ZERO_ARG_CACHES.with(|caches| {
        caches.borrow_mut().persistent.insert(
            zero_arg_key(0, persistent_name_id),
            vec![CachedOpResult {
                value: Value::int(42),
                deps: OpEvalDeps::default(),
            }],
        );
    });

    let before_state = ZERO_ARG_CACHES.with(|c| c.borrow().state.len());
    assert!(before_state > ZERO_ARG_SOFT_CAP);

    on_cache_event(CacheEvent::EvalExit);

    // Part of #3025: State partition trimmed to ~half, not fully cleared.
    let after_state = ZERO_ARG_CACHES.with(|c| c.borrow().state.len());
    assert!(
        after_state <= ZERO_ARG_SOFT_CAP / 2,
        "state partition should be trimmed to ~cap/2, got {after_state}"
    );
    // Persistent partition survives
    let persistent = ZERO_ARG_CACHES.with(|c| c.borrow().persistent.len());
    assert_eq!(persistent, 1);
}

/// Verify state partition below soft cap is NOT cleared by EvalExit.
#[test]
fn test_zero_arg_below_soft_cap_survives_eval_exit() {
    clear_for_test_reset();

    let name_id = intern_name("small_op");
    ZERO_ARG_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        for i in 0..5u64 {
            c.state.insert(
                zero_arg_key(i, name_id),
                vec![CachedOpResult {
                    value: Value::int(i as i64),
                    deps: state_dep(i as i64),
                }],
            );
        }
    });

    on_cache_event(CacheEvent::EvalExit);

    let after = ZERO_ARG_CACHES.with(|c| c.borrow().state.len());
    assert_eq!(after, 5);
}

/// Part of #3100: NARY state partition soft cap -> cleared on EvalExit.
#[test]
fn test_nary_state_partition_soft_cap_on_eval_exit() {
    clear_for_test_reset();

    let name_id = intern_name("nary_state");
    // Fill state partition above soft cap
    NARY_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        for i in 0..=NARY_SOFT_CAP {
            c.state.insert(
                nary_key(i as u64, name_id, 0),
                vec![NaryOpCacheEntry {
                    args: Arc::from(Vec::<Value>::new().into_boxed_slice()),
                    result: CachedOpResult {
                        value: Value::int(i as i64),
                        deps: state_dep(i as i64),
                    },
                }],
            );
        }
    });

    // Put a constant entry in persistent
    let persistent_name_id = intern_name("nary_const_p");
    NARY_CACHES.with(|caches| {
        caches.borrow_mut().persistent.insert(
            nary_key(0, persistent_name_id, 0),
            vec![NaryOpCacheEntry {
                args: Arc::from(Vec::<Value>::new().into_boxed_slice()),
                result: CachedOpResult {
                    value: Value::int(42),
                    deps: OpEvalDeps::default(),
                },
            }],
        );
    });

    let before = NARY_CACHES.with(|c| c.borrow().state.len());
    assert!(before > NARY_SOFT_CAP);

    on_cache_event(CacheEvent::EvalExit);

    // Part of #3025: State partition trimmed to ~half, not fully cleared.
    let after = NARY_CACHES.with(|c| c.borrow().state.len());
    assert!(
        after <= NARY_SOFT_CAP / 2,
        "NARY state partition should be trimmed to ~cap/2, got {after}"
    );
    // Persistent partition survives (below its own soft cap)
    let persistent = NARY_CACHES.with(|c| c.borrow().persistent.len());
    assert_eq!(persistent, 1);
}

/// Persistent ZERO_ARG cache exceeds soft cap -> trimmed on EvalExit.
#[test]
fn test_zero_arg_persistent_soft_cap_on_eval_exit() {
    clear_for_test_reset();

    let name_id = intern_name("op_persistent_trim");
    ZERO_ARG_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        for i in 0..=ZERO_ARG_PERSISTENT_SOFT_CAP {
            c.persistent.insert(
                zero_arg_key(i as u64, name_id),
                vec![CachedOpResult {
                    value: Value::int(i as i64),
                    deps: OpEvalDeps::default(),
                }],
            );
        }
    });

    let before = ZERO_ARG_CACHES.with(|c| c.borrow().persistent.len());
    assert!(before > ZERO_ARG_PERSISTENT_SOFT_CAP);

    on_cache_event(CacheEvent::EvalExit);

    let after = ZERO_ARG_CACHES.with(|c| c.borrow().persistent.len());
    assert!(
        after <= ZERO_ARG_PERSISTENT_SOFT_CAP / 2,
        "persistent zero-arg cache should be trimmed to ~cap/2, got {after}"
    );
}

/// Persistent NARY cache exceeds soft cap -> trimmed on EvalExit.
#[test]
fn test_nary_persistent_soft_cap_on_eval_exit() {
    clear_for_test_reset();

    let name_id = intern_name("nary_persistent_trim");
    NARY_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        for i in 0..=NARY_PERSISTENT_SOFT_CAP {
            c.persistent.insert(
                nary_key(i as u64, name_id, 0),
                vec![NaryOpCacheEntry {
                    args: Arc::from(Vec::<Value>::new().into_boxed_slice()),
                    result: CachedOpResult {
                        value: Value::int(i as i64),
                        deps: OpEvalDeps::default(),
                    },
                }],
            );
        }
    });

    let before = NARY_CACHES.with(|c| c.borrow().persistent.len());
    assert!(before > NARY_PERSISTENT_SOFT_CAP);

    on_cache_event(CacheEvent::EvalExit);

    let after = NARY_CACHES.with(|c| c.borrow().persistent.len());
    assert!(
        after <= NARY_PERSISTENT_SOFT_CAP / 2,
        "persistent nary cache should be trimmed to ~cap/2, got {after}"
    );
}

/// Persistent cache below soft cap survives EvalExit unchanged.
#[test]
fn test_persistent_below_soft_cap_survives_eval_exit() {
    clear_for_test_reset();

    let name_id = intern_name("persistent_small");
    ZERO_ARG_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        for i in 0..5u64 {
            c.persistent.insert(
                zero_arg_key(i, name_id),
                vec![CachedOpResult {
                    value: Value::int(i as i64),
                    deps: OpEvalDeps::default(),
                }],
            );
        }
    });

    NARY_CACHES.with(|caches| {
        let mut c = caches.borrow_mut();
        for i in 0..3u64 {
            c.persistent.insert(
                nary_key(i, name_id, 0),
                vec![NaryOpCacheEntry {
                    args: Arc::from(Vec::<Value>::new().into_boxed_slice()),
                    result: CachedOpResult {
                        value: Value::int(i as i64),
                        deps: OpEvalDeps::default(),
                    },
                }],
            );
        }
    });

    on_cache_event(CacheEvent::EvalExit);

    let zero_arg_after = ZERO_ARG_CACHES.with(|c| c.borrow().persistent.len());
    assert_eq!(
        zero_arg_after, 5,
        "small persistent zero-arg should survive"
    );

    let nary_after = NARY_CACHES.with(|c| c.borrow().persistent.len());
    assert_eq!(nary_after, 3, "small persistent nary should survive");
}
