// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Storage-mode unit tests.
//!
//! Part of #3436: extracted from `storage_modes.rs`.

use super::*;
use crate::arena::BulkStateStorage;
use crate::config::Config;
use crate::test_support::parse_module;
use crate::Value;

fn minimal_module() -> tla_core::ast::Module {
    parse_module(
        r#"
---- MODULE StorageModeTest ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
====
"#,
    )
}

fn minimal_config() -> Config {
    Config {
        init: Some("Init".to_string()),
        next: Some("Next".to_string()),
        ..Default::default()
    }
}

// -----------------------------------------------------------------------
// FullStateStorage tests
// -----------------------------------------------------------------------

#[test]
fn full_state_dequeue_present_returns_state_and_removes_from_seen() {
    let module = minimal_module();
    let config = minimal_config();
    let mut mc = ModelChecker::new(&module, &config);
    mc.set_store_states(true);

    let fp = Fingerprint(42);
    let state = ArrayState::from_values(vec![Value::int(7)]);
    mc.state_storage.seen.insert(fp, state);

    let mut storage = FullStateStorage;
    let result = storage.dequeue((fp, 5), &mut mc).unwrap().unwrap();
    assert_eq!(result.0, fp);
    assert_eq!(result.2, 5);
    // State should be removed from seen during dequeue
    assert!(!mc.state_storage.seen.contains_key(&fp));
}

#[test]
fn full_state_dequeue_missing_fp_returns_none_and_increments_phantom() {
    let module = minimal_module();
    let config = minimal_config();
    let mut mc = ModelChecker::new(&module, &config);

    let initial_phantoms = mc.stats.phantom_dequeues;
    let mut storage = FullStateStorage;
    let result = storage.dequeue((Fingerprint(999), 0), &mut mc).unwrap();
    assert!(result.is_none());
    assert_eq!(mc.stats.phantom_dequeues, initial_phantoms + 1);
}

#[test]
fn full_state_return_current_reinserts_into_seen() {
    let module = minimal_module();
    let config = minimal_config();
    let mut mc = ModelChecker::new(&module, &config);
    mc.set_store_states(true);

    let fp = Fingerprint(42);
    let state = ArrayState::from_values(vec![Value::int(7)]);
    assert!(!mc.state_storage.seen.contains_key(&fp));

    let mut storage = FullStateStorage;
    storage.return_current(fp, state, &mut mc);
    assert!(mc.state_storage.seen.contains_key(&fp));
}

#[test]
fn full_state_admit_new_state_returns_entry() {
    let module = minimal_module();
    let config = minimal_config();
    let mut mc = ModelChecker::new(&module, &config);
    mc.set_store_states(true);

    let fp = Fingerprint(42);
    let state = ArrayState::from_values(vec![Value::int(7)]);

    let mut storage = FullStateStorage;
    let entry = storage
        .admit_successor(fp, state, None, 0, &mut mc)
        .unwrap();
    assert!(entry.is_some());
    let (ret_fp, ret_depth) = entry.unwrap();
    assert_eq!(ret_fp, fp);
    assert_eq!(ret_depth, 0);
}

#[test]
fn full_state_admit_duplicate_returns_none() {
    let module = minimal_module();
    let config = minimal_config();
    let mut mc = ModelChecker::new(&module, &config);
    mc.set_store_states(true);

    let fp = Fingerprint(42);

    let mut storage = FullStateStorage;
    let first = storage
        .admit_successor(
            fp,
            ArrayState::from_values(vec![Value::int(7)]),
            None,
            0,
            &mut mc,
        )
        .unwrap();
    assert!(first.is_some());

    let second = storage
        .admit_successor(
            fp,
            ArrayState::from_values(vec![Value::int(7)]),
            None,
            1,
            &mut mc,
        )
        .unwrap();
    assert!(second.is_none());
}

#[test]
fn full_state_use_diffs_true_by_default() {
    let module = minimal_module();
    let config = minimal_config();
    let mc = ModelChecker::new(&module, &config);

    let storage = FullStateStorage;
    // Default: no VIEW, no symmetry, no liveness → true
    // (unless TLA2_FORCE_NO_DIFFS env var is set)
    if !crate::check::debug::force_no_diffs() {
        assert!(storage.use_diffs(&mc));
    }
}

#[test]
fn full_state_cache_full_liveness_noop_when_not_caching() {
    let module = minimal_module();
    let config = minimal_config();
    let mut mc = ModelChecker::new(&module, &config);
    // Default: cache_for_liveness is false

    let storage = FullStateStorage;
    let successors = vec![(
        ArrayState::from_values(vec![Value::int(1)]),
        Fingerprint(10),
    )];
    let result = storage.cache_full_liveness(Fingerprint(1), &successors, &mut mc);
    assert!(result.is_ok());
}

// -----------------------------------------------------------------------
// FingerprintOnlyStorage tests
// -----------------------------------------------------------------------

#[test]
fn fp_only_dequeue_owned_entry_returns_state() {
    let module = minimal_module();
    let config = minimal_config();
    let mut mc = ModelChecker::new(&module, &config);

    let fp = Fingerprint(42);
    let state = ArrayState::from_values(vec![Value::int(7)]);
    let entry = NoTraceQueueEntry::Owned {
        state: state.clone(),
        fp,
    };

    let bulk = BulkStateStorage::empty(1);
    let mut storage = FingerprintOnlyStorage::new(bulk, 1);
    let result = storage.dequeue((entry, 3, 0), &mut mc).unwrap().unwrap();
    assert_eq!(result.0, fp);
    assert_eq!(result.2, 3);
}

#[test]
fn fp_only_dequeue_sets_parent_trace_loc() {
    let module = minimal_module();
    let config = minimal_config();
    let mut mc = ModelChecker::new(&module, &config);

    let fp = Fingerprint(42);
    let state = ArrayState::from_values(vec![Value::int(7)]);
    let entry = NoTraceQueueEntry::Owned { state, fp };
    let trace_loc = 12345u64;

    let bulk = BulkStateStorage::empty(1);
    let mut storage = FingerprintOnlyStorage::new(bulk, 1);
    storage.dequeue((entry, 0, trace_loc), &mut mc).unwrap();
    assert_eq!(mc.trace.current_parent_trace_loc, Some(trace_loc));
}

#[test]
fn fp_only_return_current_is_noop() {
    let module = minimal_module();
    let config = minimal_config();
    let mut mc = ModelChecker::new(&module, &config);

    let bulk = BulkStateStorage::empty(1);
    let mut storage = FingerprintOnlyStorage::new(bulk, 1);

    let states_before = mc.stats.states_found;
    let phantoms_before = mc.stats.phantom_dequeues;

    // Should not panic or modify any state
    storage.return_current(
        Fingerprint(42),
        ArrayState::from_values(vec![Value::int(7)]),
        &mut mc,
    );

    assert_eq!(
        mc.stats.states_found, states_before,
        "return_current should not change states_found"
    );
    assert_eq!(
        mc.stats.phantom_dequeues, phantoms_before,
        "return_current should not change phantom_dequeues"
    );
}

#[test]
fn fp_only_admit_new_state_returns_entry() {
    let module = minimal_module();
    let config = minimal_config();
    let mut mc = ModelChecker::new(&module, &config);

    let fp = Fingerprint(42);
    let state = ArrayState::from_values(vec![Value::int(7)]);

    let bulk = BulkStateStorage::empty(1);
    let mut storage = FingerprintOnlyStorage::new(bulk, 1);
    let entry = storage
        .admit_successor(fp, state, None, 0, &mut mc)
        .unwrap();
    assert!(entry.is_some());
    let (queue_entry, depth, _trace_loc) = entry.unwrap();
    assert_eq!(depth, 0);
    assert!(matches!(queue_entry, NoTraceQueueEntry::Owned { fp: f, .. } if f == fp));
}

#[test]
fn fp_only_admit_duplicate_returns_none() {
    let module = minimal_module();
    let config = minimal_config();
    let mut mc = ModelChecker::new(&module, &config);

    let fp = Fingerprint(42);

    let bulk = BulkStateStorage::empty(1);
    let mut storage = FingerprintOnlyStorage::new(bulk, 1);
    let first = storage
        .admit_successor(
            fp,
            ArrayState::from_values(vec![Value::int(7)]),
            None,
            0,
            &mut mc,
        )
        .unwrap();
    assert!(first.is_some());

    let second = storage
        .admit_successor(
            fp,
            ArrayState::from_values(vec![Value::int(7)]),
            None,
            1,
            &mut mc,
        )
        .unwrap();
    assert!(second.is_none());
}

#[test]
fn fp_only_use_diffs_true_by_default() {
    let module = minimal_module();
    let config = minimal_config();
    let mc = ModelChecker::new(&module, &config);

    let bulk = BulkStateStorage::empty(1);
    let storage = FingerprintOnlyStorage::new(bulk, 1);
    // Default: no VIEW, no symmetry, cache_for_liveness=false → true
    if !crate::check::debug::force_no_diffs() {
        assert!(storage.use_diffs(&mc));
    }
}

#[test]
fn fp_only_cache_diff_liveness_is_noop() {
    let module = minimal_module();
    let config = minimal_config();
    let mut mc = ModelChecker::new(&module, &config);

    let bulk = BulkStateStorage::empty(1);
    let storage = FingerprintOnlyStorage::new(bulk, 1);
    // Should succeed without error (no-op, doesn't store anything)
    let result = storage.cache_diff_liveness(Fingerprint(1), Some(vec![Fingerprint(2)]), &mut mc);
    assert!(result.is_ok());
}

#[test]
fn fp_only_cache_full_liveness_noop_when_not_caching() {
    let module = minimal_module();
    let config = minimal_config();
    let mut mc = ModelChecker::new(&module, &config);

    let bulk = BulkStateStorage::empty(1);
    let storage = FingerprintOnlyStorage::new(bulk, 1);
    let successors = vec![(
        ArrayState::from_values(vec![Value::int(1)]),
        Fingerprint(10),
    )];
    let result = storage.cache_full_liveness(Fingerprint(1), &successors, &mut mc);
    assert!(result.is_ok());
}
