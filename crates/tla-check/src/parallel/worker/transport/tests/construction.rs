// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transport construction and lifecycle tests.

use super::helpers::{build_array_transport_via_new, build_handle_transport};
use crate::check::model_checker::bfs::transport::BfsTransport;
use crate::intern::{HandleState, HandleStateInternerBank};
use crate::var_index::VarRegistry;
use crate::Value;
use std::sync::Arc;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_handle_state_transport_reuses_decode_scratch_after_release() {
    let registry = Arc::new(VarRegistry::from_names(["x", "y"]));
    let bank = Arc::new(HandleStateInternerBank::new(1));
    let mut transport = build_handle_transport(Arc::clone(&registry), Arc::clone(&bank));

    let first = HandleState::from_values_sharded(
        &[Value::SmallInt(1), Value::SmallInt(2)],
        &registry,
        &bank,
        0,
    );
    let (first_fp, first_array, _) = match transport.resolve((first, 0)) {
        Ok(Some(resolved)) => resolved,
        Ok(None) => panic!("resolve unexpectedly skipped the first HandleState"),
        Err(e) => panic!("resolve should succeed for the first HandleState: {e:?}"),
    };
    let first_ptr = first_array.values().as_ptr();
    let first_vals = first_array.materialize_values();
    assert_eq!(
        first_vals.as_slice(),
        &[Value::SmallInt(1), Value::SmallInt(2)]
    );
    transport.release_state(first_fp, first_array);

    let second = HandleState::from_values_sharded(
        &[Value::SmallInt(3), Value::SmallInt(4)],
        &registry,
        &bank,
        0,
    );
    let (second_fp, second_array, _) = match transport.resolve((second, 0)) {
        Ok(Some(resolved)) => resolved,
        Ok(None) => panic!("resolve unexpectedly skipped the second HandleState"),
        Err(e) => panic!("resolve should succeed for the second HandleState: {e:?}"),
    };
    let second_vals = second_array.materialize_values();
    assert_eq!(
        second_vals.as_slice(),
        &[Value::SmallInt(3), Value::SmallInt(4)]
    );
    assert_eq!(
        second_array.values().as_ptr(),
        first_ptr,
        "ParallelTransport should recycle the same decode scratch allocation after release_state"
    );
    transport.release_state(second_fp, second_array);
}

#[test]
fn test_parallel_transport_new_staggers_initial_steal_cursor() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let t0 = build_array_transport_via_new(0, 4, Arc::clone(&registry));
    let t1 = build_array_transport_via_new(1, 4, Arc::clone(&registry));
    let t2 = build_array_transport_via_new(2, 4, Arc::clone(&registry));
    let t3 = build_array_transport_via_new(3, 4, registry);

    let cursors = [
        t0.steal_cursor,
        t1.steal_cursor,
        t2.steal_cursor,
        t3.steal_cursor,
    ];
    let unique: std::collections::HashSet<_> = cursors.iter().collect();
    assert_eq!(
        unique.len(),
        4,
        "each worker should start with a different steal cursor to reduce initial contention: {cursors:?}"
    );
}

#[test]
fn test_parallel_transport_new_single_worker_starts_at_zero() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let transport = build_array_transport_via_new(0, 1, registry);

    assert_eq!(
        transport.steal_cursor, 0,
        "single-worker transport should seed the cursor to the only valid queue index"
    );
}
