// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::state_arena::{StateArena, ThreadLocalArena};
use super::*;
use crate::var_index::VarIndex;
use crate::Value;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_arena_basic() {
    let arena = StateArena::new();

    // Allocate some values
    let values = vec![Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)];
    let slice = arena.alloc_slice(&values);

    assert_eq!(slice.len(), 3);
    assert_eq!(slice[0], Value::SmallInt(1));
    assert_eq!(slice[1], Value::SmallInt(2));
    assert_eq!(slice[2], Value::SmallInt(3));

    // Statistics should be updated
    assert!(arena.allocated_bytes() > 0);
    assert_eq!(arena.allocation_count(), 1);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_arena_empty_slice() {
    let arena = StateArena::new();
    let slice = arena.alloc_slice(&[]);
    assert!(slice.is_empty());
    assert_eq!(arena.allocation_count(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_arena_vec() {
    let arena = StateArena::new();
    let vec = vec![Value::Bool(true), Value::Bool(false)];
    let slice = arena.alloc_vec(vec);

    assert_eq!(slice.len(), 2);
    assert_eq!(slice[0], Value::Bool(true));
    assert_eq!(slice[1], Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_arena_capacity() {
    // Pre-allocate for 1000 states
    let arena = StateArena::with_capacity(1000);
    // Should have at least 500KB capacity (1000 * 500 bytes)
    assert!(arena.chunk_capacity() >= 500_000);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_arena_reset() {
    let mut arena = StateArena::new();

    // Allocate some data
    let _ = arena.alloc_slice(&[Value::SmallInt(1)]);
    assert!(arena.allocated_bytes() > 0);

    // Reset
    arena.reset();
    assert_eq!(arena.allocated_bytes(), 0);
    assert_eq!(arena.allocation_count(), 0);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_thread_local_arena() {
    let tl_arena = ThreadLocalArena::new();
    let arena = tl_arena.get();

    let slice = arena.alloc_slice(&[Value::SmallInt(42)]);
    assert_eq!(slice.len(), 1);
    assert_eq!(slice[0], Value::SmallInt(42));
}

// BulkStateStorage tests

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bulk_storage_basic() {
    let mut storage = BulkStateStorage::new(3, 100);

    // Add a state
    let values = vec![Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)];
    let idx = storage.push_state(&values);

    assert_eq!(idx, 0);
    assert_eq!(storage.len(), 1);
    assert_eq!(storage.vars_per_state(), 3);

    // Retrieve state
    let retrieved = storage.get_state(0);
    assert_eq!(retrieved.len(), 3);
    assert_eq!(retrieved[0], Value::SmallInt(1));
    assert_eq!(retrieved[1], Value::SmallInt(2));
    assert_eq!(retrieved[2], Value::SmallInt(3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bulk_storage_multiple_states() {
    let mut storage = BulkStateStorage::new(2, 100);

    // Add multiple states
    let idx0 = storage.push_state(&[Value::Bool(true), Value::SmallInt(10)]);
    let idx1 = storage.push_state(&[Value::Bool(false), Value::SmallInt(20)]);
    let idx2 = storage.push_state(&[Value::Bool(true), Value::SmallInt(30)]);

    assert_eq!(idx0, 0);
    assert_eq!(idx1, 1);
    assert_eq!(idx2, 2);
    assert_eq!(storage.len(), 3);

    // Verify each state
    assert_eq!(storage.get_state(0)[0], Value::Bool(true));
    assert_eq!(storage.get_state(0)[1], Value::SmallInt(10));
    assert_eq!(storage.get_state(1)[0], Value::Bool(false));
    assert_eq!(storage.get_state(1)[1], Value::SmallInt(20));
    assert_eq!(storage.get_state(2)[0], Value::Bool(true));
    assert_eq!(storage.get_state(2)[1], Value::SmallInt(30));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bulk_storage_get_set_value() {
    let mut storage = BulkStateStorage::new(3, 10);
    storage.push_state(&[Value::SmallInt(1), Value::SmallInt(2), Value::SmallInt(3)]);

    // Get individual value
    assert_eq!(storage.get_value(0, 1), &Value::SmallInt(2));

    // Set individual value
    storage.set_value(0, 1, Value::SmallInt(42));
    assert_eq!(storage.get_value(0, 1), &Value::SmallInt(42));

    // Other values unchanged
    assert_eq!(storage.get_value(0, 0), &Value::SmallInt(1));
    assert_eq!(storage.get_value(0, 2), &Value::SmallInt(3));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bulk_storage_push_state_iter() {
    let mut storage = BulkStateStorage::new(3, 10);
    let values = vec![Value::Bool(true), Value::SmallInt(42), Value::Bool(false)];
    let idx = storage.push_state_iter(values);

    assert_eq!(idx, 0);
    assert_eq!(storage.get_state(0)[0], Value::Bool(true));
    assert_eq!(storage.get_state(0)[1], Value::SmallInt(42));
    assert_eq!(storage.get_state(0)[2], Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bulk_storage_memory_efficiency() {
    // Compare memory: 100K states with 5 vars each
    let num_states = 100_000;
    let vars_per_state = 5;

    let mut storage = BulkStateStorage::new(vars_per_state, num_states);

    // Add states
    for i in 0..num_states {
        let values: Vec<Value> = (0..vars_per_state)
            .map(|v| Value::SmallInt((i * vars_per_state + v) as i64))
            .collect();
        storage.push_state(&values);
    }

    assert_eq!(storage.len(), num_states);

    // Memory should be roughly: num_states * vars_per_state * size_of::<Value>()
    // Plus fingerprint storage
    let expected_values_mem = num_states * vars_per_state * std::mem::size_of::<Value>();
    let actual_mem = storage.memory_usage();

    // Actual should be close to expected (within 2x for overhead)
    assert!(
        actual_mem <= expected_values_mem * 2,
        "Memory usage {} should be <= {} (2x expected)",
        actual_mem,
        expected_values_mem * 2
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bulk_storage_empty() {
    let storage = BulkStateStorage::empty(5);
    assert!(storage.is_empty());
    assert_eq!(storage.len(), 0);
    assert_eq!(storage.vars_per_state(), 5);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bulk_storage_from_states() {
    use crate::state::State;
    use crate::var_index::VarRegistry;

    let registry = VarRegistry::from_names(["x", "y"]);

    let states = vec![
        State::from_pairs([("x", Value::SmallInt(1)), ("y", Value::SmallInt(10))]),
        State::from_pairs([("x", Value::SmallInt(2)), ("y", Value::SmallInt(20))]),
        State::from_pairs([("x", Value::SmallInt(3)), ("y", Value::SmallInt(30))]),
    ];

    let storage = BulkStateStorage::from_states(&states, &registry);

    assert_eq!(storage.len(), 3);
    assert_eq!(storage.vars_per_state(), 2);

    // Check values are correct
    assert_eq!(storage.get_state(0)[0], Value::SmallInt(1));
    assert_eq!(storage.get_state(0)[1], Value::SmallInt(10));
    assert_eq!(storage.get_state(1)[0], Value::SmallInt(2));
    assert_eq!(storage.get_state(1)[1], Value::SmallInt(20));
    assert_eq!(storage.get_state(2)[0], Value::SmallInt(3));
    assert_eq!(storage.get_state(2)[1], Value::SmallInt(30));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bulk_storage_fingerprints() {
    use crate::state::{ArrayState, State};
    use crate::var_index::VarRegistry;

    let registry = VarRegistry::from_names(["a", "b"]);

    let state = State::from_pairs([("a", Value::SmallInt(42)), ("b", Value::Bool(true))]);

    // Create bulk storage entry
    let mut storage = BulkStateStorage::new(2, 10);
    let idx = storage.push_from_state(&state, &registry);

    // Compute fingerprint
    let bulk_fp = storage.fingerprint(idx, &registry);

    // Compare with ArrayState fingerprint
    let mut array_state = ArrayState::from_state(&state, &registry);
    let array_fp = array_state.fingerprint(&registry);

    assert_eq!(
        bulk_fp, array_fp,
        "BulkStateStorage fingerprint should match ArrayState fingerprint"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bulk_storage_to_array_state() {
    use crate::state::State;
    use crate::var_index::VarRegistry;

    let registry = VarRegistry::from_names(["x", "y"]);

    let state = State::from_pairs([("x", Value::SmallInt(100)), ("y", Value::Bool(false))]);

    let mut storage = BulkStateStorage::new(2, 10);
    storage.push_from_state(&state, &registry);

    // Convert back to ArrayState
    let array_state = storage.to_array_state(0);

    assert_eq!(array_state.get(VarIndex::new(0)), Value::SmallInt(100));
    assert_eq!(array_state.get(VarIndex::new(1)), Value::Bool(false));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_bulk_state_handle() {
    use crate::state::Fingerprint;

    let handle1 = BulkStateHandle::new(0);
    assert_eq!(handle1.index, 0);
    assert_eq!(handle1.fingerprint, None);

    let fp = Fingerprint(0x1234567890abcdef);
    let handle2 = BulkStateHandle::with_fingerprint(42, fp);
    assert_eq!(handle2.index, 42);
    assert_eq!(handle2.fingerprint, Some(fp));
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_and_state_sizes() {
    use crate::state::ArrayState;
    use std::mem::size_of;

    let value_size = size_of::<Value>();
    let array_state_size = size_of::<ArrayState>();
    let box_slice_size = size_of::<Box<[Value]>>();

    // Print sizes for reference
    println!("Size of Value: {} bytes", value_size);
    println!("Size of ArrayState: {} bytes", array_state_size);
    println!("Size of Box<[Value]>: {} bytes", box_slice_size);

    // Value size reduced from 96 → 56 bytes by Arc-wrapping large variants
    // (Int, Interval, Func, IntFunc, Seq, Closure) in #3168.
    assert!(
        value_size <= 64,
        "Value size {} exceeds expected maximum (56 bytes after Arc-wrapping)",
        value_size
    );

    // For 5 variables per state at 72 bytes each = 360 bytes data
    // Plus ArrayState overhead (fp_cache, Box pointer)
    let vars_per_state = 5;
    let expected_data_per_state = vars_per_state * value_size;

    // With Box<[Value]>: 16 bytes pointer + data
    // Plus fp_cache Option: ~40 bytes
    let expected_total = expected_data_per_state + box_slice_size + 48; // approximate fp_cache

    println!(
        "For {} vars/state: ~{} bytes data, ~{} bytes total per ArrayState",
        vars_per_state, expected_data_per_state, expected_total
    );

    // BulkStateStorage should be more efficient
    let mut bulk = BulkStateStorage::new(vars_per_state, 1000);
    for i in 0..1000 {
        let values: Vec<Value> = (0..vars_per_state)
            .map(|v| Value::SmallInt((i * vars_per_state + v) as i64))
            .collect();
        bulk.push_state(&values);
    }

    let bulk_per_state = bulk.memory_usage() / 1000;
    println!(
        "BulkStateStorage: {} bytes/state (vs ~{} for ArrayState)",
        bulk_per_state, expected_total
    );

    // Bulk storage should use less memory per state than individual ArrayStates
    // (no Box overhead per state, no fp_cache per state)
    assert!(
        bulk_per_state <= expected_total,
        "Bulk storage {} should be <= ArrayState {}",
        bulk_per_state,
        expected_total
    );
}

/// Regression test for #1729: push_from_state must panic when a registry
/// variable is missing from the State, not silently default to Bool(false).
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[should_panic(expected = "state missing variable")]
fn test_1729_push_from_state_panics_on_missing_var() {
    use crate::state::State;
    use crate::var_index::VarRegistry;

    let registry = VarRegistry::from_names(["x", "y"]);
    // State only has "x", missing "y"
    let state = State::from_pairs([("x", Value::SmallInt(1))]);

    let mut storage = BulkStateStorage::new(2, 10);
    storage.push_from_state(&state, &registry); // should panic
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[should_panic(expected = "index overflow")]
fn test_bulk_storage_push_state_panics_at_u32_max() {
    let mut storage = BulkStateStorage::empty(1);
    storage.num_states = u32::MAX as usize;
    storage.push_state(&[Value::SmallInt(1)]);
}

#[cfg(target_pointer_width = "64")]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
#[should_panic(expected = "count overflow")]
fn test_bulk_storage_handles_panics_when_count_exceeds_u32_max() {
    let mut storage = BulkStateStorage::empty(1);
    storage.num_states = (u32::MAX as usize) + 1;
    let _ = storage.handles().next();
}

/// Exercises fallback arena allocation tracking and reset.
/// Part of #2957: integration test required pub re-export of StateArena.
#[cfg(not(feature = "bumpalo"))]
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_fallback_arena_tracks_allocations_and_resets_counters() {
    let mut arena = StateArena::with_capacity(8);

    let slice = arena.alloc_slice(&[Value::SmallInt(1), Value::SmallInt(2)]);
    assert_eq!(slice, &[Value::SmallInt(1), Value::SmallInt(2)]);

    let vec_slice = arena.alloc_vec(vec![Value::Bool(true)]);
    assert_eq!(vec_slice, &[Value::Bool(true)]);

    assert_eq!(arena.chunk_capacity(), 0);
    assert!(arena.allocated_bytes() > 0);
    assert_eq!(arena.allocation_count(), 2);

    arena.reset();
    assert_eq!(arena.allocated_bytes(), 0);
    assert_eq!(arena.allocation_count(), 0);
}
