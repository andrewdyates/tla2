// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Value interner and handle state tests.

use super::*;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_value_handle_copy() {
    let handle = ValueHandle(42);
    let copy = handle; // Copy, not move
    assert_eq!(handle, copy);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interner_basic() {
    let interner = ValueInterner::new();

    let v1 = Value::SmallInt(42);
    let v2 = Value::SmallInt(42);
    let v3 = Value::SmallInt(100);

    let h1 = interner.intern(v1);
    let h2 = interner.intern(v2);
    let h3 = interner.intern(v3);

    // Same value = same handle
    assert_eq!(h1, h2);
    // Different value = different handle
    assert_ne!(h1, h3);

    // Can retrieve values
    assert_eq!(
        interner
            .try_get(h1)
            .expect("first handle should still be interned"),
        Value::SmallInt(42)
    );
    assert_eq!(
        interner
            .try_get(h3)
            .expect("third handle should still be interned"),
        Value::SmallInt(100)
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interner_try_get_returns_error_after_clear() {
    let interner = ValueInterner::new();
    let handle = interner.intern(Value::SmallInt(42));

    interner.clear();

    let err = interner
        .try_get(handle)
        .expect_err("clearing the interner must invalidate existing handles");
    assert_eq!(err.handle(), handle);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_handle_state_materialize_returns_error_after_clear() {
    use crate::var_index::VarRegistry;

    let interner = ValueInterner::new();
    let registry = VarRegistry::from_names(["x"]);
    let state = HandleState::from_values(&[Value::SmallInt(7)], &registry, &interner);

    interner.clear();

    let err = state
        .materialize(&interner)
        .expect_err("materializing a stale handle state should report a miss");
    assert_eq!(err.handle(), state.handles()[0]);
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_handle_state_clone_is_fast() {
    use crate::state::Fingerprint;
    // Create a HandleState
    let handles = vec![ValueHandle(1), ValueHandle(2), ValueHandle(3)];
    let state = HandleState::new(handles.into_boxed_slice(), Fingerprint(12345));

    // Clone should be fast (memcpy)
    let cloned = state.clone();
    assert_eq!(state.fingerprint(), cloned.fingerprint());
    assert_eq!(state.handles(), cloned.handles());
}

/// Part of #3212: Verify owner-local interner bank routing.
///
/// Creates a 2-shard bank, builds a HandleState from worker 1's shard,
/// then materializes it (as if consumed by a different worker). The values
/// must round-trip correctly and the fingerprint must remain unchanged.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_interner_bank_cross_worker_materialize() {
    use crate::var_index::VarRegistry;

    let bank = HandleStateInternerBank::new(2);
    let registry = VarRegistry::from_names(["x", "y", "z"]);

    let values = vec![
        Value::SmallInt(10),
        Value::SmallInt(20),
        Value::SmallInt(30),
    ];

    // Produce state on worker 1's shard.
    let state = HandleState::from_values_sharded(&values, &registry, &bank, 1);
    assert_eq!(state.owner_worker(), 1);

    let fp_before = state.fingerprint();

    // Materialize from the bank (simulates a different worker consuming
    // a stolen work item — it reads from shard 1 via owner_worker).
    let materialized = state
        .materialize_from_bank(&bank)
        .expect("materialization should succeed while shard contents are present");

    assert_eq!(
        materialized, values,
        "values must round-trip through owner shard"
    );
    assert_eq!(state.fingerprint(), fp_before, "fingerprint must be stable");

    // Verify shard isolation: shard 0 should NOT contain these values.
    let shard0 = bank.shard(0);
    assert!(
        shard0.is_empty(),
        "shard 0 should be empty (values interned on shard 1)"
    );
    let shard1 = bank.shard(1);
    assert_eq!(shard1.len(), 3, "shard 1 should contain 3 interned values");
}

/// Part of #3213: Verify in-place materialization into an existing ArrayState.
///
/// `materialize_into_bank` writes interner lookups directly into a
/// caller-owned scratch buffer, avoiding the Vec allocation of
/// `materialize_from_bank`.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_materialize_into_bank_round_trips() {
    use crate::state::ArrayState;
    use crate::var_index::VarRegistry;

    let bank = HandleStateInternerBank::new(2);
    let registry = VarRegistry::from_names(["a", "b"]);

    let values = vec![Value::SmallInt(100), Value::SmallInt(200)];

    // Build a HandleState on shard 0.
    let hs = HandleState::from_values_sharded(&values, &registry, &bank, 0);

    // Allocate a scratch ArrayState with dummy values.
    let mut scratch = ArrayState::from_values(vec![Value::SmallInt(0), Value::SmallInt(0)]);

    // In-place decode.
    hs.materialize_into_bank(&mut scratch, &bank)
        .expect("in-place materialize must succeed");

    // Verify round-trip.
    assert_eq!(
        scratch.get(crate::var_index::VarIndex::new(0)),
        Value::SmallInt(100),
        "slot 0 must contain 100 after in-place decode"
    );
    assert_eq!(
        scratch.get(crate::var_index::VarIndex::new(1)),
        Value::SmallInt(200),
        "slot 1 must contain 200 after in-place decode"
    );
}
