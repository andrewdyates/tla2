// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::WORK_BATCH_SIZE;
use super::coordination::record_state_completion;
use super::work_item::ResolvedArrayState;
use super::{BfsWorkItem, HandleStateMode};
use crate::intern::{HandleState, HandleStateInternerBank};
use crate::state::ArrayState;
use crate::var_index::VarRegistry;
use crate::Value;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

/// Part of #3212: a stolen HandleState must materialize from its owner's
/// shard, but any successor enqueued by the stealing worker must move to
/// the new producer's shard.
#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_handle_state_reenqueue_moves_to_new_producer_shard() {
    let bank = Arc::new(HandleStateInternerBank::new(2));
    let registry = VarRegistry::from_names(["x", "y"]);
    let mode = HandleStateMode {
        interner_bank: Arc::clone(&bank),
    };

    let original_values = vec![Value::SmallInt(10), Value::SmallInt(20)];
    let stolen_state = HandleState::from_values_sharded(&original_values, &registry, &bank, 0);
    assert_eq!(stolen_state.owner_worker(), 0);

    let mut scratch = ArrayState::new(registry.len());
    let resolved = <HandleState as BfsWorkItem>::resolve_array_state(
        stolen_state,
        Some(&mut scratch),
        &registry,
        &mode,
    );
    assert!(matches!(resolved, ResolvedArrayState::UsedScratch));
    assert_eq!(scratch.materialize_values(), original_values);

    let successor_values = vec![Value::SmallInt(11), Value::SmallInt(21)];
    let successor_array = ArrayState::from_values(successor_values.clone());
    let successor_state =
        <HandleState as BfsWorkItem>::from_array_state(successor_array, &registry, &mode, 1);
    assert_eq!(successor_state.owner_worker(), 1);
    assert_eq!(
        successor_state
            .materialize_from_bank(&bank)
            .expect("materialization should succeed while shard contents are present"),
        successor_values,
        "re-enqueued successor must round-trip through the new producer shard"
    );

    assert_eq!(
        bank.shard(0).len(),
        2,
        "original owner shard should retain only the stolen state's values"
    );
    assert_eq!(
        bank.shard(1).len(),
        2,
        "stealing worker shard should receive the re-enqueued successor"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_handle_state_resolve_reuses_caller_scratch_allocation() {
    let bank = Arc::new(HandleStateInternerBank::new(1));
    let registry = VarRegistry::from_names(["x", "y"]);
    let mode = HandleStateMode {
        interner_bank: Arc::clone(&bank),
    };

    let mut scratch = ArrayState::new(registry.len());
    let scratch_ptr = scratch.values().as_ptr();

    for values in [
        [Value::SmallInt(1), Value::SmallInt(2)],
        [Value::SmallInt(3), Value::SmallInt(4)],
    ] {
        let state = HandleState::from_values_sharded(&values, &registry, &bank, 0);
        let resolved = <HandleState as BfsWorkItem>::resolve_array_state(
            state,
            Some(&mut scratch),
            &registry,
            &mode,
        );
        assert!(matches!(resolved, ResolvedArrayState::UsedScratch));
        assert_eq!(scratch.materialize_values(), values);
        assert_eq!(
            scratch.values().as_ptr(),
            scratch_ptr,
            "HandleState decode should reuse the caller-provided ArrayState allocation"
        );
    }
}

#[test]
fn test_record_state_completion_keeps_positive_delta_batched() {
    let work_remaining = AtomicUsize::new(11);
    let mut delta = 4;

    record_state_completion(&mut delta, &work_remaining);

    assert_eq!(
        delta, 3,
        "productive completion should keep positive work batched"
    );
    assert_eq!(
        work_remaining.load(Ordering::Acquire),
        11,
        "per-state completion should not flush shared work_remaining on productive runs"
    );
}

#[test]
fn test_record_state_completion_preserves_negative_batch_flush() {
    let work_remaining = AtomicUsize::new(512);
    let mut delta = -((WORK_BATCH_SIZE as isize) - 1);

    record_state_completion(&mut delta, &work_remaining);

    assert_eq!(
        delta, 0,
        "negative batch should flush once the threshold is crossed"
    );
    assert_eq!(
        work_remaining.load(Ordering::Acquire),
        256,
        "state completion must still flush large negative batches to keep work_remaining accurate"
    );
}
