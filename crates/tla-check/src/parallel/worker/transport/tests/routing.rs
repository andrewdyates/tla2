// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bootstrap injector budget, successor batch routing, and enqueue item tests.

use crate::state::ArrayState;
use crossbeam_deque::{Injector, Worker};
use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering};

#[test]
fn test_initial_bootstrap_injector_budget_only_enables_thin_initial_frontier() {
    assert_eq!(
        super::super::initial_bootstrap_injector_budget(1, 2),
        super::super::BOOTSTRAP_INJECTOR_BATCH_BUDGET,
        "single-initial-state startup should enable bootstrap sharing"
    );
    assert_eq!(
        super::super::initial_bootstrap_injector_budget(2, 2),
        0,
        "when each worker already owns one initial state, bootstrap sharing should stay off"
    );
    assert_eq!(
        super::super::initial_bootstrap_injector_budget(4, 2),
        0,
        "wide initial frontiers should keep the steady-state transport policy"
    );
    assert_eq!(
        super::super::initial_bootstrap_injector_budget(1, 1),
        0,
        "single-worker runs should not pay bootstrap injector overhead"
    );
}

#[test]
fn test_route_successor_batch_to_injector_consumes_bootstrap_budget() {
    let budget = AtomicUsize::new(2);
    let active_workers = AtomicUsize::new(4);

    assert!(
        super::super::route_successor_batch_to_injector(&budget, false, &active_workers, 4),
        "bootstrap sharing should still route the first batch through the injector"
    );
    assert_eq!(
        budget.load(Ordering::Relaxed),
        1,
        "bootstrap routing should consume one shared startup batch"
    );

    assert!(
        super::super::route_successor_batch_to_injector(&budget, false, &active_workers, 4),
        "bootstrap sharing should keep routing until the budget is exhausted"
    );
    assert_eq!(
        budget.load(Ordering::Relaxed),
        0,
        "bootstrap routing should stop once the shared budget is exhausted"
    );

    assert!(
        !super::super::route_successor_batch_to_injector(&budget, false, &active_workers, 4),
        "once bootstrap is exhausted and all workers are active, batches should stay local"
    );
}

#[test]
fn test_route_successor_batch_stays_local_when_all_workers_active_after_bootstrap() {
    let budget = AtomicUsize::new(0);
    let active_workers = AtomicUsize::new(4);

    assert!(
        !super::super::route_successor_batch_to_injector(&budget, false, &active_workers, 4),
        "steady-state batches should stay local while every worker is already active"
    );
}

#[test]
fn test_route_successor_batch_routes_to_injector_when_any_worker_is_idle() {
    let budget = AtomicUsize::new(0);
    let active_workers = AtomicUsize::new(3);

    assert!(
        super::super::route_successor_batch_to_injector(&budget, false, &active_workers, 4),
        "underfilled steady-state batches should route through the injector so idle workers can see work"
    );
}

/// Part of #3265: verify that depth_limited=true disables all injector routing.
#[test]
fn test_route_successor_batch_to_injector_disabled_when_depth_limited() {
    let budget = AtomicUsize::new(100);
    let active_workers = AtomicUsize::new(0);

    assert!(
        !super::super::route_successor_batch_to_injector(&budget, true, &active_workers, 4),
        "idle-aware routing should stay disabled while max-depth is active"
    );
    assert!(
        !super::super::route_successor_batch_to_injector(&budget, true, &active_workers, 4),
        "bootstrap routing should be suppressed when depth-limited"
    );
    assert_eq!(
        budget.load(Ordering::Relaxed),
        100,
        "bootstrap budget should not be consumed when depth-limited"
    );
}

#[test]
fn test_route_successor_batch_sampling_is_reused_for_entire_enqueue_batch() {
    let budget = AtomicUsize::new(0);
    let active_workers = AtomicUsize::new(3);
    let route_to_injector =
        super::super::route_successor_batch_to_injector(&budget, false, &active_workers, 4);
    let local_queue = Worker::new_fifo();
    let injector = Injector::new();
    let injector_pushes = Cell::new(0usize);

    active_workers.store(4, Ordering::Release);

    super::super::enqueue_successor_item(
        route_to_injector,
        ArrayState::new(0),
        7,
        &local_queue,
        &injector,
        &injector_pushes,
    );
    super::super::enqueue_successor_item(
        route_to_injector,
        ArrayState::new(0),
        9,
        &local_queue,
        &injector,
        &injector_pushes,
    );

    assert_eq!(
        injector_pushes.get(),
        2,
        "batch routing should reuse the sampled decision for every successor in the batch"
    );
    assert_eq!(
        injector.steal().success().map(|(_, depth)| depth),
        Some(7),
        "the first successor should keep the original batch route"
    );
    assert_eq!(
        injector.steal().success().map(|(_, depth)| depth),
        Some(9),
        "later successors in the same batch should not resample active_workers"
    );
    assert!(
        local_queue.pop().is_none(),
        "reusing the batch decision should keep the entire batch on one route"
    );
}

#[test]
fn test_enqueue_successor_item_counts_injector_pushes() {
    let local_queue = Worker::new_fifo();
    let injector = Injector::new();
    let injector_pushes = Cell::new(0usize);

    super::super::enqueue_successor_item(
        true,
        ArrayState::new(0),
        7,
        &local_queue,
        &injector,
        &injector_pushes,
    );
    assert_eq!(
        injector_pushes.get(),
        1,
        "injector-routed batches must increment the profiling counter"
    );
    assert_eq!(
        injector.steal().success().map(|(_, depth)| depth),
        Some(7),
        "injector-routed work should be visible on the global injector"
    );

    super::super::enqueue_successor_item(
        false,
        ArrayState::new(0),
        9,
        &local_queue,
        &injector,
        &injector_pushes,
    );
    assert_eq!(
        injector_pushes.get(),
        1,
        "local-queue routing must not increment injector profiling"
    );
    assert_eq!(
        local_queue.pop().map(|(_, depth)| depth),
        Some(9),
        "local routing should keep the work on the producer-local queue"
    );
}
