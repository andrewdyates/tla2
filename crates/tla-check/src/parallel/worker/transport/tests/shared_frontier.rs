// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared frontier tail promotion, publish, enqueue, and dequeue tests.

use super::super::shared_queue::SHARED_QUEUE_BATCH_SIZE;
use super::super::ParallelTransport;
use super::helpers::build_array_transport_via_new;
use crate::check::model_checker::bfs::transport::BfsTransport;
use crate::state::ArrayState;
use crate::var_index::VarRegistry;
use smallvec::SmallVec;
use std::cell::{Cell, RefCell};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

#[test]
fn test_shared_frontier_tail_promotion_ignores_bootstrap_budget_after_persistent_underfill() {
    let budget = AtomicUsize::new(1);
    let active_workers = AtomicUsize::new(3);

    assert!(
        super::super::super::work_stealing::should_promote_shared_frontier_tail(
            &budget,
            false,
            &active_workers,
            4,
            super::super::super::BACKOFF_YIELD_THRESHOLD,
        ),
        "persistent underfill should allow tail promotion even before the bootstrap budget reaches zero"
    );
}

#[test]
fn test_shared_frontier_tail_promotion_disabled_when_depth_limited() {
    let budget = AtomicUsize::new(0);
    let active_workers = AtomicUsize::new(0);

    assert!(
        !super::super::super::work_stealing::should_promote_shared_frontier_tail(
            &budget,
            true,
            &active_workers,
            4,
            super::super::super::BACKOFF_YIELD_THRESHOLD,
        ),
        "bounded-depth runs must keep the existing work-stealing path unchanged"
    );
}

#[test]
fn test_shared_frontier_tail_promotion_stays_off_while_all_workers_active() {
    let budget = AtomicUsize::new(1);
    let active_workers = AtomicUsize::new(4);

    assert!(
        !super::super::super::work_stealing::should_promote_shared_frontier_tail(
            &budget,
            false,
            &active_workers,
            4,
            super::super::super::BACKOFF_YIELD_THRESHOLD,
        ),
        "bootstrap-aware tail promotion still requires proof that at least one worker is truly underfilled"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_shared_frontier_tail_publish_drains_local_queue_before_blocking() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let mut transport = build_array_transport_via_new(0, 2, registry);
    transport
        .shared_frontier_tail_mode
        .store(true, Ordering::Release);
    transport.local_queue.push((ArrayState::new(0), 7));
    transport.local_queue.push((ArrayState::new(0), 9));

    transport.ensure_shared_frontier_tail_published();

    assert!(
        transport.local_queue.pop().is_none(),
        "promotion should publish hidden local work before any shared-frontier wait path"
    );

    let mut batch: SmallVec<[(ArrayState, usize); SHARED_QUEUE_BATCH_SIZE]> = SmallVec::new();
    let outcome = transport.shared_frontier.dequeue_batch_blocking(
        &mut batch,
        SHARED_QUEUE_BATCH_SIZE,
        &transport.stop_flag,
    );
    assert_eq!(
        outcome,
        super::super::shared_queue::DequeueOutcome::Refilled
    );
    assert_eq!(
        batch
            .into_iter()
            .map(|(_, depth)| depth)
            .collect::<Vec<_>>(),
        vec![7, 9],
        "promotion should move the worker-local deque to the shared frontier in FIFO order"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_shared_frontier_tail_publish_drains_visible_injector_work() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let mut transport = build_array_transport_via_new(0, 2, registry);
    transport
        .shared_frontier_tail_mode
        .store(true, Ordering::Release);
    transport.injector.push((ArrayState::new(0), 11));

    transport.ensure_shared_frontier_tail_published();

    assert!(
        transport.injector.steal().success().is_none(),
        "promotion should opportunistically publish injector-visible work to the shared frontier"
    );

    let mut batch: SmallVec<[(ArrayState, usize); SHARED_QUEUE_BATCH_SIZE]> = SmallVec::new();
    let outcome = transport.shared_frontier.dequeue_batch_blocking(
        &mut batch,
        SHARED_QUEUE_BATCH_SIZE,
        &transport.stop_flag,
    );
    assert_eq!(
        outcome,
        super::super::shared_queue::DequeueOutcome::Refilled
    );
    assert_eq!(
        batch.pop().map(|(_, depth)| depth),
        Some(11),
        "promotion should move injector-visible work into the shared frontier"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_shared_frontier_tail_enqueue_bypasses_local_queue_and_injector() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let transport = build_array_transport_via_new(0, 2, registry);
    transport
        .shared_frontier_tail_mode
        .store(true, Ordering::Release);
    let route_to_injector = super::super::route_successor_batch_to_injector(
        &transport.bootstrap_injector_budget,
        transport.depth_limited,
        transport.active_workers.as_ref(),
        transport.num_workers,
    );
    let frontier_batch: RefCell<SmallVec<[(ArrayState, usize); SHARED_QUEUE_BATCH_SIZE]>> =
        RefCell::new(SmallVec::new());
    let injector_pushes = Cell::new(0usize);
    let enqueue_route = ParallelTransport::successor_batch_route(
        transport.shared_frontier_tail_mode_active(),
        &transport.shared_frontier,
        &transport.local_queue,
        &transport.injector,
        route_to_injector,
        &frontier_batch,
        &injector_pushes,
    );

    enqueue_route.enqueue(ArrayState::new(0), 13);
    enqueue_route.finish();

    assert!(
        transport.local_queue.pop().is_none(),
        "shared-frontier tail mode must stop queueing late-tail work on the local deque"
    );
    assert!(
        transport.injector.steal().success().is_none(),
        "shared-frontier tail mode must bypass the injector entirely"
    );

    let mut batch: SmallVec<[(ArrayState, usize); SHARED_QUEUE_BATCH_SIZE]> = SmallVec::new();
    let outcome = transport.shared_frontier.dequeue_batch_blocking(
        &mut batch,
        SHARED_QUEUE_BATCH_SIZE,
        &transport.stop_flag,
    );
    assert_eq!(
        outcome,
        super::super::shared_queue::DequeueOutcome::Refilled
    );
    assert_eq!(
        batch.pop().map(|(_, depth)| depth),
        Some(13),
        "late-tail enqueue should be queue-owned once shared-frontier mode is active"
    );
    assert_eq!(
        injector_pushes.get(),
        0,
        "shared-frontier enqueue must not increment injector profiling counters"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_shared_frontier_tail_try_dequeue_does_not_fall_back_to_injector() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let mut transport = build_array_transport_via_new(0, 2, registry);
    transport
        .shared_frontier_tail_mode
        .store(true, Ordering::Release);
    transport.shared_frontier_tail_published = true;
    transport
        .shared_frontier
        .push_single(ArrayState::new(0), 17);
    transport.injector.push((ArrayState::new(0), 19));

    let dequeued = transport.try_dequeue();

    assert_eq!(
        dequeued.map(|(_, depth)| depth),
        Some(17),
        "once promoted, try_dequeue should read from the shared frontier instead of the steal/backoff path"
    );
    assert_eq!(
        transport.injector.steal().success().map(|(_, depth)| depth),
        Some(19),
        "shared-frontier dequeue should leave injector work untouched instead of falling back to steals"
    );
}
