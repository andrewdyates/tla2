// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for `try_dequeue` — idle detection, flush semantics, and barrier interaction.

use super::helpers::{build_array_transport_via_new, build_array_transport_with_result_rx};
use crate::check::model_checker::bfs::transport::BfsTransport;
use crate::parallel::WorkerResult;
use crate::state::ArrayState;
use crate::var_index::VarRegistry;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::thread;
use std::time::Duration;

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_try_dequeue_stays_active_when_replacement_work_is_immediately_visible() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let mut transport = build_array_transport_via_new(0, 1, registry);
    transport.worker_active = true;
    transport.active_workers.store(1, Ordering::Release);
    transport.local_work_delta = 1;
    transport.injector.push((ArrayState::new(0), 0));

    let dequeued = transport.try_dequeue();

    assert!(
        dequeued.is_some(),
        "visible injector work should still be dequeued when the local queue is empty"
    );
    assert_eq!(
        transport.work_remaining.load(Ordering::Acquire),
        0,
        "short empty streaks should not flush the local work delta before replacement work arrives"
    );
    assert_eq!(
        transport.local_work_delta, 1,
        "replacement work found on the first probe should keep the worker on the active fast path"
    );
    assert_eq!(
        transport.active_workers.load(Ordering::Acquire),
        1,
        "the worker should stay active across a transient local-queue miss"
    );
    assert_eq!(
        transport.stats.active_worker_deactivations, 0,
        "transient misses should not churn the active_workers counter"
    );
    assert_eq!(
        transport.stats.active_worker_activations, 0,
        "a worker that never went idle should not record a spurious reactivation"
    );
    assert_eq!(
        transport.stats.work_remaining_cas_retries, 0,
        "no contention is expected in this single-threaded retry counter test"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_try_dequeue_non_diff_path_flushes_pending_work_before_steal() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let mut transport = build_array_transport_via_new(0, 1, registry);
    transport.use_diffs = false;
    transport.worker_active = true;
    transport.active_workers.store(1, Ordering::Release);
    transport.local_work_delta = 1;
    transport.injector.push((ArrayState::new(0), 0));

    let dequeued = transport.try_dequeue();

    assert!(
        dequeued.is_some(),
        "non-diff full-state specs should still steal visible replacement work"
    );
    assert_eq!(
        transport.work_remaining.load(Ordering::Acquire),
        1,
        "non-diff full-state paths should publish pending discovered work before entering the steal loop"
    );
    assert_eq!(
        transport.local_work_delta, 0,
        "publishing the full-state idle transition should clear the local work delta"
    );
    assert_eq!(
        transport.active_workers.load(Ordering::Acquire),
        1,
        "the worker should reactivate after stealing the visible replacement work"
    );
    assert_eq!(
        transport.stats.active_worker_deactivations, 1,
        "the full-state path should record the eager idle transition before polling"
    );
    assert_eq!(
        transport.stats.active_worker_activations, 1,
        "stealing replacement work should bring the worker back into the active set"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_try_dequeue_marks_worker_idle_after_repeated_empty_polls() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let (mut transport, result_rx) = build_array_transport_with_result_rx(0, 1, registry);
    transport.worker_active = true;
    transport.active_workers.store(1, Ordering::Release);

    let dequeued = transport.try_dequeue();

    assert!(
        dequeued.is_none(),
        "a worker with no visible work should eventually terminate after the idle hysteresis expires"
    );
    assert_eq!(
        transport.active_workers.load(Ordering::Acquire),
        0,
        "repeated empty polls must still drop the worker out of active_workers"
    );
    assert!(
        !transport.worker_active,
        "terminating on confirmed idleness must leave the worker flagged idle"
    );
    // Note: send_done_result() calls std::mem::take(stats), moving the
    // accumulated counters into WorkerResult::Done and zeroing the
    // transport-local copy. Check the done result for deactivation counts.
    match result_rx.try_recv() {
        Ok(WorkerResult::Done(done_stats)) => {
            assert_eq!(
                done_stats.active_worker_deactivations, 1,
                "confirmed idleness should publish exactly one deactivation"
            );
            assert_eq!(
                done_stats.active_worker_activations, 0,
                "no replacement work was found, so the worker should stay idle"
            );
        }
        Ok(other) => panic!("expected Done result after empty termination, got {other:?}"),
        Err(err) => panic!("expected Done result after empty termination: {err}"),
    }
    assert!(
        result_rx.try_recv().is_err(),
        "termination should publish exactly one Done result"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_try_dequeue_flushes_local_work_before_barrier_wait() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let mut transport = build_array_transport_via_new(0, 1, registry);
    transport.worker_active = true;
    transport.active_workers.store(1, Ordering::Release);
    transport.local_work_delta = 2;
    transport.local_queue.push((ArrayState::new(0), 0));

    let barrier = Arc::clone(&transport.barrier);
    let work_remaining = Arc::clone(&transport.work_remaining);
    let helper = thread::spawn(move || {
        barrier.suspend_all();
        assert_eq!(
            work_remaining.load(Ordering::Acquire),
            2,
            "workers must flush batched work before parking at the pause barrier"
        );
        barrier.resume_all();
    });

    for _ in 0..100 {
        if transport.barrier.is_pause_requested() {
            break;
        }
        thread::sleep(Duration::from_millis(1));
    }
    assert!(
        transport.barrier.is_pause_requested(),
        "test setup must request the pause barrier before try_dequeue runs"
    );

    let dequeued = transport.try_dequeue();
    helper
        .join()
        .expect("barrier helper thread should complete");

    assert!(
        dequeued.is_some(),
        "worker should resume and return the local item after the barrier releases"
    );
    assert_eq!(
        transport.local_work_delta, 0,
        "barrier path should flush the outstanding local batch"
    );
}

#[cfg_attr(test, ntest::timeout(10000))]
#[test]
fn test_try_dequeue_stop_flushes_local_work_before_returning() {
    let registry = Arc::new(VarRegistry::from_names(["x"]));
    let (mut transport, _result_rx) = build_array_transport_with_result_rx(0, 1, registry);
    transport.worker_active = true;
    transport.active_workers.store(1, Ordering::Release);
    transport.local_work_delta = 2;
    transport.local_queue.push((ArrayState::new(0), 0));
    transport.stop_flag.store(true, Ordering::SeqCst);

    let dequeued = transport.try_dequeue();

    assert!(
        dequeued.is_none(),
        "stop requests should terminate dequeuing immediately"
    );
    assert_eq!(
        transport.work_remaining.load(Ordering::Acquire),
        2,
        "stop path should flush the outstanding local batch before returning"
    );
    assert_eq!(
        transport.local_work_delta, 0,
        "stop-path flush should clear the worker-local work delta"
    );
}
