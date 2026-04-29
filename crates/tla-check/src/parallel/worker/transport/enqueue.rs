// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared enqueue policy helpers for parallel BFS transport.

use crossbeam_deque::{Injector, Worker};
use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Startup-only injector budget for thin initial frontiers.
///
/// Part of #3234: when `num_initial < num_workers`, let a bounded prefix of
/// early successor batches go through the global injector so idle workers can
/// claim frontier ownership instead of repeatedly stealing from worker 0.
pub(in crate::parallel::worker) const BOOTSTRAP_INJECTOR_BATCH_BUDGET: usize = 4096;

#[inline]
pub(in crate::parallel) fn initial_bootstrap_injector_budget(
    num_initial: usize,
    num_workers: usize,
) -> usize {
    if num_workers > 1 && num_initial < num_workers {
        BOOTSTRAP_INJECTOR_BATCH_BUDGET
    } else {
        0
    }
}

#[inline]
pub(super) fn route_successor_batch_to_injector(
    bootstrap_injector_budget: &AtomicUsize,
    depth_limited: bool,
    active_workers: &AtomicUsize,
    num_workers: usize,
) -> bool {
    // Part of #3265: When max_depth is active, disable cross-worker injection
    // entirely. Injector routing during depth-limited exploration can cause
    // states to be processed at inconsistent depths across workers, producing
    // incorrect state counts that diverge from sequential mode.
    if depth_limited {
        return false;
    }
    // Part of #3285: keep the startup bootstrap handoff, then widen the
    // frontier only when at least one worker is already idle. Call sites sample
    // this once per parent-state batch before building their enqueue closure.
    consume_bootstrap_injector_batch(bootstrap_injector_budget)
        || (num_workers > 1 && active_workers.load(Ordering::Acquire) < num_workers)
}

#[inline]
pub(super) fn enqueue_successor_item<T>(
    route_to_injector: bool,
    item: T,
    enq_depth: usize,
    local_queue: &Worker<(T, usize)>,
    injector: &Injector<(T, usize)>,
    injector_pushes: &Cell<usize>,
) {
    if route_to_injector {
        injector_pushes.set(injector_pushes.get() + 1);
        injector.push((item, enq_depth));
    } else {
        local_queue.push((item, enq_depth));
    }
}

#[inline]
fn consume_bootstrap_injector_batch(bootstrap_injector_budget: &AtomicUsize) -> bool {
    bootstrap_injector_budget
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |remaining| {
            remaining.checked_sub(1)
        })
        .is_ok()
}
