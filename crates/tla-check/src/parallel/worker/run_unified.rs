// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parallel BFS worker entry point.
//!
//! Part of #2356 Phase 4 Step 4d: the BFS loop body is now in
//! `bfs::worker_loop::run_bfs_worker`. This module provides the entry point
//! that initializes the worker context, constructs `ParallelTransport`, and
//! delegates to the unified loop — matching TLC's single `Worker.run()`.
//!
//! Previously contained a ~270-line inline BFS loop; now reduced to worker
//! initialization + transport construction + unified loop call.

use super::helpers::init_worker_ctx;
use super::transport::shared_queue::{SharedFrontier, SharedQueueTransport};
use super::transport::ParallelTransport;
use super::work_item::BfsWorkItem;
use super::{WorkerModelConfig, WorkerPanicGuard, WorkerSharedState};
use crate::arena::init_worker_arena;
use crate::check::model_checker::bfs::transport::BfsWorkerConfig;
use crate::check::model_checker::bfs::worker_loop::run_bfs_worker;
use crate::eval::set_eval_worker_count;
use crate::parallel::WorkerStats;
use crossbeam_deque::{Injector, Stealer, Worker};
use std::sync::Arc;
use tla_eval::eval_arena::init_thread_arena;

/// Unified BFS worker entry point, generic over work item type.
///
/// Handles both `ArrayState` (standard) and `HandleState` (interning-optimized)
/// work items through the [`BfsWorkItem`] trait.
///
/// Initializes the worker evaluation context, constructs a
/// [`ParallelTransport`], and delegates to [`run_bfs_worker`] — the single
/// BFS loop body shared with sequential mode.
///
/// Part of #2356 Phase 4 Step 4d.
pub(in crate::parallel) fn run_worker_unified<T: BfsWorkItem>(
    worker_id: usize,
    local_queue: Worker<(T, usize)>,
    injector: Arc<Injector<(T, usize)>>,
    stealers: Arc<Vec<Stealer<(T, usize)>>>,
    frontier: Arc<SharedFrontier<T>>,
    shared: WorkerSharedState,
    model: WorkerModelConfig,
    mode: T::Mode,
) {
    // Extract values needed before shared/model are consumed by ParallelTransport.
    let stop_flag = shared.stop_flag.clone();
    let result_tx = shared.result_tx.clone();
    let num_workers = model.num_workers;
    let max_depth_limit = model.max_depth_limit;

    let mut stats = WorkerStats {
        worker_id: Some(worker_id),
        ..WorkerStats::default()
    };
    let ctx = match init_worker_ctx(&model, &stop_flag, &result_tx, &mut stats) {
        Ok(ctx) => ctx,
        Err(()) => return,
    };
    set_eval_worker_count(num_workers);

    // Part of #3285: Install worker-local value intern scope. The guard drops
    // on worker exit, clearing the thread-local overlay. This routes
    // intern_set_array() and intern_int_func_array() through the frozen
    // snapshot + local overlay instead of the global DashMap.
    let _intern_guard = tla_value::WorkerInternGuard::new();

    // Part of #3580: Initialize per-worker eval arena for bump allocation.
    init_thread_arena();

    // Part of #3990: Initialize per-worker state arena for successor allocation.
    init_worker_arena();

    // Part of #1824: set stop_flag on panic to prevent termination detection
    // corruption from unflushed local_work_delta.
    let _panic_guard = WorkerPanicGuard::new(&stop_flag);

    let config = BfsWorkerConfig {
        max_depth: max_depth_limit,
    };
    // Part of #3212: pass worker_id so ParallelTransport can thread it
    // into from_array_state for owner-local interner sharding.
    let mut transport = ParallelTransport::new(
        worker_id,
        local_queue,
        injector,
        stealers,
        frontier,
        ctx,
        shared,
        model,
        mode,
    );

    // The unified BFS loop — same function called by sequential mode with
    // SequentialTransport. The BfsLoopOutcome return value is unused for
    // parallel workers (results are sent via channel in ParallelTransport).
    let _ = run_bfs_worker(&mut transport, &config, None);
}

/// Shared-queue BFS worker entry point (Part of #3258).
///
/// Same initialization as `run_worker_unified` but constructs a
/// [`SharedQueueTransport`] instead of [`ParallelTransport`]. Workers share
/// a single [`SharedFrontier`] FIFO instead of per-worker deques.
pub(in crate::parallel) fn run_worker_shared_queue<T: BfsWorkItem>(
    worker_id: usize,
    frontier: Arc<SharedFrontier<T>>,
    shared: WorkerSharedState,
    model: WorkerModelConfig,
    mode: T::Mode,
) {
    let stop_flag = shared.stop_flag.clone();
    let result_tx = shared.result_tx.clone();
    let num_workers = model.num_workers;
    let max_depth_limit = model.max_depth_limit;

    let mut stats = WorkerStats {
        worker_id: Some(worker_id),
        ..WorkerStats::default()
    };
    let ctx = match init_worker_ctx(&model, &stop_flag, &result_tx, &mut stats) {
        Ok(ctx) => ctx,
        Err(()) => return,
    };
    set_eval_worker_count(num_workers);

    // Part of #3285: Install worker-local value intern scope (same as work-stealing path).
    let _intern_guard = tla_value::WorkerInternGuard::new();

    // Part of #3580: Initialize per-worker eval arena for bump allocation.
    init_thread_arena();

    // Part of #3990: Initialize per-worker state arena for successor allocation.
    init_worker_arena();

    let _panic_guard = WorkerPanicGuard::new(&stop_flag);

    let config = BfsWorkerConfig {
        max_depth: max_depth_limit,
    };

    let mut transport = SharedQueueTransport::new(worker_id, frontier, ctx, shared, model, mode);

    let _ = run_bfs_worker(&mut transport, &config, None);
}
