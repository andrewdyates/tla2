// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! BFS transport abstraction for unified loop execution.
//!
//! Part of #2356 Phase 4: abstracts the queue, termination, and coordination
//! mechanics so that one BFS loop body (`run_bfs_worker`) can serve both
//! sequential (1 worker, VecDeque, no sync) and parallel (N workers,
//! work-stealing, atomics) modes.
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────┐
//! │              run_bfs_worker (unified)            │
//! │  dequeue → limits → depth → process_successors  │
//! └──────────────────┬──────────────────────────────┘
//!                    │ BfsTransport trait
//!         ┌──────────┴──────────┐
//!         ▼                     ▼
//!  SequentialTransport    ParallelTransport
//!  (VecDeque, no sync)    (work-stealing, atomics)
//!         │                     │
//!         └──────────┬──────────┘
//!                    │ CoreStepAdapter trait
//!                    ▼
//!             run_core_step (unified)
//!    admit → invariant → violation → enqueue
//! ```
//!
//! `CoreStepAdapter` (Phase 1-3) handles the **inner** per-successor decision.
//! `BfsTransport` (Phase 4) handles the **outer** loop shell.
//! Together they eliminate the three-loop-body duplication that was the root
//! cause of #2355, #1931, #1799, and #1812.

use crate::check::{CheckError, CheckResult};
use crate::state::{ArrayState, Fingerprint};

/// Signal that the BFS loop should terminate early.
///
/// Separates sequential termination (returns a `CheckResult` to the caller)
/// from parallel termination (result already sent via channel — just exit).
///
/// `CheckResult` is boxed to keep the `Result<T, BfsTermination>` return type
/// compact (avoids `clippy::result_large_err`).
#[derive(Debug)]
pub(crate) enum BfsTermination {
    /// Terminate with a check result. Used by `SequentialTransport` where the
    /// caller (`run_bfs_loop`) needs the result to pass to `finish_check_after_bfs`.
    Result(Box<CheckResult>),
    /// Worker should exit silently. Used by `ParallelTransport` when the result
    /// has already been sent through the `WorkerResult` channel.
    Exit,
}

impl BfsTermination {
    /// Convenience constructor for the common sequential termination path.
    pub(crate) fn result(r: CheckResult) -> Self {
        Self::Result(Box::new(r))
    }
}

impl From<BfsTermination> for super::BfsLoopOutcome {
    fn from(t: BfsTermination) -> Self {
        match t {
            BfsTermination::Result(r) => super::BfsLoopOutcome::Terminated(r),
            // Parallel workers send results via channel before returning Exit.
            // Map to Complete so the (ignored) return type is valid.
            BfsTermination::Exit => super::BfsLoopOutcome::Complete {
                depth_limit_reached: false,
            },
        }
    }
}

/// Transport layer for BFS state exploration.
///
/// Abstracts the queue, termination, and coordination mechanics so that
/// one BFS loop body (`run_bfs_worker`) can serve both sequential (1 worker,
/// VecDeque, no sync) and parallel (N workers, work-stealing, atomics).
///
/// ## Relationship to CoreStepAdapter
///
/// [`CoreStepAdapter`](super::core_step::CoreStepAdapter) handles the **inner**
/// per-successor decision (admit → invariant → enqueue).
/// `BfsTransport` handles the **outer** loop shell (dequeue → limits → depth →
/// successor dispatch). Together they provide a single code path for all BFS
/// modes, matching TLC's single `Worker.run()`.
///
/// ## Design Choice: Trait vs Shared Synchronized Queue
///
/// TLC uses Java's `synchronized` keyword which has biased locking (near-zero
/// cost when uncontended for sequential single-worker mode). Rust's `Mutex`
/// does not have biased locking — even uncontended `lock()`/`unlock()` costs
/// ~20ns for the atomic CAS. For sequential mode processing millions of states,
/// this would add measurable overhead.
///
/// The trait approach gives us TLC's conceptual simplicity (one loop body) with
/// Rust's zero-cost abstraction (monomorphized to direct VecDeque calls for
/// sequential, work-stealing for parallel).
pub(crate) trait BfsTransport {
    /// Type carried in the work queue.
    ///
    /// - Sequential: `S::QueueEntry` (e.g., `(Fingerprint, usize)` for
    ///   full-state, `(NoTraceQueueEntry, usize, u64)` for fingerprint-only)
    /// - Parallel: `(T, usize)` where `T: BfsWorkItem`
    type WorkItem;

    /// Try to get the next work item.
    ///
    /// Returns `None` when the worker should stop:
    /// - Sequential: queue exhausted
    /// - Parallel: termination detected (all workers idle + queue empty)
    fn try_dequeue(&mut self) -> Option<Self::WorkItem>;

    /// Resolve a work item to `(fingerprint, ArrayState, depth)`.
    ///
    /// Returns `Ok(None)` to skip a phantom dequeue (sequential storage can
    /// produce `None` for entries that were superseded). Returns `Err` to
    /// terminate the loop.
    fn resolve(
        &mut self,
        item: Self::WorkItem,
    ) -> Result<Option<(Fingerprint, ArrayState, usize)>, BfsTermination>;

    /// Report progress for this iteration.
    ///
    /// Returns `Err(BfsTermination)` if a memory limit was reached and BFS should stop.
    /// Sequential: delegates to `ModelChecker::maybe_report_progress`.
    /// Parallel: no-op (coordinator thread handles progress externally).
    fn report_progress(&mut self, depth: usize, queue_len: usize) -> Result<(), BfsTermination>;

    /// Check if a checkpoint should be saved at this point.
    ///
    /// Sequential: delegates to `ModelChecker::should_save_checkpoint`.
    /// Parallel: returns `false`; periodic checkpoint saves are not triggered
    /// via this transport hook even though parallel runs support
    /// checkpoint/resume at the CLI/checker layer.
    fn should_checkpoint(&self) -> bool;

    /// Save a checkpoint of the current BFS frontier.
    ///
    /// Only called when `should_checkpoint()` returns `true`.
    fn save_checkpoint(&mut self, current: &ArrayState);

    /// Check if the state limit has been reached.
    ///
    /// Sequential: delegates to `ModelChecker::check_state_limit`.
    /// Parallel: state limit is enforced at the admission point via CAS
    /// (in `ParallelAdapter::admit`), so this is a no-op returning `Ok(())`.
    fn check_state_limit(&mut self) -> Result<(), BfsTermination>;

    /// Release a state back to the transport without processing successors.
    ///
    /// Called on early exit paths (state limit hit, depth limit skip, level
    /// computation error) where the state from `resolve()` was not passed to
    /// `process_successors`.
    ///
    /// Sequential: delegates to `BfsStorage::return_current` (required by the
    /// `BfsIterState` guard contract).
    /// Parallel: no-op (states are not stored during iteration).
    fn release_state(&mut self, fp: Fingerprint, current: ArrayState);

    /// Notify that a state was skipped due to the depth limit.
    ///
    /// Sequential: sets the `depth_limit_reached` flag for the return value.
    /// Parallel: sets the shared `depth_limit_reached` atomic.
    fn on_depth_limit_skip(&mut self);

    /// Process all successors of the given state.
    ///
    /// This is the dispatch entry point that handles:
    /// 1. Diff-based vs full-state enumeration selection
    /// 2. Creating the appropriate `CoreStepAdapter` (sequential or parallel)
    /// 3. Running `run_core_step` for each successor
    /// 4. Deadlock checking (sequential) or transition counting (parallel)
    /// 5. Returning the current state to storage (sequential `BfsIterState` guard)
    ///
    /// The `current` state is consumed: sequential wraps it in `BfsIterState`
    /// for RAII return-to-storage, parallel passes it to `WorkerBfsCtx`.
    fn process_successors(
        &mut self,
        fp: Fingerprint,
        current: ArrayState,
        depth: usize,
        succ_depth: usize,
        current_level: u32,
        succ_level: u32,
    ) -> Result<(), BfsTermination>;

    /// Handle a fatal error during loop iteration (e.g., depth overflow,
    /// level conversion failure).
    ///
    /// Takes the current state to release it back to storage before
    /// producing the termination signal.
    ///
    /// Sequential: calls `bfs_error_return` (update coverage + return state +
    /// produce `CheckResult`).
    /// Parallel: sends a `WorkerResult::Error` through the channel.
    fn handle_error(
        &mut self,
        fp: Fingerprint,
        current: ArrayState,
        error: CheckError,
    ) -> BfsTermination;

    /// Output profiling data after the loop completes normally.
    ///
    /// Called when the loop exits due to queue exhaustion (not early termination).
    fn output_profile(&self);

    /// Whether the depth limit was reached during exploration.
    ///
    /// Queried after the loop exits normally to construct the return value.
    /// Sequential: returns the local `depth_limit_reached` flag.
    /// Parallel: reads the shared `depth_limit_reached` atomic.
    fn depth_limit_reached(&self) -> bool;

    /// Attempt periodic liveness checking during BFS exploration.
    ///
    /// Part of #2752: Replicates TLC's `doPeriodicWork()` pattern. Called from
    /// the unified BFS loop between checkpoint and state-limit checks.
    ///
    /// Sequential: delegates to `ModelChecker::maybe_periodic_liveness()` which
    /// gates on growth threshold, time budget, and minimum interval.
    /// Parallel: no-op (requires worker suspension, deferred to future work).
    ///
    /// Returns `Err(BfsTermination)` if a liveness violation is found mid-BFS,
    /// `Ok(())` otherwise (including when the check is skipped).
    fn maybe_periodic_liveness(&mut self) -> Result<(), BfsTermination> {
        Ok(())
    }

    /// Notify the transport of a dequeued state for frontier sampling (CDEMC).
    ///
    /// Part of #3768: At BFS level boundaries (depth increases), the transport
    /// samples up to 10 scalar-only states and sends them to the cooperative
    /// state hub for symbolic engine consumption.
    ///
    /// Default: no-op. Overridden when the ModelChecker has a cooperative state.
    fn maybe_sample_frontier(&mut self, _depth: usize, _state: &super::super::ArrayState) {}
}

/// Shared configuration for the BFS worker loop.
///
/// Contains parameters that are identical across sequential and parallel
/// modes and control the loop's behavior. Transport implementations read
/// these at construction time; the unified loop body reads them directly.
///
/// Part of #2356 Phase 4.
#[derive(Debug, Clone)]
pub(crate) struct BfsWorkerConfig {
    /// Maximum BFS exploration depth (`None` = unlimited).
    ///
    /// When set, states at `depth >= max_depth` are skipped (not explored
    /// further) and the transport's `on_depth_limit_skip` is called.
    pub max_depth: Option<usize>,
}
