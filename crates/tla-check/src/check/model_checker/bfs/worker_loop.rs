// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unified BFS worker loop body, generic over [`BfsTransport`].
//!
//! Part of #2356 Phase 4 Step 4d: the single BFS dequeue–limits–depth–process
//! loop that serves both sequential and parallel modes. This is the Rust
//! equivalent of TLC's single `Worker.run()` — one function called with
//! either `SequentialTransport` or `ParallelTransport`.
//!
//! ## Architecture
//!
//! ```text
//! run_bfs_worker<T: BfsTransport>(transport, config)
//!   while transport.try_dequeue():
//!     transport.maybe_periodic_liveness() → mid-BFS liveness (#2752)
//!     transport.resolve(item)             → (fp, state, depth)
//!     transport.maybe_sample_frontier()   → CDEMC frontier sampling (#3768)
//!     transport.report_progress()
//!     transport.should_checkpoint()       → save_checkpoint()
//!     transport.check_state_limit()
//!     depth_limit_check(config)
//!     depth_to_tlc_level(depth)           → current_level, succ_level
//!     transport.process_successors()      → run_core_step (unified inner)
//!   transport.output_profile()
//! ```
//!
//! The `BfsTransport` trait dispatches mode-specific mechanics (VecDeque vs
//! work-stealing, progress vs no-op, checkpoint vs no-op) while this function
//! owns the shared control flow. Together with `CoreStepAdapter` (Phases 1-3),
//! this eliminates the three-loop-body duplication that was the root cause of
//! #2355, #1931, #1799, and #1812.

use super::dialect_trace::DialectTracer;
use super::transport::{BfsTransport, BfsWorkerConfig};
use crate::shared_verdict::SharedVerdict;

/// Thread-local monotonic worker id counter used solely by the dialect
/// tracer. Zero-cost when the tracer is disabled (the tracer never reads it),
/// and cheap when enabled — one relaxed atomic increment per worker.
///
/// Part of #4253 Wave 14: the unified BFS loop does not otherwise know its
/// worker lane id (sequential mode has no lane id; parallel mode carries it
/// on the transport). Rather than plumb the id through every transport impl,
/// we mint a process-global monotonic id here that is stable for the life of
/// a worker and unique across workers. That is exactly the invariant the
/// `verif.bfs_step` op wants on its `worker_id` field.
fn next_dialect_worker_id() -> u32 {
    use std::sync::atomic::{AtomicU32, Ordering};
    static COUNTER: AtomicU32 = AtomicU32::new(0);
    COUNTER.fetch_add(1, Ordering::Relaxed)
}

#[inline]
fn terminate_with_profile<T: BfsTransport>(
    transport: &T,
    term: super::transport::BfsTermination,
) -> BfsLoopOutcome {
    transport.output_profile();
    term.into()
}

/// Outcome of the core BFS loop (`run_bfs_worker`).
///
/// Separates the BFS iteration loop from post-loop finalization so that
/// callers can select `resume_mode` when calling `finish_check_after_bfs`.
///
/// Part of #2356: enables resume path reuse of the BFS loop.
/// Part of #1812: both paths now use `finish_check_after_bfs` with a
/// `resume_mode` flag instead of separate finalization functions.
pub(crate) enum BfsLoopOutcome {
    /// BFS queue exhausted normally. Caller should run post-loop finalization
    /// via `finish_check_after_bfs(depth_limit_reached, resume_mode)`.
    Complete { depth_limit_reached: bool },
    /// BFS loop terminated early (error, violation, state limit).
    ///
    /// Boxed to avoid `clippy::large_enum_variant` — `CheckResult` is large
    /// (contains error details, violation info, trace) while `Complete` is a bool.
    Terminated(Box<super::super::CheckResult>),
}

/// Check interval for portfolio early-exit polling.
///
/// Every 4096 states, the BFS loop checks whether another portfolio lane
/// has resolved the verdict, avoiding wasted work. 4096 is cheap enough
/// (one atomic load) to not affect throughput while being responsive
/// enough for timely early exit.
const PORTFOLIO_CHECK_INTERVAL: u64 = 4096;

/// Unified BFS worker loop, generic over transport mode.
///
/// Called by:
/// - `engine.rs:run_bfs_loop_core` with `SequentialTransport` (single-threaded)
/// - `run_unified.rs:run_worker_unified` with `ParallelTransport` (multi-threaded)
///
/// When `portfolio_verdict` is `Some`, checks every [`PORTFOLIO_CHECK_INTERVAL`]
/// states whether another lane has resolved the verdict, exiting early if so.
///
/// Returns `BfsLoopOutcome::Complete` when the queue is exhausted normally,
/// or `BfsLoopOutcome::Terminated` for early exit (error, violation, limit).
///
/// Part of #2356 Phase 4 Step 4d.
/// Part of #3717: SharedVerdict wiring for portfolio racing.
pub(crate) fn run_bfs_worker<T: BfsTransport>(
    transport: &mut T,
    config: &BfsWorkerConfig,
    portfolio_verdict: Option<&SharedVerdict>,
) -> BfsLoopOutcome {
    let mut states_processed: u64 = 0;
    // Part of #3990: Track last-seen depth for arena reset at level boundaries.
    // When we transition to a new BFS depth, the transient successor allocations
    // from the previous level are no longer needed. Resetting the arena at
    // depth transitions provides O(1) bulk free of per-level scratch memory.
    let mut last_arena_reset_depth: Option<usize> = None;

    // Part of #4253 Wave 14: Per-worker dialect tracer. When the env var
    // `TLA2_DIALECT_TRACE=1` is set, emits one `verif.bfs_step` op per BFS
    // dequeue and logs it to stderr. When the env var is unset (production
    // default), the tracer's `emit_step` is a single predictable-branch
    // early-return that LLVM inlines away in release builds.
    let dialect_tracer = DialectTracer::new(next_dialect_worker_id());

    while let Some(item) = transport.try_dequeue() {
        // Portfolio early-exit check: poll every PORTFOLIO_CHECK_INTERVAL states.
        // Part of #3717.
        if let Some(sv) = portfolio_verdict {
            if states_processed % PORTFOLIO_CHECK_INTERVAL == 0 && states_processed > 0 {
                if sv.is_resolved() {
                    transport.output_profile();
                    return BfsLoopOutcome::Complete {
                        depth_limit_reached: false,
                    };
                }
            }
        }
        states_processed += 1;
        // Periodic liveness checking BEFORE resolve — must run while all
        // states are still in `seen`. FullStateStorage::dequeue() temporarily
        // removes the current state from the HashMap; if periodic liveness
        // ran after dequeue, safety_temporal would fail to find the dequeued
        // state when iterating cached successor fingerprints (#2901).
        // Sequential: gated on growth/time/interval; parallel: no-op.
        // Part of #2752: TLC doPeriodicWork() pattern.
        if let Err(term) = transport.maybe_periodic_liveness() {
            return terminate_with_profile(transport, term);
        }

        // Resolve work item to (fingerprint, ArrayState, depth).
        // None = phantom dequeue (superseded entry) — skip.
        let (fp, current, depth) = match transport.resolve(item) {
            Ok(Some(resolved)) => resolved,
            Ok(None) => continue,
            Err(term) => return terminate_with_profile(transport, term),
        };

        // Part of #4253 Wave 14: emit a `verif.bfs_step` op per resolved
        // dequeue. `states_processed` is used as a monotonic frontier-size
        // proxy (the unified transport does not expose current frontier
        // width; the monotonic counter is sufficient to distinguish steps in
        // the trace log). `action_id = 0` because the dequeue site does not
        // know which action produced the frontier state — that information
        // lives one level up in `process_successors`, and routing it here
        // would force every transport impl to thread it through. A later
        // wave can refine this once the dialect has a stable action id
        // registry.
        dialect_tracer.emit_step(depth, states_processed as usize, 0);

        // Part of #4286 Wave 14 TL3d: emit the graduated per-state
        // verification primitives alongside `verif.bfs_step`. Every resolved
        // dequeue is, conceptually:
        //   (1) compute a state fingerprint to dedup against `seen`
        //   (2) check every invariant against the state
        // The BFS worker loop does not *perform* either operation at this
        // call site (dedup happened before enqueue; invariant eval runs
        // inside `process_successors` against each produced successor), but
        // the tracer view is the namespace seam we want the dialect tower
        // to own. Emitting here keeps the trace output self-contained at the
        // dequeue level and exercises the graduated `new_at_depth`
        // constructors + structured leaves on every BFS step.
        //
        // `states_processed` is the monotonic state-slot proxy (same logic
        // as `emit_step`). `invariant_id = 0` because the dequeue site has
        // no stable invariant registry yet; a later wave can plumb real
        // ids through `BfsTransport` and route them here.
        if dialect_tracer.is_enabled() {
            dialect_tracer.emit_state_fingerprint(states_processed as usize, depth);
            dialect_tracer.emit_invariant_check(0, states_processed as usize, depth);
        }

        // Part of #3990: Reset the per-worker bump arena at BFS depth transitions.
        // When depth changes, all transient successor states from the previous
        // level have been processed (dedup checked, invariant checked, either
        // admitted to the seen-set or discarded). The arena can safely reclaim
        // all bump-allocated memory in O(1). This is the "bulk free at BFS level
        // boundaries" pattern from the Phase 7 arena design.
        //
        // Part of #4286 Wave 14 TL3: BFS depth transitions are the natural
        // emit site for the graduated `verif.frontier_drain` +
        // `verif.fingerprint_batch` ops. A depth transition marks that the
        // previous level's frontier was fully drained (drain) and that its
        // states were fingerprinted into the seen-set (batch). We emit on
        // the transition *edge* (when `last_arena_reset_depth` is `Some(old)`
        // and `old != depth`) — the very first state of the run
        // (`last_arena_reset_depth == None`) emits no retroactive drain
        // because there is no previous level. `states_processed - 1` is
        // used as the monotonic `state_base` so successive batches do not
        // overlap in the trace log.
        if last_arena_reset_depth != Some(depth) {
            if last_arena_reset_depth.is_some() && dialect_tracer.is_enabled() {
                // `states_processed` counts every dequeue including the
                // current one, so states drained at the *previous* level ==
                // states_processed - 1 (the current state is the first at
                // the new level). We forward that into the drain's `max`
                // (bounded dequeue count) and the batch's `count`.
                let prev_level_drained = states_processed.saturating_sub(1) as usize;
                dialect_tracer.emit_frontier_drain(prev_level_drained.max(1));
                let state_base = prev_level_drained.saturating_sub(prev_level_drained.max(1));
                let prev_depth = last_arena_reset_depth.unwrap_or(0);
                dialect_tracer.emit_fingerprint_batch(
                    state_base,
                    prev_level_drained.max(1),
                    prev_depth,
                );
            }
            crate::arena::worker_arena_reset();
            last_arena_reset_depth = Some(depth);
        }

        // Part of #3768: CDEMC frontier sampling at level boundaries.
        // Runs before progress/checkpoint so sampling doesn't delay hot-path
        // control flow. The transport delegates to FrontierSampler (if active)
        // which detects depth transitions and samples scalar-only states.
        transport.maybe_sample_frontier(depth, &current);

        // Progress reporting (sequential: periodic output; parallel: no-op).
        // Returns Err if memory limit reached (Part of #2751).
        if let Err(term) = transport.report_progress(depth, 0) {
            transport.release_state(fp, current);
            return terminate_with_profile(transport, term);
        }

        // Checkpoint saving (sequential: periodic; parallel: no-op).
        if transport.should_checkpoint() {
            transport.save_checkpoint(&current);
        }

        // State limit check (sequential: count-based; parallel: CAS in admit).
        if let Err(term) = transport.check_state_limit() {
            transport.release_state(fp, current);
            return terminate_with_profile(transport, term);
        }

        // Depth limit check.
        if let Some(max_depth) = config.max_depth {
            if depth >= max_depth {
                transport.on_depth_limit_skip();
                transport.release_state(fp, current);
                continue;
            }
        }

        // Compute successor depth (overflow check).
        let succ_depth = match depth.checked_add(1) {
            Some(d) => d,
            None => {
                let error = crate::checker_ops::depth_overflow_error(depth);
                let term = transport.handle_error(fp, current, error);
                return terminate_with_profile(transport, term);
            }
        };

        // Compute TLC levels for current and successor depths.
        let current_level = match crate::checker_ops::depth_to_tlc_level(depth) {
            Ok(level) => level,
            Err(error) => {
                let term = transport.handle_error(fp, current, error);
                return terminate_with_profile(transport, term);
            }
        };
        let succ_level = match crate::checker_ops::depth_to_tlc_level(succ_depth) {
            Ok(level) => level,
            Err(error) => {
                let term = transport.handle_error(fp, current, error);
                return terminate_with_profile(transport, term);
            }
        };

        // Dispatch to successor processing (diff or full-state enumeration).
        // The transport handles CoreStepAdapter creation and BfsIterState/RAII.
        if let Err(term) =
            transport.process_successors(fp, current, depth, succ_depth, current_level, succ_level)
        {
            return terminate_with_profile(transport, term);
        }
    }

    // Queue exhausted — output profiling and return success.
    transport.output_profile();
    BfsLoopOutcome::Complete {
        depth_limit_reached: transport.depth_limit_reached(),
    }
}

#[cfg(test)]
#[path = "worker_loop_tests/mod.rs"]
mod tests;
