// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
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

use super::transport::{BfsTransport, BfsWorkerConfig};
use crate::shared_verdict::SharedVerdict;

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

        // Part of #3990: Reset the per-worker bump arena at BFS depth transitions.
        // When depth changes, all transient successor states from the previous
        // level have been processed (dedup checked, invariant checked, either
        // admitted to the seen-set or discarded). The arena can safely reclaim
        // all bump-allocated memory in O(1). This is the "bulk free at BFS level
        // boundaries" pattern from the Phase 7 arena design.
        if last_arena_reset_depth != Some(depth) {
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
