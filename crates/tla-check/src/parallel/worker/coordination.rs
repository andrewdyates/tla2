// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Lifecycle coordination for parallel workers: result sending, stop-flag
//! handling, delta flushing, and state snapshots.
//!
//! Work-stealing, backoff, and steal rotation live in `work_stealing.rs`.
//! Part of #2492: extracted from `helpers.rs` to separate work coordination
//! concerns from successor processing.

use super::super::{FxDashMap, WorkerResult, WorkerStats, WORK_BATCH_SIZE};
use super::StopCtx;
use crate::eval::EvalCtx;
use crate::state::{ArrayState, Fingerprint};
use crate::storage::FingerprintSet;
use crossbeam_channel::Sender;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::OnceLock;

/// Send a worker result to the main thread, warning if the channel is disconnected.
/// Part of #1443: replace all `let _ = result_tx.send(...)` sites with this helper.
pub(in crate::parallel) fn send_result(result_tx: &Sender<WorkerResult>, result: WorkerResult) {
    let maybe_stats = match &result {
        WorkerResult::Violation { stats, .. }
        | WorkerResult::PropertyActionViolation { stats, .. }
        | WorkerResult::Deadlock { stats, .. }
        | WorkerResult::Done(stats)
        | WorkerResult::Error(_, stats)
        | WorkerResult::LimitReached { stats, .. } => Some(stats),
    };
    if let Some(stats) = maybe_stats {
        super::super::emit_parallel_profile_worker_stats(stats);
    }
    if let Err(e) = result_tx.send(result) {
        let variant = match &e.0 {
            WorkerResult::Violation { invariant, .. } => {
                format!("Violation({})", invariant)
            }
            WorkerResult::Deadlock { .. } => "Deadlock".to_string(),
            WorkerResult::Error(err, _) => format!("Error({:?})", err),
            WorkerResult::Done(_) => "Done".to_string(),
            WorkerResult::PropertyActionViolation { property, .. } => {
                format!("PropertyActionViolation({})", property)
            }
            WorkerResult::LimitReached { limit_type, .. } => {
                format!("LimitReached({:?})", limit_type)
            }
        };
        eprintln!(
            "WARNING: worker result channel disconnected, dropping {} result. \
             This may indicate the main thread panicked.",
            variant
        );
    }
}

#[inline]
pub(super) fn send_done_result(
    _ctx: &EvalCtx,
    stats: &mut WorkerStats,
    result_tx: &Sender<WorkerResult>,
) {
    // Part of #3285: Capture intern attribution counters before sending stats.
    // The worker-local intern scope is still installed at this point (guard
    // drops later in run_worker_unified), so the counters are still readable.
    if stats.intern_counters.is_none() {
        stats.intern_counters = tla_value::read_intern_attribution_counters();
    }
    send_result(result_tx, WorkerResult::Done(std::mem::take(stats)));
}

/// Shared stop-flag check for worker loops. Returns true when the caller should return.
#[inline]
pub(super) fn finish_if_stop_requested(
    stop_flag: &AtomicBool,
    ctx: &EvalCtx,
    stats: &mut WorkerStats,
    result_tx: &Sender<WorkerResult>,
    local_work_delta: &mut isize,
    work_remaining: &AtomicUsize,
) -> bool {
    if !stop_flag.load(Ordering::Relaxed) {
        return false;
    }
    flush_local_work_delta_profiled(local_work_delta, work_remaining, stats);
    send_done_result(ctx, stats, result_tx);
    true
}

// skip_depth_limited_state was removed in #2356 Phase 4 Step 4d — depth
// limiting is now handled by the unified run_bfs_worker loop via
// BfsTransport::on_depth_limit_skip.

/// Flush a worker's batched work delta into the shared work counter.
///
/// Returns true when `work_remaining` is zero after the flush.
#[inline]
pub(super) fn flush_local_work_delta(delta: &mut isize, work_remaining: &AtomicUsize) -> bool {
    flush_local_work_delta_inner(delta, work_remaining).0
}

#[inline]
pub(super) fn flush_local_work_delta_profiled(
    delta: &mut isize,
    work_remaining: &AtomicUsize,
    stats: &mut WorkerStats,
) -> bool {
    let (is_zero, cas_retries) = flush_local_work_delta_inner(delta, work_remaining);
    stats.work_remaining_cas_retries += cas_retries;
    is_zero
}

#[inline]
fn flush_local_work_delta_inner(delta: &mut isize, work_remaining: &AtomicUsize) -> (bool, usize) {
    if *delta == 0 {
        return (work_remaining.load(Ordering::Acquire) == 0, 0);
    }
    if *delta > 0 {
        work_remaining.fetch_add(*delta as usize, Ordering::Release);
    } else {
        // Fix for #293: Atomic saturating subtraction via CAS loop.
        let sub_amount = (-*delta) as usize;
        let mut cas_retries = 0;
        loop {
            let current = work_remaining.load(Ordering::Acquire);
            let new_value = current.saturating_sub(sub_amount);
            match work_remaining.compare_exchange_weak(
                current,
                new_value,
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(_) => cas_retries += 1,
            }
        }
        *delta = 0;
        return (work_remaining.load(Ordering::Acquire) == 0, cas_retries);
    }
    *delta = 0;
    (work_remaining.load(Ordering::Acquire) == 0, 0)
}

/// Record one parent-state completion while preserving batched positive work.
/// Negative deltas still flush once the configured batch threshold is reached.
#[inline]
#[cfg(test)]
pub(super) fn record_state_completion(delta: &mut isize, work_remaining: &AtomicUsize) {
    record_state_completion_profiled(delta, work_remaining, None);
}

#[inline]
pub(super) fn record_state_completion_profiled(
    delta: &mut isize,
    work_remaining: &AtomicUsize,
    stats: Option<&mut WorkerStats>,
) {
    *delta -= 1;
    if *delta <= -(WORK_BATCH_SIZE as isize) {
        if let Some(stats) = stats {
            flush_local_work_delta_profiled(delta, work_remaining, stats);
        } else {
            flush_local_work_delta(delta, work_remaining);
        }
    }
}

#[inline]
pub(super) fn flush_transition_batch(total_transitions: &AtomicUsize, batch: &mut usize) {
    if *batch == 0 {
        return;
    }
    total_transitions.fetch_add(*batch, Ordering::Relaxed);
    *batch = 0;
}

/// Part of #1906/#2309: Snapshot the distinct-state count at first stop so
/// `finalize_check` can report it without post-violation inflation. `Some(0)`
/// remains distinguishable from "no snapshot" via `OnceLock`.
pub(super) fn snapshot_states_at_stop(
    states_at_stop: &OnceLock<usize>,
    seen: &FxDashMap<Fingerprint, ArrayState>,
    seen_fps: &dyn FingerprintSet,
    store_full_states: bool,
) {
    let count = if store_full_states {
        seen.len()
    } else {
        seen_fps.len()
    };
    // First writer wins; subsequent set() calls are no-ops.
    let _ = states_at_stop.set(count);
}

/// Stop worker execution with `states_at_stop` snapshot, then send terminal result.
pub(super) fn snapshot_stop_and_send(
    _ctx: &EvalCtx,
    stats: &mut WorkerStats,
    stop: &StopCtx<'_>,
    result_tx: &Sender<WorkerResult>,
    build_result: impl FnOnce(WorkerStats) -> WorkerResult,
) {
    stop.stop_flag.store(true, Ordering::SeqCst);
    snapshot_states_at_stop(
        stop.states_at_stop,
        stop.seen,
        stop.seen_fps,
        stop.store_full_states,
    );
    // Part of #3285: Capture intern attribution counters before sending.
    if stats.intern_counters.is_none() {
        stats.intern_counters = tla_value::read_intern_attribution_counters();
    }
    send_result(result_tx, build_result(std::mem::take(stats)));
}

// compute_current_level was removed in #2356 Phase 4 Step 4d — level
// computation is now handled by the unified run_bfs_worker loop via
// checker_ops::depth_to_tlc_level + BfsTransport::handle_error.

// compute_succ_depth_and_level was removed in #2356 Phase 4 Step 4e —
// succ_depth and succ_level are now computed once by the unified
// run_bfs_worker loop and threaded through BfsTransport::process_successors.
