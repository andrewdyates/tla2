// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parallel-mode adapter for the shared CoreStepAdapter reducer.
//!
//! Part of #2356 Step 3a: implements [`CoreStepAdapter`] for the parallel worker
//! path, wrapping the parallel worker's channel-based stop protocol, shared
//! FingerprintSet, and work-stealing counters to match the CoreStepAdapter contract.
//!
//! The adapter covers the core admit→check→enqueue sequence. Pre-admit operations
//! (constraint checking, materialization, VIEW fingerprinting, implied action checking)
//! remain in the caller — matching TLC's design where `Worker.addElement()` handles
//! only the core sequence while pre-admit ops happen in the calling code.

use super::super::{accum_ns, timing_start, WorkerResult, WorkerStats, WORK_BATCH_SIZE};
use super::coordination::{flush_local_work_delta_profiled, snapshot_stop_and_send};
use super::observer::{observe_admitted_successor, SuccessorObservationCtx};
use super::{InvariantCheckCtx, StopCtx};
use crate::check::model_checker::{CoreStepAdapter, CoreStepInput};
use crate::check::{CheckError, LimitType};
use crate::checker_ops::InvariantOutcome;
use crate::eval::EvalCtx;
use crate::storage::InsertOutcome;
use crossbeam_channel::Sender;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Parallel-mode adapter for the shared CoreStepAdapter reducer.
///
/// Wraps the parallel worker's channel-based stop protocol, shared
/// FingerprintSet, and work-stealing counters to match the CoreStepAdapter
/// contract.
///
/// Created per-successor (via reborrow) so that `ctx` remains available to the
/// caller for pre-admit operations between successive `run_core_step` calls.
///
/// Part of #2356 Step 3a.
// Step 3a creates the type; Steps 3b-3c wire it into successors/.
pub(super) struct ParallelAdapter<'a, 'inv, F> {
    pub(super) ctx: &'a mut EvalCtx,
    pub(super) inv_ctx: &'a InvariantCheckCtx<'inv>,
    pub(super) stop: &'a StopCtx<'inv>,
    pub(super) result_tx: &'a Sender<WorkerResult>,
    pub(super) stats: &'a mut WorkerStats,
    pub(super) local_work_delta: &'a mut isize,
    pub(super) work_remaining: &'a AtomicUsize,
    pub(super) max_depth_atomic: &'a AtomicUsize,
    pub(super) enqueue_fn: F,
}

impl<F> CoreStepAdapter for ParallelAdapter<'_, '_, F>
where
    F: FnMut(&crate::state::ArrayState, usize),
{
    type Stop = bool;

    fn admit(&mut self, input: &CoreStepInput<'_>) -> Result<bool, Self::Stop> {
        // Step 1: Reserve admission slot (Part of #2123, prevents overshoot).
        if let Some(limit) = self.stop.max_states_limit {
            if !crate::checker_ops::try_reserve_state_slot(self.stop.admitted_states, limit) {
                snapshot_stop_and_send(self.ctx, self.stats, self.stop, self.result_tx, |stats| {
                    WorkerResult::LimitReached {
                        limit_type: LimitType::States,
                        stats,
                    }
                });
                return Err(true);
            }
        }

        // Step 2: Check if state is new and insert into seen set.
        if let Some(diagnostics) = self.stop.collision_diagnostics {
            diagnostics.record_state(input.succ_fp, input.succ, input.succ_depth);
        }
        let t_admit = timing_start();
        // Part of #3233: Read-first dedup — contains_key (read lock) filters
        // ~95% duplicates; insert+clone only runs for genuinely new states.
        let is_new = if self.stop.store_full_states {
            !self.stop.seen.contains_key(&input.succ_fp)
                && self
                    .stop
                    .seen
                    .insert(input.succ_fp, input.succ.clone())
                    .is_none()
        } else {
            match self.stop.seen_fps.insert_checked(input.succ_fp) {
                InsertOutcome::Inserted => {
                    // Part of #3801: When liveness is active (cache_for_liveness),
                    // also store the full ArrayState in `seen` so that post-BFS
                    // liveness has all states available without needing the
                    // unreliable fp-only replay path. The fp-only replay can
                    // fail when re-enumeration produces different fingerprints
                    // than the original BFS (due to evaluation context differences),
                    // causing incomplete state caches and incorrect liveness results.
                    if self.stop.cache_for_liveness {
                        self.stop.seen.insert(input.succ_fp, input.succ.clone());
                    }
                    true
                }
                InsertOutcome::AlreadyPresent => false,
                InsertOutcome::StorageFault(fault) => {
                    if self.stop.max_states_limit.is_some() {
                        crate::checker_ops::release_state_slot(self.stop.admitted_states);
                    }
                    let error = crate::checker_ops::storage_fault_to_check_error(
                        self.stop.seen_fps,
                        &fault,
                    );
                    snapshot_stop_and_send(
                        self.ctx,
                        self.stats,
                        self.stop,
                        self.result_tx,
                        |stats| WorkerResult::Error(error, stats),
                    );
                    return Err(true);
                }
                _ => unreachable!(),
            }
        };
        accum_ns(
            if is_new {
                &mut self.stats.insert_ns
            } else {
                &mut self.stats.contains_ns
            },
            t_admit,
        );

        if !is_new {
            if self.stop.max_states_limit.is_some() {
                crate::checker_ops::release_state_slot(self.stop.admitted_states);
            }
            return Ok(false);
        }

        // Step 3: Update work counters and depth tracking.
        *self.local_work_delta += 1;
        if *self.local_work_delta >= WORK_BATCH_SIZE as isize {
            flush_local_work_delta_profiled(self.local_work_delta, self.work_remaining, self.stats);
        }
        // Part of #3178: Append to per-worker shard (zero contention).
        if self.stop.store_full_states || self.stop.cache_for_liveness {
            self.inv_ctx
                .parent_log
                .append(self.inv_ctx.worker_id, input.succ_fp, input.parent_fp);
        }
        // Part of #3233: depth tracking only when checkpoint or fp-only liveness is active.
        if self.inv_ctx.track_depths {
            self.inv_ctx.depths.insert(input.succ_fp, input.succ_depth);
        }
        let _ = self
            .max_depth_atomic
            .fetch_max(input.succ_depth, Ordering::Relaxed);

        Ok(true)
    }

    fn check_invariants(&mut self, input: &CoreStepInput<'_>) -> InvariantOutcome {
        let t_inv = timing_start();
        let outcome = observe_admitted_successor(
            self.ctx,
            self.inv_ctx,
            self.stop,
            self.result_tx,
            self.stats,
            &SuccessorObservationCtx {
                current: input.succ,
                parent_fp: input.parent_fp,
                succ: input.succ,
                succ_fp: input.succ_fp,
                succ_depth: input.succ_depth,
                succ_level: input.succ_level,
            },
        );
        accum_ns(&mut self.stats.invariant_ns, t_inv);
        // Flush JIT counters from the Cell-based inv_ctx into worker stats.
        let hits = self.inv_ctx.jit_hits.get();
        let misses = self.inv_ctx.jit_misses.get();
        if hits > 0 {
            self.stats.jit_hits += hits;
            self.inv_ctx.jit_hits.set(0);
        }
        if misses > 0 {
            self.stats.jit_misses += misses;
            self.inv_ctx.jit_misses.set(0);
        }
        // Part of #3935: Flush fine-grained JIT dispatch counters.
        let fallback = self.inv_ctx.jit_fallback.get();
        let not_compiled = self.inv_ctx.jit_not_compiled.get();
        if fallback > 0 {
            self.stats.jit_fallback += fallback;
            self.inv_ctx.jit_fallback.set(0);
        }
        if not_compiled > 0 {
            self.stats.jit_not_compiled += not_compiled;
            self.inv_ctx.jit_not_compiled.set(0);
        }
        let verify_checked = self.inv_ctx.jit_verify_checked.get();
        let verify_mismatches = self.inv_ctx.jit_verify_mismatches.get();
        if verify_checked > 0 {
            self.stats.jit_verify_checked += verify_checked;
            self.inv_ctx.jit_verify_checked.set(0);
        }
        if verify_mismatches > 0 {
            self.stats.jit_verify_mismatches += verify_mismatches;
            self.inv_ctx.jit_verify_mismatches.set(0);
        }
        outcome
    }

    fn on_violation(
        &mut self,
        input: &CoreStepInput<'_>,
        invariant: String,
    ) -> Result<Option<Self::Stop>, Self::Stop> {
        // In parallel mode, continue_on_error is already handled by
        // check_successor_invariants (returns ViolationContinued). If we get here,
        // it's a fatal violation — stop the worker.
        snapshot_stop_and_send(self.ctx, self.stats, self.stop, self.result_tx, |stats| {
            WorkerResult::Violation {
                invariant,
                state_fp: input.succ_fp,
                stats,
            }
        });
        Ok(Some(true))
    }

    fn on_error(&mut self, _input: &CoreStepInput<'_>, error: CheckError) -> Self::Stop {
        snapshot_stop_and_send(self.ctx, self.stats, self.stop, self.result_tx, |stats| {
            WorkerResult::Error(error, stats)
        });
        true
    }

    fn enqueue(&mut self, input: &CoreStepInput<'_>) -> Result<(), Self::Stop> {
        (self.enqueue_fn)(input.succ, input.succ_depth);
        self.stats.states_generated += 1;
        Ok(())
    }
}

// Unit tests deferred to Step 3c when ParallelAdapter replaces inline code
// in successors/. All existing parallel integration tests must produce
// identical state counts — that is the behavioral equivalence gate.
