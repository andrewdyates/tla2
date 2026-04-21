// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `BfsTransport` implementation for `SharedQueueTransport` (Part of #3258, #3271).
//!
//! Split from `shared_queue.rs` for file-size compliance. Contains the trait
//! impl (try_dequeue, resolve, process_successors, etc.) and the Drop impl.
//!
//! Part of #3271: `try_dequeue` uses the frontier's condvar-based
//! `dequeue_batch_blocking` instead of polling with backoff. Termination is
//! detected by the frontier when all workers are waiting with an empty queue
//! — matching TLC's `StateQueue.isAvail()` contract.

use super::super::coordination::{
    flush_local_work_delta, send_done_result, snapshot_stop_and_send,
};
use super::super::work_item::{BfsWorkItem, ResolvedArrayState};
use super::super::StopCtx;
use super::shared_queue::{DequeueOutcome, SharedQueueTransport, SHARED_QUEUE_BATCH_SIZE};
use crate::check::model_checker::bfs::transport::{BfsTermination, BfsTransport};
use crate::check::CheckError;
use crate::parallel::{WorkerResult, WORK_BATCH_SIZE};
use crate::state::{ArrayState, Fingerprint};
use tla_eval::eval_arena::ArenaStateGuard;

use std::sync::atomic::Ordering;

impl<T: BfsWorkItem> BfsTransport for SharedQueueTransport<T> {
    type WorkItem = (T, usize);

    fn try_dequeue(&mut self) -> Option<Self::WorkItem> {
        // Step 1: Pop from local dequeue_batch first (no lock needed).
        if let Some(item) = self.dequeue_batch.pop() {
            if self.stop_flag.load(Ordering::Relaxed) {
                flush_local_work_delta(&mut self.local_work_delta, &self.work_remaining);
                send_done_result(&self.ctx, &mut self.stats, &self.result_tx);
                return None;
            }
            if self.barrier.is_pause_requested() {
                flush_local_work_delta(&mut self.local_work_delta, &self.work_remaining);
                self.barrier.worker_check();
            }
            return Some(item);
        }

        // Step 2: Local batch empty — flush work delta before blocking.
        // The delta flush keeps work_remaining accurate for ParallelAdapter
        // even though it's not used for termination (Part of #3271).
        flush_local_work_delta(&mut self.local_work_delta, &self.work_remaining);
        if self.frontier_batch_active {
            self.frontier.complete_level_batch();
            self.frontier_batch_active = false;
        }

        // Step 3: Block on shared frontier with TLC-style wait/notify.
        // The frontier's condvar handles sleeping, waking on new work, and
        // completion detection (all workers waiting + empty queue).
        loop {
            // Check stop flag before blocking.
            if self.stop_flag.load(Ordering::Relaxed) {
                send_done_result(&self.ctx, &mut self.stats, &self.result_tx);
                return None;
            }

            // Check barrier before blocking.
            if self.barrier.is_pause_requested() {
                self.barrier.worker_check();
            }

            match self.frontier.dequeue_batch_blocking(
                &mut self.dequeue_batch,
                SHARED_QUEUE_BATCH_SIZE,
                &self.stop_flag,
            ) {
                DequeueOutcome::Refilled => {
                    // Reverse so pop() yields items in FIFO order: dequeue fills
                    // [A, B, C]; reverse gives [C, B, A]; pop() returns A, B, C.
                    self.dequeue_batch.reverse();
                    self.frontier_batch_active = true;
                    return self.dequeue_batch.pop();
                }
                DequeueOutcome::Done => {
                    send_done_result(&self.ctx, &mut self.stats, &self.result_tx);
                    return None;
                }
                DequeueOutcome::TimedOut => {
                    // Woke from timeout — loop back to check stop/barrier, then retry.
                    self.stats.empty_polls += 1;
                    continue;
                }
            }
        }
    }

    fn resolve(
        &mut self,
        item: Self::WorkItem,
    ) -> Result<Option<(Fingerprint, ArrayState, usize)>, BfsTermination> {
        let (mut work_item, current_depth) = item;
        let base_fp = work_item.base_fingerprint(&self.var_registry);
        self.stats.states_explored += 1;
        debug_assert!(
            !self.current_uses_decode_scratch,
            "decode scratch must be reclaimed before resolving the next work item"
        );
        let mut scratch = self.decode_scratch.take();
        let resolved =
            work_item.resolve_array_state(scratch.as_mut(), &self.var_registry, &self.mode);
        let (current_array, used_scratch) = match resolved {
            ResolvedArrayState::Owned(arr) => {
                self.decode_scratch = scratch;
                (arr, false)
            }
            ResolvedArrayState::UsedScratch => (
                scratch.expect("scratch-backed resolve must return the transport scratch"),
                true,
            ),
        };
        self.current_uses_decode_scratch = used_scratch;

        Ok(Some((base_fp, current_array, current_depth)))
    }

    fn report_progress(&mut self, _depth: usize, _queue_len: usize) -> Result<(), BfsTermination> {
        // Per-worker inline RSS check: supplements the coordinator's periodic
        // maintenance barrier with a lightweight check every 10,000 states.
        if let Some(critical) = self.critical_rss_bytes {
            self.states_since_rss_check += 1;
            if self.states_since_rss_check >= 10_000 {
                self.states_since_rss_check = 0;
                if let Some(rss) = crate::memory::current_rss_bytes() {
                    if rss >= critical {
                        self.stop_flag.store(true, Ordering::Relaxed);
                        let stop_ctx = StopCtx {
                            stop_flag: &self.stop_flag,
                            states_at_stop: &self.states_at_stop,
                            seen: &self.seen,
                            seen_fps: &*self.seen_fps,
                            store_full_states: self.store_full_states,
                            cache_for_liveness: self.successors_cache.is_some(),
                            admitted_states: &self.admitted_states,
                            max_states_limit: self.max_states_limit,
                            collision_diagnostics: self.collision_diagnostics.as_deref(),
                        };
                        snapshot_stop_and_send(
                            &self.ctx,
                            &mut self.stats,
                            &stop_ctx,
                            &self.result_tx,
                            |stats| WorkerResult::LimitReached {
                                limit_type: crate::check::LimitType::Memory,
                                stats,
                            },
                        );
                        return Err(BfsTermination::Exit);
                    }
                }
            }
        }
        Ok(())
    }

    fn should_checkpoint(&self) -> bool {
        false
    }

    fn save_checkpoint(&mut self, _current: &ArrayState) {}

    fn check_state_limit(&mut self) -> Result<(), BfsTermination> {
        Ok(())
    }

    fn release_state(&mut self, _fp: Fingerprint, current: ArrayState) {
        self.reclaim_decode_scratch(current);
    }

    fn on_depth_limit_skip(&mut self) {
        self.depth_limit_reached.store(true, Ordering::Relaxed);
        self.local_work_delta -= 1;
        if self.local_work_delta <= -(WORK_BATCH_SIZE as isize) {
            flush_local_work_delta(&mut self.local_work_delta, &self.work_remaining);
        }
    }

    fn process_successors(
        &mut self,
        fp: Fingerprint,
        current: ArrayState,
        _depth: usize,
        succ_depth: usize,
        current_level: u32,
        succ_level: u32,
    ) -> Result<(), BfsTermination> {
        // Part of #3580: keep the arena lifecycle panic-safe across successor eval.
        let _arena_state = ArenaStateGuard::new();
        #[cfg(feature = "jit")]
        let transitions_before = self.stats.transitions;
        let result =
            self.process_successors_inner(fp, &current, succ_depth, current_level, succ_level);
        // Part of #3910: Record action evaluation for tier promotion tracking.
        #[cfg(feature = "jit")]
        if let Some(ref tier) = self.tier_state {
            let succ_count = self.stats.transitions.saturating_sub(transitions_before);
            tier.record_action_eval(0, succ_count as u64);
        }
        self.reclaim_decode_scratch(current);
        result
    }

    fn handle_error(
        &mut self,
        _fp: Fingerprint,
        current: ArrayState,
        error: CheckError,
    ) -> BfsTermination {
        self.reclaim_decode_scratch(current);
        let stop_ctx = StopCtx {
            stop_flag: &self.stop_flag,
            states_at_stop: &self.states_at_stop,
            seen: &self.seen,
            seen_fps: &*self.seen_fps,
            store_full_states: self.store_full_states,
            cache_for_liveness: self.successors_cache.is_some(),
            admitted_states: &self.admitted_states,
            max_states_limit: self.max_states_limit,
            collision_diagnostics: self.collision_diagnostics.as_deref(),
        };
        snapshot_stop_and_send(
            &self.ctx,
            &mut self.stats,
            &stop_ctx,
            &self.result_tx,
            |stats| WorkerResult::Error(error, stats),
        );
        BfsTermination::Exit
    }

    fn output_profile(&self) {
        // Part of #3580: report per-worker arena allocation stats.
        tla_eval::eval_arena::report_arena_stats();
        // Part of #3990: report per-worker state arena stats.
        crate::arena::report_worker_arena_stats();
    }

    fn depth_limit_reached(&self) -> bool {
        self.depth_limit_reached.load(Ordering::Relaxed)
    }
}

impl<T: BfsWorkItem> Drop for SharedQueueTransport<T> {
    fn drop(&mut self) {
        // Part of #3271: Wake any workers sleeping on the frontier condvar.
        // Handles all exit paths: normal completion (no-op if already finished),
        // error/violation (sleeping workers wake and see stop_flag), and panic
        // (WorkerPanicGuard sets stop_flag, then this wakes sleepers).
        self.frontier.finish();
    }
}
