// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pre-admitted diff processing for streaming BFS transport.
//!
//! Part of #3254: diffs authoritatively inserted during Phase A enumeration
//! skip FPSet admission in Phase B. Only invariant check + enqueue remain.
//!
//! Extracted from `streaming.rs` to keep file sizes under 500 lines (#3397).

use super::super::super::{accum_ns, timing_start, WORK_BATCH_SIZE};
use super::super::coordination::{flush_local_work_delta_profiled, snapshot_stop_and_send};
use super::super::observer::{observe_admitted_successor, SuccessorObservationCtx};
use super::super::work_item::BfsWorkItem;
use super::super::WorkerResult;
#[allow(unused_imports)]
use super::super::{InvariantCheckCtx, StopCtx};
use super::enqueue::route_successor_batch_to_injector;
use super::shared_queue::SHARED_QUEUE_BATCH_SIZE;
use super::ParallelTransport;
use crate::checker_ops::InvariantOutcome;
use crate::state::{ArrayState, DiffSuccessor, Fingerprint};
use smallvec::SmallVec;
use std::cell::{Cell, RefCell};
use std::sync::atomic::Ordering;

impl<T: BfsWorkItem> ParallelTransport<T> {
    /// Process pre-admitted diffs: invariant check + enqueue only.
    ///
    /// Part of #3254: These diffs were authoritatively inserted into the FPSet
    /// during Phase A enumeration. They contain no lazy values, so no
    /// materialization is needed. The fingerprint and combined_xor were
    /// pre-computed in Phase A.
    ///
    /// Returns `true` if the worker must stop (violation or error).
    pub(in crate::parallel) fn process_admitted_diffs(
        &mut self,
        base_array: &ArrayState,
        parent_fp: Fingerprint,
        succ_depth: usize,
        succ_level: u32,
        diffs: &mut Vec<(DiffSuccessor, Fingerprint, u64)>,
    ) -> bool {
        let admitted_count = diffs.len();

        // Update work counters for all admitted states.
        self.local_work_delta += admitted_count as isize;
        if self.local_work_delta >= WORK_BATCH_SIZE as isize {
            flush_local_work_delta_profiled(
                &mut self.local_work_delta,
                &self.work_remaining,
                &mut self.stats,
            );
        }

        // Update max depth (once for the batch, since all have same depth).
        let _ = self
            .max_depth_atomic
            .fetch_max(succ_depth, Ordering::Relaxed);

        // Parent pointers and depth tracking for admitted states.
        let cache_for_liveness = self.successors_cache.is_some();
        if self.store_full_states || cache_for_liveness {
            for &(_, succ_fp, _) in diffs.iter() {
                self.parent_log.append(self.worker_id, succ_fp, parent_fp);
            }
        }
        if self.track_depths {
            for &(_, succ_fp, _) in diffs.iter() {
                self.depths.insert(succ_fp, succ_depth);
            }
        }

        // Collision diagnostics (if enabled) — deferred to after materialize_into
        // since record_state needs the full ArrayState.

        // Set up enqueue infrastructure.
        let shared_frontier = &self.shared_frontier;
        let local_queue = &self.local_queue;
        let injector = &self.injector;
        let shared_frontier_tail_mode_active = self.shared_frontier_tail_mode_active();
        let route_to_injector = route_successor_batch_to_injector(
            &self.bootstrap_injector_budget,
            self.depth_limited,
            self.active_workers.as_ref(),
            self.num_workers,
        );
        let var_reg = &*self.var_registry;
        let mode_ref = &self.mode;
        let frontier_batch: RefCell<SmallVec<[(T, usize); SHARED_QUEUE_BATCH_SIZE]>> =
            RefCell::new(SmallVec::new());
        let injector_pushes = Cell::new(0usize);
        let enqueue_route = Self::successor_batch_route(
            shared_frontier_tail_mode_active,
            shared_frontier,
            local_queue,
            injector,
            route_to_injector,
            &frontier_batch,
            &injector_pushes,
        );
        let producer_worker = self.worker_id;
        let preserve_complete_fp_cache =
            super::super::super::parallel_preserve_value_fps() && T::preserves_complete_fp_cache();

        let inv_ctx = par_inv_ctx!(self);
        let stop_ctx = par_stop_ctx!(self);

        for (diff, succ_fp, combined_xor) in diffs.drain(..) {
            // Part of #3073: Materialize diff directly into an owned ArrayState.
            // Unlike the batch path (which uses a scratch buffer because ~95% of
            // successors are duplicates and never enqueued), ALL admitted diffs are
            // new states that will be enqueued. Using into_array_state_with_fp +
            // move eliminates the N Value clones that scratch.clone() required.
            let t_mat = timing_start();
            let succ = if preserve_complete_fp_cache {
                diff.into_array_state_with_complete_fp_cache(
                    base_array,
                    succ_fp,
                    combined_xor,
                    var_reg,
                )
            } else {
                diff.into_array_state_with_fp(base_array, succ_fp, combined_xor)
            };
            accum_ns(&mut self.stats.materialize_ns, t_mat);

            // Collision diagnostics (if enabled).
            if let Some(diagnostics) = stop_ctx.collision_diagnostics {
                diagnostics.record_state(succ_fp, &succ, succ_depth);
            }

            // Part of #3254: Time invariant check for admitted diffs.
            let t_inv = timing_start();
            // Invariant check — the only per-successor work remaining.
            let outcome = observe_admitted_successor(
                &mut self.ctx,
                &inv_ctx,
                &stop_ctx,
                &self.result_tx,
                &mut self.stats,
                &SuccessorObservationCtx {
                    current: base_array,
                    parent_fp,
                    succ: &succ,
                    succ_fp,
                    succ_depth,
                    succ_level,
                },
            );
            accum_ns(&mut self.stats.invariant_ns, t_inv);
            self.stats.jit_hits += inv_ctx.jit_hits.get();
            self.stats.jit_misses += inv_ctx.jit_misses.get();
            self.stats.jit_fallback += inv_ctx.jit_fallback.get();
            self.stats.jit_not_compiled += inv_ctx.jit_not_compiled.get();
            self.stats.jit_verify_checked += inv_ctx.jit_verify_checked.get();
            self.stats.jit_verify_mismatches += inv_ctx.jit_verify_mismatches.get();
            inv_ctx.jit_hits.set(0);
            inv_ctx.jit_misses.set(0);
            inv_ctx.jit_fallback.set(0);
            inv_ctx.jit_not_compiled.set(0);
            inv_ctx.jit_verify_checked.set(0);
            inv_ctx.jit_verify_mismatches.set(0);

            match outcome {
                InvariantOutcome::Ok | InvariantOutcome::ViolationContinued => {
                    // Enqueue for further BFS exploration. Move instead of clone
                    // since the ArrayState is freshly created and won't be reused.
                    let item = T::from_array_state(succ, var_reg, mode_ref, producer_worker);
                    enqueue_route.enqueue(item, succ_depth);
                    self.stats.states_generated += 1;
                }
                InvariantOutcome::Violation { invariant, .. } => {
                    snapshot_stop_and_send(
                        &self.ctx,
                        &mut self.stats,
                        &stop_ctx,
                        &self.result_tx,
                        |stats| WorkerResult::Violation {
                            invariant,
                            state_fp: succ_fp,
                            stats,
                        },
                    );
                    self.stats.injector_pushes += enqueue_route.injector_pushes();
                    return true;
                }
                InvariantOutcome::Error(error) => {
                    snapshot_stop_and_send(
                        &self.ctx,
                        &mut self.stats,
                        &stop_ctx,
                        &self.result_tx,
                        |stats| WorkerResult::Error(error, stats),
                    );
                    self.stats.injector_pushes += enqueue_route.injector_pushes();
                    return true;
                }
            }
        }

        enqueue_route.finish();
        self.stats.injector_pushes += enqueue_route.injector_pushes();
        false
    }

    pub(super) fn can_streaming_preadmit(&self) -> bool {
        !self.store_full_states && self.max_states_limit.is_none()
    }
}
