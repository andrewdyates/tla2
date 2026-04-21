// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Streaming diff successor processing for parallel BFS transport.
//!
//! Part of #3027 Phase 5: uses `ClosureSink` with split borrows for inline
//! dedup during enumeration. Part of #3254: upgrades speculative dedup to
//! authoritative `insert_checked` for non-lazy diffs in fp-only mode,
//! eliminating the race window between Phase A and Phase B.
//!
//! Extracted from `transport/mod.rs` to keep file sizes under 500 lines.

use super::super::super::timing_start;
use super::super::coordination::{record_state_completion_profiled, snapshot_stop_and_send};
use super::super::observer::{observe_state_completion, ObservationSignal, StateCompletionCtx};
use super::super::work_item::BfsWorkItem;
use super::super::worker_bfs_ctx::WorkerBfsCtx;
use super::super::WorkerResult;
#[allow(unused_imports)]
use super::super::{InvariantCheckCtx, StopCtx};
use super::enqueue::route_successor_batch_to_injector;
use super::shared_queue::SHARED_QUEUE_BATCH_SIZE;
use super::ParallelTransport;
use crate::check::model_checker::bfs::transport::BfsTermination;
use crate::enumerate::ClosureSink;
use crate::materialize::has_lazy_state_value;
use crate::state::{compute_diff_fingerprint_with_xor, ArrayState, DiffSuccessor, Fingerprint};
use crate::storage::{InsertOutcome, LookupOutcome};
use crate::EvalCheckError;
use smallvec::SmallVec;
use std::cell::{Cell, RefCell};
use std::ops::ControlFlow;
use std::sync::atomic::Ordering;

impl<T: BfsWorkItem> ParallelTransport<T> {
    /// Try the streaming diff path with inline dedup.
    ///
    /// Part of #3027 Phase 5, upgraded by #3254. Returns:
    /// - `Some(Ok(()))` if streaming handled the state successfully
    /// - `Some(Err(BfsTermination::Exit))` on terminal error (deadlock, fault)
    /// - `None` if streaming is not eligible (caller falls through to batch)
    ///
    /// Eligibility: use_diffs && no implied actions && no constraints && no
    /// liveness caching. When eligible, Phase A enumerates successors through
    /// a `ClosureSink` that fingerprints and dedup-checks inline. Phase B
    /// feeds pre-deduped diffs through the existing `process_diffs` pipeline.
    ///
    /// Part of #3254: For non-lazy diffs in fp-only mode (no `store_full_states`,
    /// no `max_states_limit`), Phase A performs authoritative `insert_checked`
    /// instead of speculative `contains_checked`. This makes new states visible
    /// to other workers immediately during enumeration, reducing cross-worker
    /// duplicate work. Pre-admitted diffs skip the admit step in Phase B.
    pub(in crate::parallel) fn try_streaming_process(
        &mut self,
        fp: Fingerprint,
        current: &ArrayState,
        succ_depth: usize,
        succ_level: u32,
    ) -> Option<Result<(), BfsTermination>> {
        let streaming_eligible = !self.force_batch
            && self.use_diffs
            && self.eval_implied_actions.is_empty()
            && self.config.constraints.is_empty()
            && self.config.action_constraints.is_empty()
            && self.successors_cache.is_none()
            && self.successor_witnesses_cache.is_none();

        if !streaming_eligible {
            return None;
        }

        // Look up Next operator definition (caller already validated it exists).
        let def = self.op_defs.get(&self.next_name)?;
        let tir_program = Self::next_tir_program(
            &self.parallel_tir_next_selection,
            &self.module,
            &self.extended_modules,
            &self.tir_caches,
        );

        // Phase A accumulators — captured by the ClosureSink closure.
        // Part of #3254: admitted_diffs holds pre-admitted diffs (authoritative
        // insert done in Phase A). deferred_diffs holds diffs that need full
        // Phase B processing (lazy values or store_full mode).
        let mut admitted_diffs: Vec<(DiffSuccessor, Fingerprint, u64)> = Vec::new();
        let mut deferred_diffs: Vec<DiffSuccessor> = Vec::new();
        let mut total_count: usize = 0;
        let mut storage_fault: Option<crate::storage::StorageFault> = None;
        // Part of #3285: per-diff fingerprint timing sub-bucket.
        let mut enum_diff_fp_ns: u64 = 0;

        // Part of #3254: Authoritative insert is safe when:
        // - fp-only mode (no need for full ArrayState in seen map)
        // - no max_states_limit (can't roll back insert_checked on limit hit)
        let can_preadmit = self.can_streaming_preadmit();

        // Phase A: split borrows for enumeration + inline dedup.
        let t_enum = timing_start();
        let streaming_result = {
            let seen_fps = &*self.seen_fps;
            // Part of #3233: Also borrow `seen` DashMap for full-state dedup.
            // When `store_full_states=true`, `seen_fps` is unpopulated and the
            // old `seen_fps.contains_checked()` never filtered anything.
            let seen_map = &*self.seen;
            let store_full = self.store_full_states;
            let var_registry = &*self.var_registry;
            let current_ref = current;

            let mut sink = ClosureSink::new(|diff: DiffSuccessor| -> ControlFlow<()> {
                total_count += 1;

                // Part of #3254: Check if diff has lazy values needing
                // post-enumeration materialization. If so, the fingerprint
                // may change after materialization — can't do authoritative insert.
                // Part of #4053: Skip the per-value walk when the spec cannot produce lazy values.
                let has_lazy = self.spec_may_produce_lazy
                    && diff.changes.iter().any(|(_, v)| has_lazy_state_value(v));

                if can_preadmit && !has_lazy {
                    // Part of #3254: Authoritative insert — fingerprint is final.
                    // Part of #3285: time per-diff fingerprinting.
                    let t_fp = timing_start();
                    let (succ_fp, combined_xor) =
                        compute_diff_fingerprint_with_xor(current_ref, &diff.changes, var_registry);
                    if let Some(t) = t_fp {
                        enum_diff_fp_ns += t.elapsed().as_nanos() as u64;
                    }
                    match seen_fps.insert_checked(succ_fp) {
                        InsertOutcome::Inserted => {
                            admitted_diffs.push((diff, succ_fp, combined_xor));
                        }
                        InsertOutcome::AlreadyPresent => {
                            // Duplicate — rejected immediately during enumeration.
                        }
                        InsertOutcome::StorageFault(fault) => {
                            storage_fault = Some(fault);
                            return ControlFlow::Break(());
                        }
                        _ => unreachable!(),
                    }
                } else {
                    // Speculative dedup (existing behavior for lazy values or
                    // store_full mode). Fingerprint may change after materialization.
                    let succ_fp = if diff.fingerprint.0 != 0 {
                        diff.fingerprint
                    } else {
                        // Part of #3285: time per-diff fingerprinting.
                        let t_fp = timing_start();
                        let fp = compute_diff_fingerprint_with_xor(
                            current_ref,
                            &diff.changes,
                            var_registry,
                        )
                        .0;
                        if let Some(t) = t_fp {
                            enum_diff_fp_ns += t.elapsed().as_nanos() as u64;
                        }
                        fp
                    };

                    // Part of #3233: Speculative dedup against the correct seen
                    // structure. In full-state mode, check the DashMap (read lock
                    // only). In fp-only mode, check the CAS fingerprint set.
                    let is_present = if store_full {
                        seen_map.contains_key(&succ_fp)
                    } else {
                        match seen_fps.contains_checked(succ_fp) {
                            LookupOutcome::Present => true,
                            LookupOutcome::StorageFault(fault) => {
                                storage_fault = Some(fault);
                                return ControlFlow::Break(());
                            }
                            LookupOutcome::Absent => false,
                            _ => unreachable!(),
                        }
                    };
                    if is_present {
                        return ControlFlow::Continue(());
                    }

                    // Speculatively new (~5-20%) — collect for Phase B.
                    deferred_diffs.push(diff);
                }
                ControlFlow::Continue(())
            });

            T::try_streaming_diff_enumerate(
                current,
                &mut self.ctx,
                def,
                &self.vars,
                &self.var_registry,
                &self.mode,
                tir_program.as_ref(),
                &mut sink,
            )
        };
        // ---- Split borrow scope ends: &mut self is fully available ----
        // Part of #3285: capture per-state enum_ns delta for sub-bucket derivation.
        let enum_delta = t_enum.map(|t| t.elapsed().as_nanos() as u64).unwrap_or(0);
        self.stats.enum_ns += enum_delta;

        match streaming_result {
            Ok(Some((base_array, rebuilt_base_fp_cache, base_cache_ns))) => {
                self.stats.base_fp_cache_rebuilds += usize::from(rebuilt_base_fp_cache);
                // Part of #3285: accumulate Enumeration sub-buckets.
                self.stats.enum_base_cache_ns += base_cache_ns;
                self.stats.enum_diff_fp_ns += enum_diff_fp_ns;
                self.stats.enum_eval_ns +=
                    enum_delta.saturating_sub(base_cache_ns + enum_diff_fp_ns);
                // Storage fault — terminal error.
                if let Some(fault) = storage_fault {
                    let stop_ctx = par_stop_ctx!(self);
                    snapshot_stop_and_send(
                        &self.ctx,
                        &mut self.stats,
                        &stop_ctx,
                        &self.result_tx,
                        |stats| {
                            let error = crate::checker_ops::storage_fault_to_check_error(
                                &*self.seen_fps,
                                &fault,
                            );
                            WorkerResult::Error(error, stats)
                        },
                    );
                    return Some(Err(BfsTermination::Exit));
                }

                // Deadlock check (total_count == 0 means no successors at all).
                {
                    let inv_ctx = par_inv_ctx!(self);
                    let stop_ctx = par_stop_ctx!(self);
                    match observe_state_completion(
                        &mut self.ctx,
                        &inv_ctx,
                        &stop_ctx,
                        &self.result_tx,
                        &mut self.stats,
                        &StateCompletionCtx {
                            state_fp: fp,
                            state: current,
                            has_successors: total_count > 0,
                        },
                        self.check_deadlock,
                    ) {
                        Ok(ObservationSignal::Continue | ObservationSignal::Skip) => {}
                        Ok(ObservationSignal::Stop) => return Some(Err(BfsTermination::Exit)),
                        Ok(ObservationSignal::Invariant(_)) => {
                            debug_assert!(
                                false,
                                "state completion observers should not emit invariant outcomes"
                            );
                        }
                        Err(error) => {
                            snapshot_stop_and_send(
                                &self.ctx,
                                &mut self.stats,
                                &stop_ctx,
                                &self.result_tx,
                                |stats| WorkerResult::Error(error, stats),
                            );
                            return Some(Err(BfsTermination::Exit));
                        }
                    }
                }

                // Record transitions (all successors, including duplicates).
                self.stats.transitions += total_count;
                self.total_transitions
                    .fetch_add(total_count, Ordering::Relaxed);
                // Part of #3254: Count pre-admitted diffs for profiling.
                self.stats.streaming_preadmits += admitted_diffs.len();

                // All successors were duplicates — nothing to process.
                if admitted_diffs.is_empty() && deferred_diffs.is_empty() {
                    record_state_completion_profiled(
                        &mut self.local_work_delta,
                        &self.work_remaining,
                        Some(&mut self.stats),
                    );
                    return Some(Ok(()));
                }

                // Part of #3254: Phase B-admitted — process pre-admitted diffs.
                // These were authoritatively inserted in Phase A. Skip FPSet
                // admit; only invariant check + enqueue remain.
                if !admitted_diffs.is_empty()
                    && self.process_admitted_diffs(
                        &base_array,
                        fp,
                        succ_depth,
                        succ_level,
                        &mut admitted_diffs,
                    )
                {
                    return Some(Err(BfsTermination::Exit));
                }

                // Phase B-deferred: process through existing pipeline.
                // These diffs need full processing: materialize → re-fingerprint
                // → admit (authoritative insert) → invariant check → enqueue.
                if !deferred_diffs.is_empty() {
                    let deferred_count = deferred_diffs.len();

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
                    // Part of #3212: pass worker_id so HandleState interns into owner shard.
                    let producer_worker = self.worker_id;
                    let enqueue = |succ_arr: ArrayState, enq_depth: usize| {
                        let item =
                            T::from_array_state(succ_arr, var_reg, mode_ref, producer_worker);
                        enqueue_route.enqueue(item, enq_depth);
                    };

                    let inv_ctx = par_inv_ctx!(self);
                    let stop_ctx = par_stop_ctx!(self);
                    let mut wctx = WorkerBfsCtx {
                        ctx: &mut self.ctx,
                        inv_ctx: &inv_ctx,
                        stop: &stop_ctx,
                        result_tx: &self.result_tx,
                        stats: &mut self.stats,
                        check_deadlock: self.check_deadlock,
                        local_work_delta: &mut self.local_work_delta,
                        work_remaining: &self.work_remaining,
                        max_depth_atomic: &self.max_depth_atomic,
                        total_transitions: &self.total_transitions,
                        successors_cache: &self.successors_cache,
                        successor_witnesses_cache: &self.successor_witnesses_cache,
                        mvperms: &self.mvperms,
                        spec_may_produce_lazy: self.spec_may_produce_lazy,
                    };

                    let terminated = wctx.process_diffs(
                        &base_array,
                        fp,
                        succ_depth,
                        succ_level,
                        deferred_diffs,
                        enqueue,
                    );
                    enqueue_route.finish();
                    self.stats.injector_pushes += enqueue_route.injector_pushes();
                    if terminated {
                        return Some(Err(BfsTermination::Exit));
                    }

                    // Fix transition double-counting: process_diffs counted
                    // deferred_count transitions, but we already counted total_count.
                    self.stats.transitions -= deferred_count;
                    self.total_transitions
                        .fetch_sub(deferred_count, Ordering::Relaxed);
                } else {
                    // Only admitted diffs — need manual state completion.
                    // (When deferred_diffs exist, process_diffs handles this
                    // via flush_work_completion.)
                    record_state_completion_profiled(
                        &mut self.local_work_delta,
                        &self.work_remaining,
                        Some(&mut self.stats),
                    );
                }

                Some(Ok(()))
            }
            Ok(None) => None, // Streaming unavailable — fall through to batch.
            Err(e) => {
                let stop_ctx = par_stop_ctx!(self);
                snapshot_stop_and_send(
                    &self.ctx,
                    &mut self.stats,
                    &stop_ctx,
                    &self.result_tx,
                    |stats| WorkerResult::Error(EvalCheckError::Eval(e).into(), stats),
                );
                Some(Err(BfsTermination::Exit))
            }
        }
    }
}
