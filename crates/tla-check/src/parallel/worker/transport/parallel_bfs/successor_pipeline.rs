// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Successor-generation pipeline for the parallel BFS transport.
//!
//! Contains `process_successors_inner`, the core per-state successor enumeration
//! and routing logic. Extracted from `parallel_bfs.rs` for file size compliance
//! (#3546).

use super::super::super::coordination::snapshot_stop_and_send;
use super::super::super::helpers::compute_view_fingerprint_array;
use super::super::super::work_item::BfsWorkItem;
use super::super::super::worker_bfs_ctx::WorkerBfsCtx;
use super::super::super::WorkerResult;
use super::super::enqueue::route_successor_batch_to_injector;
use super::super::shared_queue::SHARED_QUEUE_BATCH_SIZE;
use super::super::ParallelTransport;
use crate::check::model_checker::bfs::transport::BfsTermination;
use crate::state::{ArrayState, Fingerprint};
use crate::{ConfigCheckError, EvalCheckError};
use smallvec::SmallVec;
use std::cell::{Cell, RefCell};

impl<T: BfsWorkItem> ParallelTransport<T> {
    pub(super) fn process_successors_inner(
        &mut self,
        fp: Fingerprint,
        current: &ArrayState,
        succ_depth: usize,
        current_level: u32,
        succ_level: u32,
    ) -> Result<(), BfsTermination> {
        self.ctx.set_tlc_level(current_level);

        // Part of #3083: update TLCGet("stats") runtime stats from shared atomics.
        // Uses Relaxed loads — values are approximate but non-zero, which is the
        // key improvement over the hardcoded-zero fallback in builtin_tlc_get.rs.
        {
            let distinct = self
                .admitted_states
                .load(std::sync::atomic::Ordering::Relaxed) as i64;
            let queue = self
                .work_remaining
                .load(std::sync::atomic::Ordering::Relaxed) as i64;
            let generated = self
                .total_transitions
                .load(std::sync::atomic::Ordering::Relaxed) as i64;
            self.ctx
                .set_tlc_runtime_stats(Some(crate::eval::TlcRuntimeStats::new(
                    generated,
                    distinct,
                    queue,
                    0, // traces: not applicable in BFS mode
                    i64::from(current_level),
                )));
        }

        if !self.op_defs.contains_key(&self.next_name) {
            let stop_ctx = par_stop_ctx!(self);
            snapshot_stop_and_send(
                &self.ctx,
                &mut self.stats,
                &stop_ctx,
                &self.result_tx,
                |stats| WorkerResult::Error(ConfigCheckError::MissingNext.into(), stats),
            );
            return Err(BfsTermination::Exit);
        }

        // Wave 11a (Part of #4267): JIT next-state dispatch removed.
        // The block formerly here attempted to evaluate Next via a
        // compiled Cranelift JitNextStateCache when the monolithic
        // action was promoted to Tier 1, but always fell through to the
        // interpreter. With the Cranelift JIT being deleted (Epic
        // #4251), `is_promoted_to_jit()` is always false and the path
        // was pure dead instrumentation.

        // Part of #3027 Phase 5: streaming diff path with inline dedup.
        if let Some(r) = self.try_streaming_process(fp, current, succ_depth, succ_level) {
            return r;
        }

        // Part of #3273: constrained streaming diff path. Handles specs with
        // CONSTRAINT / ACTION_CONSTRAINT that the unconstrained streaming path
        // rejects by sending each emitted diff directly through the shared
        // constrained fallback reducer.
        if let Some(r) = self.try_streaming_constrained_process(
            fp,
            current,
            succ_depth,
            current_level,
            succ_level,
        ) {
            return r;
        }

        let def = match self.op_defs.get(&self.next_name) {
            Some(def) => def,
            None => return Err(BfsTermination::Exit),
        };
        let tir_program = Self::next_tir_program(
            &self.parallel_tir_next_selection,
            &self.module,
            &self.extended_modules,
            &self.tir_caches,
        );

        // Diff-based enumeration fast path.
        let diff_result = if self.use_diffs {
            match T::try_diff_enumerate(
                current,
                &mut self.ctx,
                def,
                &self.vars,
                &self.var_registry,
                &self.mode,
                tir_program.as_ref(),
            ) {
                Ok(r) => r,
                Err(e) => {
                    let stop_ctx = par_stop_ctx!(self);
                    snapshot_stop_and_send(
                        &self.ctx,
                        &mut self.stats,
                        &stop_ctx,
                        &self.result_tx,
                        |stats| WorkerResult::Error(EvalCheckError::Eval(e).into(), stats),
                    );
                    return Err(BfsTermination::Exit);
                }
            }
        } else {
            None
        };

        // Pre-compute VIEW fingerprint while &mut self.ctx is available.
        // Part of #3022: Operates on ArrayState directly — no State/OrdMap conversion.
        let view_fp = if diff_result.is_none() {
            if let Some(ref view_name) = self.cached_view_name {
                match compute_view_fingerprint_array(
                    &mut self.ctx,
                    current,
                    view_name,
                    current_level,
                ) {
                    Ok(vfp) => vfp,
                    Err(e) => {
                        let stop_ctx = par_stop_ctx!(self);
                        snapshot_stop_and_send(
                            &self.ctx,
                            &mut self.stats,
                            &stop_ctx,
                            &self.result_tx,
                            |stats| WorkerResult::Error(e, stats),
                        );
                        return Err(BfsTermination::Exit);
                    }
                }
            } else {
                fp
            }
        } else {
            fp // unused when diff path is taken
        };

        // Bind references for enqueue closure before creating WorkerBfsCtx
        // (field-level borrow splitting requires local bindings).
        let var_reg = &*self.var_registry;
        let mode_ref = &self.mode;
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
            let item = T::from_array_state(succ_arr, var_reg, mode_ref, producer_worker);
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

        if let Some(independence) = self.por_independence.as_ref() {
            let terminated = wctx.enumerate_and_process_with_por(
                def,
                &self.vars,
                &self.por_actions,
                independence,
                self.por_visibility.as_ref(),
                &self.cached_view_name,
                current,
                view_fp,
                current_level,
                succ_depth,
                succ_level,
                enqueue,
            );
            enqueue_route.finish();
            self.stats.injector_pushes += enqueue_route.injector_pushes();
            if terminated {
                return Err(BfsTermination::Exit);
            }
            return Ok(());
        }

        if let Some((diffs, base_array, rebuilt_base_fp_cache)) = diff_result {
            wctx.stats.base_fp_cache_rebuilds += usize::from(rebuilt_base_fp_cache);
            let terminated =
                wctx.process_diffs(&base_array, fp, succ_depth, succ_level, diffs, enqueue);
            enqueue_route.finish();
            self.stats.injector_pushes += enqueue_route.injector_pushes();
            if terminated {
                return Err(BfsTermination::Exit);
            }
            return Ok(());
        }

        // State-based enumeration fallback.
        // Part of #3022: Pass ArrayState directly — no State/OrdMap conversion.
        let terminated = wctx.enumerate_and_process(
            def,
            &self.vars,
            &self.cached_view_name,
            tir_program.as_ref(),
            current,
            view_fp,
            current_level,
            succ_depth,
            succ_level,
            enqueue,
        );
        enqueue_route.finish();
        self.stats.injector_pushes += enqueue_route.injector_pushes();
        if terminated {
            return Err(BfsTermination::Exit);
        }
        Ok(())
    }
}
