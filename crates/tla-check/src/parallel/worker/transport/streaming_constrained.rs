// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constrained streaming diff successor processing for parallel BFS transport.
//!
//! Part of #3273: sibling to `streaming.rs` that handles specs with
//! CONSTRAINT / ACTION_CONSTRAINT. The unconstrained streaming path rejects
//! constrained specs because `supports_diffs()` returns false when constraints
//! are present. But diff enumeration itself works fine — only the batch diff
//! reducer can't handle constraints.
//!
//! Phase A: enumerate through the sink-based AST path.
//! Phase B: process each diff immediately through the constrained fallback
//! pipeline via `DiffSink::push_with_ctx`.
//!
//! Extracted from `streaming.rs` to keep file sizes under 500 lines.

use super::super::work_item::BfsWorkItem;
use super::super::worker_bfs_ctx::WorkerBfsCtx;
#[allow(unused_imports)]
use super::super::{InvariantCheckCtx, StopCtx};
use super::enqueue::route_successor_batch_to_injector;
use super::shared_queue::SHARED_QUEUE_BATCH_SIZE;
use super::ParallelTransport;
use crate::check::model_checker::bfs::transport::BfsTermination;
use crate::state::{ArrayState, Fingerprint};
use smallvec::SmallVec;
use std::cell::{Cell, RefCell};

impl<T: BfsWorkItem> ParallelTransport<T> {
    pub(super) fn constrained_streaming_eligible(&self) -> bool {
        let has_constraints =
            !self.config.constraints.is_empty() || !self.config.action_constraints.is_empty();
        let can_enumerate_diffs = self.config.view.is_none() && self.config.symmetry.is_none();

        !self.force_batch
            && can_enumerate_diffs
            && self.por_independence.is_none()
            && has_constraints
            && self.eval_implied_actions.is_empty()
            && self.successors_cache.is_none()
            && self.successor_witnesses_cache.is_none()
    }

    /// Try the constrained streaming diff path.
    ///
    /// Part of #3273: Sibling to `try_streaming_process` for specs with
    /// CONSTRAINT / ACTION_CONSTRAINT. The unconstrained streaming path
    /// rejects these specs because `supports_diffs()` returns false when
    /// constraints are present. But diff enumeration itself works fine with
    /// constraints — only the batch diff reducer can't handle them.
    ///
    /// Phase A enumerates with the same AST path as the legacy constrained
    /// fallback and emits diffs through the sink-based API.
    ///
    /// This intentionally bypasses compiled/split-action enumeration. The
    /// existing constrained fallback calls
    /// `enumerate_successors_array_as_diffs(..., None)`, so this path
    /// must preserve the same AST semantics before it can be evaluated for
    /// performance. Constraint checking still happens after enumeration
    /// because it needs the worker-owned `EvalCtx`.
    ///
    /// Phase B processes each emitted diff immediately through the
    /// constrained fallback pipeline: materialize → constraint check →
    /// transition count → admit/dedup → invariant → enqueue.
    ///
    /// First-slice scope: no VIEW, no symmetry, no implied actions, no
    /// liveness caches. This targets the MCBoulanger-shaped lane.
    ///
    /// Returns:
    /// - `Some(Ok(()))` if streaming handled the state successfully
    /// - `Some(Err(BfsTermination::Exit))` on terminal error
    /// - `None` if constrained streaming is not eligible
    pub(in crate::parallel) fn try_streaming_constrained_process(
        &mut self,
        fp: Fingerprint,
        current: &ArrayState,
        succ_depth: usize,
        current_level: u32,
        succ_level: u32,
    ) -> Option<Result<(), BfsTermination>> {
        if !self.constrained_streaming_eligible() {
            return None;
        }

        let def = self.op_defs.get(&self.next_name)?;
        let tir_program = Self::next_tir_program(
            &self.parallel_tir_next_selection,
            &self.module,
            &self.extended_modules,
            &self.tir_caches,
        );

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

        let terminated = wctx.enumerate_and_process_constrained_streaming(
            def,
            &self.vars,
            tir_program.as_ref(),
            current,
            fp,
            current_level,
            succ_depth,
            succ_level,
            enqueue,
        );
        enqueue_route.finish();
        self.stats.injector_pushes += enqueue_route.injector_pushes();
        if terminated {
            Some(Err(BfsTermination::Exit))
        } else {
            Some(Ok(()))
        }
    }
}
