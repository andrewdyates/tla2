// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared-queue parallel BFS transport (Part of #3258, #3271).
//!
//! Env-gated pilot (`TLA2_SHARED_QUEUE=1`) that replaces per-worker deques
//! and work-stealing with a single globally-visible FIFO frontier. This matches
//! TLC's `StateQueue` topology for direct throughput comparison on cheap-state
//! specs like MCBoulanger.
//!
//! Part of #3271: `SharedFrontier` (in `shared_frontier.rs`) now owns the
//! termination contract via condvar-based wait/notify instead of external
//! `work_remaining` / `active_workers` atomics.

use super::super::work_item::BfsWorkItem;
use super::super::worker_bfs_ctx::WorkerBfsCtx;
use super::super::{InvariantCheckCtx, StopCtx, WorkerModelConfig, WorkerSharedState};
use crate::check::model_checker::bfs::transport::BfsTermination;
use crate::config::Config;
use crate::eval::EvalCtx;
use crate::parallel::{FxDashMap, WorkBarrier, WorkerResult, WorkerStats};
use crate::state::{ArrayState, Fingerprint};
use crate::storage::FingerprintSet;
use crate::var_index::VarRegistry;
use crate::{ConfigCheckError, EvalCheckError};

use super::super::coordination::snapshot_stop_and_send;
use super::super::helpers::compute_view_fingerprint_array;

use crossbeam_channel::Sender;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::cell::RefCell;
use std::sync::atomic::{AtomicBool, AtomicUsize};
use std::sync::{Arc, OnceLock};
use tla_core::ast::{Module, OperatorDef};
use tla_eval::tir::TirProgram;

/// Batch size for local staging buffers. Matches TLC's `DiskStateQueue.BufSize`
/// concept: most queue operations stay local, only flushing/refilling in batches.
pub(super) const SHARED_QUEUE_BATCH_SIZE: usize = 64;

// Re-export SharedFrontier and DequeueOutcome from the split module.
pub(in crate::parallel) use super::shared_frontier::{DequeueOutcome, SharedFrontier};

/// Construct a `StopCtx` from `SharedQueueTransport` fields.
macro_rules! sq_stop_ctx {
    ($self:expr) => {
        StopCtx {
            stop_flag: &$self.stop_flag,
            states_at_stop: &$self.states_at_stop,
            seen: &$self.seen,
            seen_fps: &*$self.seen_fps,
            store_full_states: $self.store_full_states,
            cache_for_liveness: $self.successors_cache.is_some(),
            admitted_states: &$self.admitted_states,
            max_states_limit: $self.max_states_limit,
            collision_diagnostics: $self.collision_diagnostics.as_deref(),
        }
    };
}

/// Construct an `InvariantCheckCtx` from `SharedQueueTransport` fields.
macro_rules! sq_inv_ctx {
    ($self:expr) => {
        InvariantCheckCtx {
            config: &$self.config,
            eval_implied_actions: &$self.eval_implied_actions,
            eval_state_invariants: &$self.eval_state_invariants,
            uses_trace: $self.uses_trace,
            store_full_states: $self.store_full_states,
            continue_on_error: $self.continue_on_error,
            first_violation: &$self.first_violation,
            first_action_property_violation: &$self.first_action_property_violation,
            parent_log: &$self.parent_log,
            worker_id: $self.worker_id,
            seen: &$self.seen,
            var_registry: &$self.var_registry,
            depths: &$self.depths,
            track_depths: $self.track_depths,
            bytecode: &$self.bytecode,
            jit_cache: &$self.jit_cache,
            jit_state_scratch: &$self.jit_state_scratch,
            jit_hits: std::cell::Cell::new(0),
            jit_misses: std::cell::Cell::new(0),
            jit_fallback: std::cell::Cell::new(0),
            jit_not_compiled: std::cell::Cell::new(0),
            jit_verify_checked: std::cell::Cell::new(0),
            jit_verify_mismatches: std::cell::Cell::new(0),
            action_constraint_analysis: $self.action_constraint_analysis.as_deref(),
        }
    };
}

/// Shared-queue parallel BFS transport with queue-owned termination (Part of #3271).
///
/// Implements `BfsTransport` using a shared `SharedFrontier` instead of
/// per-worker deques and injector/stealer mechanics. The successor processing
/// pipeline is identical to `ParallelTransport` — only the queue topology
/// and termination mechanism change.
///
/// Unlike the work-stealing `ParallelTransport`, termination is detected by
/// the frontier itself: when all workers are blocked in
/// `dequeue_batch_blocking()` with an empty queue, completion is signaled
/// via condvar — no external `active_workers` tracking needed.
pub(in crate::parallel) struct SharedQueueTransport<T: BfsWorkItem> {
    pub(super) worker_id: usize,
    pub(super) frontier: Arc<SharedFrontier<T>>,
    /// Tracks whether this worker still owns a current-level frontier batch.
    pub(super) frontier_batch_active: bool,
    /// Worker-local dequeue cache: items popped from the shared frontier.
    pub(super) dequeue_batch: SmallVec<[(T, usize); SHARED_QUEUE_BATCH_SIZE]>,
    pub(super) ctx: EvalCtx,
    pub(super) stats: WorkerStats,
    pub(super) stop_flag: Arc<AtomicBool>,
    /// Kept for `ParallelAdapter::admit()` work counting — not used for
    /// termination (Part of #3271: frontier condvar handles that).
    pub(super) work_remaining: Arc<AtomicUsize>,
    pub(super) depth_limit_reached: Arc<AtomicBool>,
    pub(super) max_depth_atomic: Arc<AtomicUsize>,
    pub(super) total_transitions: Arc<AtomicUsize>,
    pub(super) states_at_stop: Arc<OnceLock<usize>>,
    pub(super) seen: Arc<FxDashMap<Fingerprint, ArrayState>>,
    pub(super) seen_fps: Arc<dyn FingerprintSet>,
    pub(super) admitted_states: Arc<AtomicUsize>,
    pub(super) collision_diagnostics: Option<Arc<crate::parallel::ParallelCollisionDiagnostics>>,
    pub(super) max_states_limit: Option<usize>,
    pub(super) result_tx: Sender<WorkerResult>,
    pub(super) vars: Vec<Arc<str>>,
    pub(super) op_defs: FxHashMap<String, OperatorDef>,
    pub(super) por_actions: Arc<Vec<crate::coverage::DetectedAction>>,
    pub(super) por_independence: Option<Arc<crate::por::IndependenceMatrix>>,
    pub(super) por_visibility: Arc<crate::por::VisibilitySet>,
    pub(super) module: Arc<Module>,
    pub(super) extended_modules: Arc<Vec<Module>>,
    pub(super) next_name: String,
    pub(super) parallel_tir_next_selection: Option<crate::tir_mode::ParallelNextTirEvalSelection>,
    pub(super) mode: T::Mode,
    pub(super) var_registry: Arc<VarRegistry>,
    pub(super) check_deadlock: bool,
    pub(super) use_diffs: bool,
    pub(super) cached_view_name: Option<String>,
    pub(super) config: Config,
    pub(super) eval_implied_actions: Arc<Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>>,
    pub(super) eval_state_invariants: Arc<Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>>,
    pub(super) uses_trace: bool,
    pub(super) store_full_states: bool,
    pub(super) continue_on_error: bool,
    pub(super) first_violation: Arc<OnceLock<(String, Fingerprint)>>,
    pub(super) first_action_property_violation: Arc<OnceLock<(String, Fingerprint)>>,
    /// Part of #3178: Shared parent log replaces DashMap.
    pub(super) parent_log: Arc<crate::parallel::ParentLog>,
    pub(super) successors_cache: Option<Arc<FxDashMap<Fingerprint, Vec<Fingerprint>>>>,
    pub(super) successor_witnesses_cache: Option<Arc<crate::parallel::SuccessorWitnessDashMap>>,
    pub(super) mvperms: Arc<Vec<crate::value::MVPerm>>,
    /// Kept for `ParallelAdapter::admit()` batched work counting — not used
    /// for termination (Part of #3271).
    pub(super) local_work_delta: isize,
    pub(super) barrier: Arc<WorkBarrier>,
    pub(super) depths: Arc<FxDashMap<Fingerprint, usize>>,
    pub(super) track_depths: bool,
    pub(super) decode_scratch: Option<ArrayState>,
    pub(super) current_uses_decode_scratch: bool,
    /// Part of #3392: Per-worker TIR caches for cross-state persistence.
    pub(super) tir_caches: tla_eval::tir::TirProgramCaches,
    /// Critical RSS threshold in bytes for per-worker inline memory checks.
    pub(super) critical_rss_bytes: Option<usize>,
    /// Counter for inline RSS check frequency (every 10,000 states).
    pub(super) states_since_rss_check: u32,
    /// Part of #3621: Compiled bytecode for invariant fast path, shared across workers.
    pub(super) bytecode: Option<Arc<tla_eval::bytecode_vm::CompiledBytecode>>,
    /// Part of #3700: Shared JIT cache for invariant hot-path dispatch.
    pub(super) jit_cache: Option<crate::parallel::SharedJitInvariantCache>,
    /// Part of #3700: Reusable scalar-state scratch for JIT checks in this worker.
    pub(super) jit_state_scratch: RefCell<Vec<i64>>,
    pub(super) action_constraint_analysis:
        Option<Arc<crate::checker_ops::ActionConstraintAnalysis>>,
    /// Part of #3910: Per-worker scratch buffer for JIT next-state flattening.
    pub(super) jit_next_state_scratch: RefCell<Vec<i64>>,
    /// Part of #3910: Shared tiered JIT state for parallel promotion tracking.
    pub(super) tier_state: Option<Arc<crate::parallel::tier_state::SharedTierState>>,
    /// Part of #4053: Skip materialization when spec has no lazy-producing AST nodes.
    pub(super) spec_may_produce_lazy: bool,
}

impl<T: BfsWorkItem> SharedQueueTransport<T> {
    pub(in crate::parallel) fn new(
        worker_id: usize,
        frontier: Arc<SharedFrontier<T>>,
        ctx: EvalCtx,
        shared: WorkerSharedState,
        model: WorkerModelConfig,
        mode: T::Mode,
    ) -> Self {
        let use_diffs = T::supports_diffs(&model.config) && model.por_independence.is_none();
        let WorkerSharedState {
            seen,
            seen_fps,
            parent_log,
            stop_flag,
            depth_limit_reached,
            work_remaining,
            active_workers: _, // Part of #3271: frontier condvar handles termination
            bootstrap_injector_budget: _, // not used in shared-queue mode
            shared_frontier_tail_mode: _, // not used in shared-queue mode
            max_queue: _,      // no per-worker queue to track in shared mode
            max_depth_atomic,
            total_transitions,
            result_tx,
            first_violation,
            first_action_property_violation,
            states_at_stop,
            admitted_states,
            collision_diagnostics,
            successors: successors_cache,
            successor_witnesses: successor_witnesses_cache,
            barrier,
            depths,
            tier_state,
        } = shared;
        let WorkerModelConfig {
            module,
            extended_modules,
            unqualified_modules: _,
            vars,
            op_defs,
            por_actions,
            por_independence,
            por_visibility,
            config,
            check_deadlock,
            next_name,
            parallel_tir_next_selection,
            num_workers: _,
            max_states_limit,
            store_full_states,
            uses_trace,
            var_registry,

            eval_implied_actions,
            eval_state_invariants,
            continue_on_error,
            cached_view_name,
            mvperms,
            track_depths,
            max_depth_limit: _,
            input_base_dir: _,
            critical_rss_bytes,
            bytecode,
            jit_cache,
            action_constraint_analysis,
            spec_may_produce_lazy,
        } = model;
        let decode_scratch =
            T::requires_decode_scratch().then(|| ArrayState::new(var_registry.len()));
        Self {
            worker_id,
            frontier,
            frontier_batch_active: false,
            dequeue_batch: SmallVec::new(),
            ctx,
            stats: WorkerStats {
                worker_id: Some(worker_id),
                ..WorkerStats::default()
            },
            stop_flag,
            work_remaining,
            depth_limit_reached,
            max_depth_atomic,
            total_transitions,
            states_at_stop,
            seen,
            seen_fps,
            admitted_states,
            collision_diagnostics,
            max_states_limit,
            result_tx,
            vars,
            op_defs,
            por_actions,
            por_independence,
            por_visibility,
            module,
            extended_modules,
            next_name,
            parallel_tir_next_selection,
            mode,
            var_registry,
            check_deadlock,
            use_diffs,
            cached_view_name,
            config,

            eval_implied_actions,
            eval_state_invariants,
            uses_trace,
            store_full_states,
            continue_on_error,
            first_violation,
            first_action_property_violation,
            parent_log,
            successors_cache,
            successor_witnesses_cache,
            mvperms,
            local_work_delta: 0,
            barrier,
            depths,
            track_depths,
            decode_scratch,
            current_uses_decode_scratch: false,
            tir_caches: tla_eval::tir::TirProgramCaches::new(),
            critical_rss_bytes,
            states_since_rss_check: 0,
            bytecode,
            jit_cache,
            jit_state_scratch: RefCell::new(Vec::new()),
            action_constraint_analysis,
            jit_next_state_scratch: RefCell::new(Vec::new()),
            tier_state,
            spec_may_produce_lazy,
        }
    }

    /// Build `TirProgram` from disjoint field borrows (not `&self`) to avoid
    /// blocking `&mut self.ctx` / `&mut self.stats` during successor processing.
    /// Part of #3285: parallel-leaf-TIR evaluator slice.
    /// Part of #3392: uses per-worker shared caches for cross-state persistence.
    fn next_tir_program<'a>(
        selection: &Option<crate::tir_mode::ParallelNextTirEvalSelection>,
        module: &'a Module,
        extended_modules: &'a [Module],
        caches: &'a tla_eval::tir::TirProgramCaches,
    ) -> Option<TirProgram<'a>> {
        selection
            .as_ref()
            .and_then(|s| s.tir_program_with_cache(module, extended_modules, caches))
    }

    pub(super) fn reclaim_decode_scratch(&mut self, current: ArrayState) {
        if self.current_uses_decode_scratch {
            debug_assert!(self.decode_scratch.is_none());
            let replaced = self.decode_scratch.replace(current);
            debug_assert!(replaced.is_none());
            self.current_uses_decode_scratch = false;
        }
    }

    /// Successor processing: shared with ParallelTransport except for the
    /// enqueue target (shared frontier instead of local queue + injector).
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

        // Wave 11a (Part of #4267): JIT next-state dispatch removed.
        // See `parallel_bfs/successor_pipeline.rs` for the equivalent
        // removal rationale. The Cranelift JIT is being deleted (Epic
        // #4251) and `is_promoted_to_jit()` always returns false, so
        // the dispatch block was dead instrumentation.

        let def = match self.op_defs.get(&self.next_name) {
            Some(def) => def,
            None => {
                let stop_ctx = sq_stop_ctx!(self);
                snapshot_stop_and_send(
                    &self.ctx,
                    &mut self.stats,
                    &stop_ctx,
                    &self.result_tx,
                    |stats| WorkerResult::Error(ConfigCheckError::MissingNext.into(), stats),
                );
                return Err(BfsTermination::Exit);
            }
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
                    let stop_ctx = sq_stop_ctx!(self);
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
                        let stop_ctx = sq_stop_ctx!(self);
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
            fp
        };

        // Batch successors locally, flush to shared frontier at threshold.
        // Uses RefCell for interior mutability so the closure is Fn-compatible
        // (process_diffs/enumerate_and_process require Fn, not FnMut).
        let var_reg = &*self.var_registry;
        let mode_ref = &self.mode;
        let producer_worker = self.worker_id;
        let frontier = &self.frontier;
        let enqueue_batch: RefCell<SmallVec<[(T, usize); SHARED_QUEUE_BATCH_SIZE]>> =
            RefCell::new(SmallVec::new());
        let enqueue = |succ_arr: ArrayState, enq_depth: usize| {
            let item = T::from_array_state(succ_arr, var_reg, mode_ref, producer_worker);
            let mut batch = enqueue_batch.borrow_mut();
            batch.push((item, enq_depth));
            if batch.len() >= SHARED_QUEUE_BATCH_SIZE {
                frontier.push_batch(&mut batch);
            }
        };

        let inv_ctx = sq_inv_ctx!(self);
        let stop_ctx = sq_stop_ctx!(self);
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
            frontier.push_batch(&mut enqueue_batch.borrow_mut());
            if terminated {
                return Err(BfsTermination::Exit);
            }
            return Ok(());
        }

        if let Some((diffs, base_array, rebuilt_base_fp_cache)) = diff_result {
            wctx.stats.base_fp_cache_rebuilds += usize::from(rebuilt_base_fp_cache);
            let terminated =
                wctx.process_diffs(&base_array, fp, succ_depth, succ_level, diffs, enqueue);
            frontier.push_batch(&mut enqueue_batch.borrow_mut());
            if terminated {
                return Err(BfsTermination::Exit);
            }
            return Ok(());
        }

        // State-based enumeration fallback.
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
        frontier.push_batch(&mut enqueue_batch.borrow_mut());
        if terminated {
            return Err(BfsTermination::Exit);
        }
        Ok(())
    }
}
