// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parallel BFS transport (#2356 Phase 4 Step 4c): work-stealing queue,
//! coordination atomics, and successor processing behind [`BfsTransport`].
//! Active worker tracking uses `worker_active` flag (not RAII) to avoid
//! self-referential borrows. Part of #3233: `active_workers` is only
//! modified on idle↔active transitions (queue-empty/steal events), not
//! per state. The fast path in `try_dequeue` pops the local queue without
//! touching shared atomics.

use super::coordination::{
    finish_if_stop_requested, flush_local_work_delta_profiled, send_done_result,
};
use super::work_item::BfsWorkItem;
use super::{WorkerModelConfig, WorkerSharedState};
use crate::config::Config;
use crate::eval::EvalCtx;
use crate::parallel::{FxDashMap, WorkBarrier, WorkerResult, WorkerStats};
use crate::state::{ArrayState, Fingerprint};
use crate::storage::FingerprintSet;
use crate::var_index::VarRegistry;
use crossbeam_channel::Sender;
use crossbeam_deque::{Injector, Stealer, Worker};
use smallvec::SmallVec;
use std::cell::RefCell;
use rustc_hash::FxHashMap;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, OnceLock};
use tla_core::ast::{Module, OperatorDef};
use tla_eval::tir::TirProgram;

/// Construct a `StopCtx` from `ParallelTransport` fields via field-level borrow splitting.
macro_rules! par_stop_ctx {
    ($self:expr) => {
        $crate::parallel::worker::StopCtx {
            stop_flag: &$self.stop_flag,
            states_at_stop: &$self.states_at_stop,
            seen: &$self.seen,
            seen_fps: &*$self.seen_fps,
            store_full_states: $self.store_full_states,
            // Part of #3175: derive liveness-active from successors presence.
            cache_for_liveness: $self.successors_cache.is_some(),
            admitted_states: &$self.admitted_states,
            max_states_limit: $self.max_states_limit,
            collision_diagnostics: $self.collision_diagnostics.as_deref(),
        }
    };
}

/// Construct an `InvariantCheckCtx` from `ParallelTransport` fields.
macro_rules! par_inv_ctx {
    ($self:expr) => {
        $crate::parallel::worker::InvariantCheckCtx {
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

mod batch_route; // Part of #3389: SuccessorBatchRoute extraction
mod enqueue;
mod parallel_bfs; // Part of #3389: BfsTransport impl + process_successors_inner
pub(in crate::parallel) mod shared_frontier; // Part of #3271: condvar-based frontier
pub(in crate::parallel) mod shared_queue; // Part of #3258
mod shared_queue_bfs; // Part of #3258: BfsTransport impl split for file-size
mod streaming; // after macros for textual scope (#3027 Phase 5)
mod streaming_admitted; // Part of #3397: extracted from streaming.rs for 500-line limit
mod streaming_constrained; // Part of #3273: constrained variant (after macros)
#[cfg(test)]
mod tests;

pub(in crate::parallel) use self::enqueue::initial_bootstrap_injector_budget;
#[cfg(test)]
use self::enqueue::BOOTSTRAP_INJECTOR_BATCH_BUDGET;
#[cfg(test)]
use self::enqueue::{enqueue_successor_item, route_successor_batch_to_injector};
use self::shared_queue::{SharedFrontier, SHARED_QUEUE_BATCH_SIZE};

/// Parallel BFS transport: multi-threaded BFS with work-stealing queue.
/// Part of #2356 Phase 4 Step 4c.
pub(in crate::parallel) struct ParallelTransport<T: BfsWorkItem> {
    /// Part of #3212: ID of this worker thread for owner-local interning.
    worker_id: usize,
    /// Fixed worker count for idle-aware injector routing decisions.
    num_workers: usize,
    local_queue: Worker<(T, usize)>,
    injector: Arc<Injector<(T, usize)>>,
    stealers: Arc<Vec<Stealer<(T, usize)>>>,
    shared_frontier: Arc<SharedFrontier<T>>,
    shared_frontier_tail_mode: Arc<AtomicBool>,
    shared_frontier_tail_published: bool,
    frontier_batch_active: bool,
    dequeue_batch: SmallVec<[(T, usize); SHARED_QUEUE_BATCH_SIZE]>,
    ctx: EvalCtx,
    stats: WorkerStats,
    stop_flag: Arc<AtomicBool>,
    work_remaining: Arc<AtomicUsize>,
    active_workers: Arc<AtomicUsize>,
    bootstrap_injector_budget: Arc<AtomicUsize>,
    depth_limit_reached: Arc<AtomicBool>,
    max_queue: Arc<AtomicUsize>,
    max_depth_atomic: Arc<AtomicUsize>,
    total_transitions: Arc<AtomicUsize>,
    states_at_stop: Arc<OnceLock<usize>>,
    seen: Arc<FxDashMap<Fingerprint, ArrayState>>,
    seen_fps: Arc<dyn FingerprintSet>,
    admitted_states: Arc<AtomicUsize>,
    collision_diagnostics: Option<Arc<crate::parallel::ParallelCollisionDiagnostics>>,
    max_states_limit: Option<usize>,
    result_tx: Sender<WorkerResult>,
    vars: Vec<Arc<str>>,
    op_defs: FxHashMap<String, OperatorDef>,
    por_actions: Arc<Vec<crate::coverage::DetectedAction>>,
    por_independence: Option<Arc<crate::por::IndependenceMatrix>>,
    por_visibility: Arc<crate::por::VisibilitySet>,
    module: Arc<Module>,
    extended_modules: Arc<Vec<Module>>,
    next_name: String,
    parallel_tir_next_selection: Option<crate::tir_mode::ParallelNextTirEvalSelection>,
    mode: T::Mode,
    var_registry: Arc<VarRegistry>,
    check_deadlock: bool,
    use_diffs: bool,
    cached_view_name: Option<String>,
    config: Config,
    eval_implied_actions: Arc<Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>>,
    eval_state_invariants: Arc<Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>>,
    uses_trace: bool,
    store_full_states: bool,
    continue_on_error: bool,
    first_violation: Arc<OnceLock<(String, Fingerprint)>>,
    first_action_property_violation: Arc<OnceLock<(String, Fingerprint)>>,
    /// Part of #3178: Shared parent log replaces DashMap.
    parent_log: Arc<crate::parallel::ParentLog>,
    successors_cache: Option<Arc<FxDashMap<Fingerprint, Vec<Fingerprint>>>>,
    /// Part of #3011: Concrete successor witness states for symmetry liveness.
    successor_witnesses_cache: Option<Arc<crate::parallel::SuccessorWitnessDashMap>>,
    /// Part of #3011: Symmetry permutations for canonical fingerprinting.
    mvperms: Arc<Vec<crate::value::MVPerm>>,
    local_work_delta: isize,
    consecutive_empty: usize,
    local_max_queue: usize,
    /// Whether `active_workers` was incremented for the current state.
    worker_active: bool,
    /// Part of #2749: Barrier for worker suspension during periodic work.
    barrier: Arc<WorkBarrier>,
    /// Part of #2749: Per-state depth tracking for checkpoint support.
    depths: Arc<FxDashMap<Fingerprint, usize>>,
    /// Part of #3233: Whether depth tracking is active (checkpoint or fp-only liveness).
    track_depths: bool,
    /// Part of #3213: Reusable scratch buffer for HandleState → ArrayState decode.
    /// Avoids per-dequeue allocation on the parallel BFS hot path.
    decode_scratch: Option<ArrayState>,
    current_uses_decode_scratch: bool,
    /// Part of #3232: Worker-local steal cursor for rotated victim selection.
    /// Seeded from `worker_id` to stagger initial victim probes across workers.
    steal_cursor: usize,
    /// Part of #3265: When true, injector routing is disabled to preserve
    /// depth-limit parity between sequential and parallel modes.
    depth_limited: bool,
    /// Part of #3397: Cached `TLA2_FORCE_BATCH=1` env var. Read once at
    /// construction instead of per-state on the BFS hot path.
    force_batch: bool,
    /// Part of #3392: Per-worker TIR caches. Persist across work items within
    /// this worker thread, avoiding redundant TIR lowering per state.
    tir_caches: tla_eval::tir::TirProgramCaches,
    /// Critical RSS threshold in bytes for per-worker inline memory checks.
    critical_rss_bytes: Option<usize>,
    /// Counter for inline RSS check frequency (every 10,000 states).
    states_since_rss_check: u32,
    /// Part of #3621: Compiled bytecode for invariant fast path, shared across workers.
    bytecode: Option<Arc<tla_eval::bytecode_vm::CompiledBytecode>>,
    /// Part of #3700: Shared JIT cache for invariant hot-path dispatch.
    jit_cache: Option<crate::parallel::SharedJitInvariantCache>,
    /// Part of #3700: Reusable scalar-state scratch for JIT checks in this worker.
    jit_state_scratch: RefCell<Vec<i64>>,
    /// Part of #3910: Per-worker scratch buffer for JIT next-state flattening.
    /// Separate from `jit_state_scratch` (used for invariant checking) because
    /// successor generation and invariant checking can overlap: JIT next-state
    /// produces successors that then go through the invariant pipeline.
    jit_next_state_scratch: RefCell<Vec<i64>>,
    /// Pre-computed ACTION_CONSTRAINT variable dependency analysis.
    action_constraint_analysis: Option<Arc<crate::checker_ops::ActionConstraintAnalysis>>,
    /// Part of #3910: Shared tiered JIT state for parallel promotion tracking.
    tier_state: Option<Arc<crate::parallel::tier_state::SharedTierState>>,
    /// Part of #4053: Skip materialization when spec has no lazy-producing AST nodes.
    spec_may_produce_lazy: bool,
}

impl<T: BfsWorkItem> ParallelTransport<T> {
    /// Create a new parallel transport from worker-thread parameters.
    ///
    /// The `ctx` must be already initialized (via `init_worker_ctx`).
    /// Caller is responsible for `set_eval_worker_count` and `WorkerPanicGuard`.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::parallel) fn new(
        worker_id: usize,
        local_queue: Worker<(T, usize)>,
        injector: Arc<Injector<(T, usize)>>,
        stealers: Arc<Vec<Stealer<(T, usize)>>>,
        shared_frontier: Arc<SharedFrontier<T>>,
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
            active_workers,
            bootstrap_injector_budget,
            shared_frontier_tail_mode,
            max_queue,
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
            num_workers,
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
            max_depth_limit,
            input_base_dir: _,
            critical_rss_bytes,
            bytecode,
            jit_cache,
            action_constraint_analysis: _,
            spec_may_produce_lazy,
        } = model;
        let depth_limited = max_depth_limit.is_some();
        let decode_scratch =
            T::requires_decode_scratch().then(|| ArrayState::new(var_registry.len()));
        Self {
            worker_id,
            num_workers,
            local_queue,
            injector,
            stealers,
            shared_frontier,
            shared_frontier_tail_mode,
            shared_frontier_tail_published: false,
            frontier_batch_active: false,
            dequeue_batch: SmallVec::new(),
            ctx,
            stats: WorkerStats {
                worker_id: Some(worker_id),
                ..WorkerStats::default()
            },
            stop_flag,
            work_remaining,
            active_workers,
            bootstrap_injector_budget,
            depth_limit_reached,
            max_queue,
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
            consecutive_empty: 0,
            local_max_queue: 0,
            worker_active: false,
            barrier,
            depths,
            track_depths,
            decode_scratch,
            current_uses_decode_scratch: false,
            steal_cursor: (worker_id + 1) % num_workers.max(1),
            depth_limited,
            force_batch: {
                static FORCE_BATCH: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
                *FORCE_BATCH.get_or_init(|| std::env::var("TLA2_FORCE_BATCH").is_ok_and(|v| v == "1"))
            },
            tir_caches: tla_eval::tir::TirProgramCaches::new(),
            critical_rss_bytes,
            states_since_rss_check: 0,
            bytecode,
            jit_cache,
            jit_state_scratch: RefCell::new(Vec::new()),
            jit_next_state_scratch: RefCell::new(Vec::new()),
            action_constraint_analysis: model.action_constraint_analysis.clone(),
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

    fn reclaim_decode_scratch(&mut self, current: ArrayState) {
        if self.current_uses_decode_scratch {
            debug_assert!(self.decode_scratch.is_none());
            let replaced = self.decode_scratch.replace(current);
            debug_assert!(replaced.is_none());
            self.current_uses_decode_scratch = false;
        }
    }

    #[inline]
    fn mark_worker_idle(&mut self) {
        if self.worker_active {
            self.active_workers.fetch_sub(1, Ordering::AcqRel);
            self.stats.active_worker_deactivations += 1;
            self.worker_active = false;
        }
    }

    #[inline]
    fn mark_worker_active(&mut self) {
        if !self.worker_active {
            self.active_workers.fetch_add(1, Ordering::AcqRel);
            self.stats.active_worker_activations += 1;
            self.worker_active = true;
        }
    }

    #[inline]
    fn shared_frontier_tail_mode_active(&self) -> bool {
        !self.depth_limited && self.shared_frontier_tail_mode.load(Ordering::Acquire)
    }

    #[inline]
    fn promote_shared_frontier_tail(&self) {
        if self.depth_limited || self.num_workers <= 1 {
            return;
        }
        self.shared_frontier_tail_mode
            .store(true, Ordering::Release);
    }

    fn ensure_shared_frontier_tail_published(&mut self) {
        if self.shared_frontier_tail_published {
            return;
        }
        flush_local_work_delta_profiled(
            &mut self.local_work_delta,
            &self.work_remaining,
            &mut self.stats,
        );
        self.mark_worker_idle();

        let mut frontier_batch: SmallVec<[(T, usize); SHARED_QUEUE_BATCH_SIZE]> = SmallVec::new();
        while let Some(item) = self.local_queue.pop() {
            frontier_batch.push(item);
            if frontier_batch.len() >= SHARED_QUEUE_BATCH_SIZE {
                self.shared_frontier.push_batch(&mut frontier_batch);
            }
        }

        loop {
            match self.injector.steal() {
                crossbeam_deque::Steal::Success(item) => {
                    frontier_batch.push(item);
                    if frontier_batch.len() >= SHARED_QUEUE_BATCH_SIZE {
                        self.shared_frontier.push_batch(&mut frontier_batch);
                    }
                }
                crossbeam_deque::Steal::Retry => continue,
                crossbeam_deque::Steal::Empty => break,
            }
        }

        self.shared_frontier.push_batch(&mut frontier_batch);
        self.shared_frontier_tail_published = true;
    }

    fn try_dequeue_shared_frontier_tail(&mut self) -> Option<(T, usize)> {
        self.ensure_shared_frontier_tail_published();

        if let Some(item) = self.dequeue_batch.pop() {
            self.consecutive_empty = 0;
            if self.stop_flag.load(Ordering::Relaxed) {
                flush_local_work_delta_profiled(
                    &mut self.local_work_delta,
                    &self.work_remaining,
                    &mut self.stats,
                );
                send_done_result(&self.ctx, &mut self.stats, &self.result_tx);
                return None;
            }
            if self.barrier.is_pause_requested() {
                flush_local_work_delta_profiled(
                    &mut self.local_work_delta,
                    &self.work_remaining,
                    &mut self.stats,
                );
                self.barrier.worker_check();
            }
            return Some(item);
        }

        flush_local_work_delta_profiled(
            &mut self.local_work_delta,
            &self.work_remaining,
            &mut self.stats,
        );
        if self.frontier_batch_active {
            self.shared_frontier.complete_level_batch();
            self.frontier_batch_active = false;
        }

        loop {
            if finish_if_stop_requested(
                &self.stop_flag,
                &self.ctx,
                &mut self.stats,
                &self.result_tx,
                &mut self.local_work_delta,
                &self.work_remaining,
            ) {
                return None;
            }
            if self.barrier.is_pause_requested() {
                flush_local_work_delta_profiled(
                    &mut self.local_work_delta,
                    &self.work_remaining,
                    &mut self.stats,
                );
                self.barrier.worker_check();
            }
            match self.shared_frontier.dequeue_batch_blocking(
                &mut self.dequeue_batch,
                SHARED_QUEUE_BATCH_SIZE,
                &self.stop_flag,
            ) {
                shared_queue::DequeueOutcome::Refilled => {
                    self.dequeue_batch.reverse();
                    self.frontier_batch_active = true;
                    self.consecutive_empty = 0;
                    return self.dequeue_batch.pop();
                }
                shared_queue::DequeueOutcome::Done => {
                    send_done_result(&self.ctx, &mut self.stats, &self.result_tx);
                    return None;
                }
                shared_queue::DequeueOutcome::TimedOut => {
                    self.stats.empty_polls += 1;
                }
            }
        }
    }
}
