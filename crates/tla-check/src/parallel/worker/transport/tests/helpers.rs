// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared test fixtures for parallel transport tests.

use super::super::shared_queue::SharedFrontier;
use super::super::ParallelTransport;
use crate::config::Config;
use crate::eval::EvalCtx;
use crate::intern::{HandleState, HandleStateInternerBank};
use crate::parallel::worker::{
    ArrayStateMode, HandleStateMode, WorkerModelConfig, WorkerSharedState,
};
use crate::parallel::{FxDashMap, WorkBarrier, WorkerResult, WorkerStats};
use crate::state::{ArrayState, Fingerprint};
use crate::storage::FingerprintSet;
use crate::var_index::VarRegistry;
use crossbeam_channel::unbounded;
use crossbeam_deque::{Injector, Worker};
use dashmap::DashSet;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use std::ffi::OsString;
use std::sync::atomic::{AtomicBool, AtomicUsize};
use std::sync::{Arc, Mutex, MutexGuard, OnceLock};
use tla_core::ast::Module;
use tla_core::span::{Span, Spanned};

static FORCE_BATCH_ENV_LOCK: Mutex<()> = Mutex::new(());

pub(super) struct ForceBatchEnvGuard {
    previous: Option<OsString>,
    lock: Option<MutexGuard<'static, ()>>,
}

impl ForceBatchEnvGuard {
    pub(super) fn set(value: Option<&str>) -> Self {
        let lock = FORCE_BATCH_ENV_LOCK
            .lock()
            .expect("force-batch env lock must not be poisoned");
        let previous = std::env::var_os("TLA2_FORCE_BATCH");
        match value {
            Some(value) => std::env::set_var("TLA2_FORCE_BATCH", value),
            None => std::env::remove_var("TLA2_FORCE_BATCH"),
        }
        Self {
            previous,
            lock: Some(lock),
        }
    }
}

impl Drop for ForceBatchEnvGuard {
    fn drop(&mut self) {
        match self.previous.take() {
            Some(value) => std::env::set_var("TLA2_FORCE_BATCH", value),
            None => std::env::remove_var("TLA2_FORCE_BATCH"),
        }
        self.lock.take();
    }
}

pub(super) fn build_handle_transport(
    registry: Arc<VarRegistry>,
    bank: Arc<HandleStateInternerBank>,
) -> ParallelTransport<HandleState> {
    let (result_tx, _result_rx) = unbounded::<WorkerResult>();
    let seen_fps: Arc<dyn FingerprintSet> = Arc::new(DashSet::<Fingerprint>::new());

    ParallelTransport {
        worker_id: 0,
        num_workers: 1,
        local_queue: Worker::new_fifo(),
        injector: Arc::new(Injector::new()),
        stealers: Arc::new(Vec::new()),
        shared_frontier: Arc::new(SharedFrontier::new(1)),
        shared_frontier_tail_mode: Arc::new(AtomicBool::new(false)),
        shared_frontier_tail_published: false,
        frontier_batch_active: false,
        dequeue_batch: SmallVec::new(),
        ctx: EvalCtx::new(),
        seen: Arc::new(FxDashMap::default()),
        seen_fps,
        stop_flag: Arc::new(AtomicBool::new(false)),
        depth_limit_reached: Arc::new(AtomicBool::new(false)),
        work_remaining: Arc::new(AtomicUsize::new(0)),
        active_workers: Arc::new(AtomicUsize::new(0)),
        bootstrap_injector_budget: Arc::new(AtomicUsize::new(0)),
        max_queue: Arc::new(AtomicUsize::new(0)),
        max_depth_atomic: Arc::new(AtomicUsize::new(0)),
        total_transitions: Arc::new(AtomicUsize::new(0)),
        stats: WorkerStats::default(),
        admitted_states: Arc::new(AtomicUsize::new(0)),
        states_at_stop: Arc::new(OnceLock::new()),
        collision_diagnostics: None,
        max_states_limit: None,
        result_tx,
        vars: Vec::new(),
        op_defs: FxHashMap::default(),
        por_actions: Arc::new(Vec::new()),
        por_independence: None,
        por_visibility: Arc::new(crate::por::VisibilitySet::new()),
        module: Arc::new(Module {
            name: Spanned::dummy("TestModule".to_string()),
            extends: Vec::new(),
            units: Vec::new(),
            action_subscript_spans: std::collections::HashSet::new(),
            span: Span::dummy(),
        }),
        extended_modules: Arc::new(Vec::new()),
        next_name: String::new(),
        parallel_tir_next_selection: None,
        mode: HandleStateMode {
            interner_bank: bank,
        },
        var_registry: Arc::clone(&registry),
        check_deadlock: false,
        use_diffs: false,
        cached_view_name: None,
        config: Config::default(),
        eval_implied_actions: Arc::new(Vec::new()),
        eval_state_invariants: Arc::new(Vec::new()),
        uses_trace: false,
        store_full_states: false,
        continue_on_error: false,
        first_violation: Arc::new(OnceLock::new()),
        first_action_property_violation: Arc::new(OnceLock::new()),
        parent_log: Arc::new(crate::parallel::ParentLog::new(1)),
        successors_cache: None,
        successor_witnesses_cache: None,
        mvperms: Arc::new(Vec::new()),
        local_work_delta: 0,
        consecutive_empty: 0,
        local_max_queue: 0,
        worker_active: false,
        barrier: Arc::new(WorkBarrier::new(1)),
        depths: Arc::new(FxDashMap::default()),
        track_depths: false,
        decode_scratch: Some(ArrayState::new(registry.len())),
        current_uses_decode_scratch: false,
        steal_cursor: 1,
        depth_limited: false,
        force_batch: false,
        tir_caches: tla_eval::tir::TirProgramCaches::new(),
        critical_rss_bytes: None,
        states_since_rss_check: 0,
        bytecode: None,
        jit_cache: None,
        jit_state_scratch: std::cell::RefCell::new(Vec::new()),
        jit_next_state_scratch: std::cell::RefCell::new(Vec::new()),
        action_constraint_analysis: None,
        tier_state: None,
        spec_may_produce_lazy: false,
    }
}

fn build_shared_state(
    result_tx: crossbeam_channel::Sender<WorkerResult>,
    seen_fps: Arc<dyn FingerprintSet>,
    worker_count: usize,
) -> WorkerSharedState {
    WorkerSharedState {
        seen: Arc::new(FxDashMap::default()),
        seen_fps,
        parent_log: Arc::new(crate::parallel::ParentLog::new(1)),
        stop_flag: Arc::new(AtomicBool::new(false)),
        depth_limit_reached: Arc::new(AtomicBool::new(false)),
        work_remaining: Arc::new(AtomicUsize::new(0)),
        active_workers: Arc::new(AtomicUsize::new(0)),
        bootstrap_injector_budget: Arc::new(AtomicUsize::new(0)),
        shared_frontier_tail_mode: Arc::new(AtomicBool::new(false)),
        max_queue: Arc::new(AtomicUsize::new(0)),
        max_depth_atomic: Arc::new(AtomicUsize::new(0)),
        total_transitions: Arc::new(AtomicUsize::new(0)),
        result_tx,
        first_violation: Arc::new(OnceLock::new()),
        first_action_property_violation: Arc::new(OnceLock::new()),
        states_at_stop: Arc::new(OnceLock::new()),
        admitted_states: Arc::new(AtomicUsize::new(0)),
        collision_diagnostics: None,
        successors: None,
        successor_witnesses: None,
        barrier: Arc::new(WorkBarrier::new(worker_count.max(1))),
        depths: Arc::new(FxDashMap::default()),
        tier_state: None,
    }
}

fn build_model_config(registry: Arc<VarRegistry>, worker_count: usize) -> WorkerModelConfig {
    WorkerModelConfig {
        module: Arc::new(Module {
            name: Spanned::dummy("TestModule".to_string()),
            extends: Vec::new(),
            units: Vec::new(),
            action_subscript_spans: std::collections::HashSet::new(),
            span: Span::dummy(),
        }),
        extended_modules: Arc::new(Vec::new()),
        unqualified_modules: Arc::new(FxHashSet::default()),
        vars: Vec::new(),
        op_defs: FxHashMap::default(),
        por_actions: Arc::new(Vec::new()),
        por_independence: None,
        por_visibility: Arc::new(crate::por::VisibilitySet::new()),
        config: Config::default(),
        check_deadlock: false,
        next_name: String::new(),
        parallel_tir_next_selection: None,
        num_workers: worker_count,
        max_states_limit: None,
        max_depth_limit: None,
        store_full_states: false,
        uses_trace: false,
        var_registry: registry,
        eval_implied_actions: Arc::new(Vec::new()),
        eval_state_invariants: Arc::new(Vec::new()),
        continue_on_error: false,
        cached_view_name: None,
        input_base_dir: None,
        mvperms: Arc::new(Vec::new()),
        track_depths: false,
        critical_rss_bytes: None,
        bytecode: None,
        jit_cache: None,
        action_constraint_analysis: None,
        spec_may_produce_lazy: false,
    }
}

pub(super) fn build_array_transport_via_new(
    worker_id: usize,
    worker_count: usize,
    registry: Arc<VarRegistry>,
) -> ParallelTransport<ArrayState> {
    build_array_transport_with_result_rx(worker_id, worker_count, registry).0
}

pub(super) fn build_array_transport_with_result_rx(
    worker_id: usize,
    worker_count: usize,
    registry: Arc<VarRegistry>,
) -> (
    ParallelTransport<ArrayState>,
    crossbeam_channel::Receiver<WorkerResult>,
) {
    let (result_tx, result_rx) = unbounded::<WorkerResult>();
    let seen_fps: Arc<dyn FingerprintSet> = Arc::new(DashSet::<Fingerprint>::new());
    let workers: Vec<_> = (0..worker_count.max(1))
        .map(|_| Worker::new_fifo())
        .collect();
    let stealers = Arc::new(workers.iter().map(Worker::stealer).collect());
    let shared_frontier = Arc::new(SharedFrontier::new(worker_count.max(1)));
    let local_queue = workers
        .into_iter()
        .nth(worker_id)
        .expect("worker_id must identify one of the constructed local queues");

    (
        ParallelTransport::new(
            worker_id,
            local_queue,
            Arc::new(Injector::new()),
            stealers,
            shared_frontier,
            EvalCtx::new(),
            build_shared_state(result_tx, seen_fps, worker_count),
            build_model_config(Arc::clone(&registry), worker_count),
            ArrayStateMode,
        ),
        result_rx,
    )
}
