// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Worker thread functions for parallel model checking.
//!
//! Decomposed from the monolithic `worker.rs` into:
//! - `mod.rs`: Shared structs, constants, and re-exports
//! - `coordination.rs`: Work-stealing, backoff, and termination detection
//! - `core_adapter.rs`: Adapter bridging worker BFS loop to shared checker core
//! - `helpers.rs`: VIEW fingerprinting, worker context init, and re-exports
//! - `invariant_dispatch.rs`: Invariant checking dispatch for workers
//! - `run_unified.rs`: Generic BFS worker entry point (unified from former run_array + run_handle)
//! - `successors.rs`: State-based and diff-based successor processing pipelines
//! - `transport/`: Transport abstraction (local deque vs shared-queue modes)
//! - `work_item.rs`: `BfsWorkItem` trait abstracting ArrayState/HandleState
//! - `worker_bfs_ctx.rs`: Per-worker BFS context and state
//!
//! Part of #2016, #2492, #2356.

use super::{FxDashMap, ParentLog, WorkBarrier, WorkerResult};
use crate::config::Config;
use crate::state::{ArrayState, Fingerprint};
use crate::storage::FingerprintSet;
use crate::var_index::VarRegistry;
use crossbeam_channel::Sender;
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, OnceLock};
use tla_core::ast::{Module, OperatorDef};

/// Adaptive backoff thresholds for empty poll handling.
/// After this many consecutive empty polls, start sleeping instead of yielding.
pub(super) const BACKOFF_YIELD_THRESHOLD: usize = 3;
/// After this many consecutive empty polls, use longer sleep.
pub(super) const BACKOFF_LONG_THRESHOLD: usize = 10;

// ActiveWorkerGuard was removed in #2356 Phase 4 Step 4d — active worker
// tracking is now internal to ParallelTransport (worker_active field + Drop impl).

/// RAII guard that sets `stop_flag` if a worker panics with unflushed `local_work_delta`.
///
/// Without this, a worker panic can leave `work_remaining` permanently inflated (if
/// `local_work_delta < 0`) or deflated (if `local_work_delta > 0`). Either condition
/// corrupts termination detection:
/// - Inflated: surviving workers spin forever (deadlock via #1826)
/// - Deflated: surviving workers terminate prematurely, skipping unexplored states
///
/// Setting `stop_flag` on panic forces an orderly shutdown rather than silent
/// correctness loss. Part of #1824.
pub(super) struct WorkerPanicGuard<'a> {
    stop_flag: &'a AtomicBool,
}

impl<'a> WorkerPanicGuard<'a> {
    pub(super) fn new(stop_flag: &'a AtomicBool) -> Self {
        Self { stop_flag }
    }
}

impl Drop for WorkerPanicGuard<'_> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            self.stop_flag.store(true, Ordering::SeqCst);
        }
    }
}

/// Shared references for invariant checking, bundled to keep argument count manageable.
pub(super) struct InvariantCheckCtx<'a> {
    pub(super) config: &'a Config,
    /// Eval-based implied actions for ModuleRef/INSTANCE properties (#2983).
    pub(super) eval_implied_actions: &'a [(String, tla_core::Spanned<tla_core::ast::Expr>)],
    /// Eval-based state invariants for ENABLED-containing state-level terms (#3113).
    pub(super) eval_state_invariants: &'a [(String, tla_core::Spanned<tla_core::ast::Expr>)],
    pub(super) uses_trace: bool,
    pub(super) store_full_states: bool,
    pub(super) continue_on_error: bool,
    pub(super) first_violation: &'a OnceLock<(String, Fingerprint)>,
    pub(super) first_action_property_violation: &'a OnceLock<(String, Fingerprint)>,
    /// Part of #3178: Per-worker sharded parent log replaces DashMap.
    pub(super) parent_log: &'a ParentLog,
    /// Part of #3178: Worker ID for parent log shard indexing.
    pub(super) worker_id: usize,
    pub(super) seen: &'a FxDashMap<Fingerprint, ArrayState>,
    pub(super) var_registry: &'a VarRegistry,
    /// Part of #2749: Per-state depth tracking for checkpoint support.
    pub(super) depths: &'a FxDashMap<Fingerprint, usize>,
    /// Part of #3233: Whether depth tracking is active.
    /// True when checkpointing OR fp-only liveness replay needs `depths`.
    pub(super) track_depths: bool,
    /// Part of #3621: Compiled bytecode for invariant fast path.
    pub(super) bytecode: &'a Option<Arc<tla_eval::bytecode_vm::CompiledBytecode>>,
    /// Part of #3700: Shared JIT cache for invariant hot-path dispatch.
    #[cfg(feature = "jit")]
    pub(super) jit_cache: &'a Option<crate::parallel::SharedJitInvariantCache>,
    /// Part of #3700: Reusable scalar-state scratch for JIT hot-path checks.
    #[cfg(feature = "jit")]
    pub(super) jit_state_scratch: &'a std::cell::RefCell<Vec<i64>>,
    /// Part of #3700: JIT hits counter (interior mutability for immutable borrow).
    pub(super) jit_hits: std::cell::Cell<usize>,
    /// Part of #3700: JIT misses counter (interior mutability for immutable borrow).
    pub(super) jit_misses: std::cell::Cell<usize>,
    /// Part of #3935: JIT dispatch — compiled but returned FallbackNeeded at runtime.
    pub(super) jit_fallback: std::cell::Cell<usize>,
    /// Part of #3935: JIT dispatch — invariant not in JIT cache.
    pub(super) jit_not_compiled: std::cell::Cell<usize>,
    /// Number of fully JIT-covered invariant evaluations cross-checked via the interpreter.
    pub(super) jit_verify_checked: std::cell::Cell<usize>,
    /// Number of JIT/interpreter invariant mismatches observed during cross-checking.
    pub(super) jit_verify_mismatches: std::cell::Cell<usize>,
    /// Pre-computed ACTION_CONSTRAINT variable dependency analysis.
    /// When `Some`, enables skipping constraint evaluation for transitions where
    /// referenced variables are unchanged.
    pub(super) action_constraint_analysis: Option<&'a crate::checker_ops::ActionConstraintAnalysis>,
}

/// Shared concurrent state accessible by all worker threads.
///
/// Groups the Arc-wrapped atomics, channels, and concurrent maps that workers
/// use for coordination, deduplication, and result reporting.
pub(super) struct WorkerSharedState {
    pub(super) seen: Arc<FxDashMap<Fingerprint, ArrayState>>,
    pub(super) seen_fps: Arc<dyn FingerprintSet>,
    /// Part of #3178: Shared parent log replaces DashMap.
    pub(super) parent_log: Arc<ParentLog>,
    pub(super) stop_flag: Arc<AtomicBool>,
    /// Part of #2216: Shared depth-limit flag. Workers set this when encountering
    /// the depth limit but continue processing (no stop-the-world).
    pub(super) depth_limit_reached: Arc<AtomicBool>,
    pub(super) work_remaining: Arc<AtomicUsize>,
    pub(super) active_workers: Arc<AtomicUsize>,
    /// Part of #3234: shared startup-only injector handoff budget.
    pub(super) bootstrap_injector_budget: Arc<AtomicUsize>,
    /// Part of #3285: one-way promotion from work-stealing to shared-frontier tail mode.
    pub(super) shared_frontier_tail_mode: Arc<AtomicBool>,
    pub(super) max_queue: Arc<AtomicUsize>,
    pub(super) max_depth_atomic: Arc<AtomicUsize>,
    pub(super) total_transitions: Arc<AtomicUsize>,
    pub(super) result_tx: Sender<WorkerResult>,
    pub(super) first_violation: Arc<OnceLock<(String, Fingerprint)>>,
    pub(super) first_action_property_violation: Arc<OnceLock<(String, Fingerprint)>>,
    /// Part of #1906/#2309: Snapshot of states_count at the first stop event.
    /// OnceLock ensures `Some(0)` is distinguishable from "no snapshot".
    pub(super) states_at_stop: Arc<OnceLock<usize>>,
    /// Part of #2123: Atomic admission counter for deterministic max_states.
    pub(super) admitted_states: Arc<AtomicUsize>,
    /// Part of #2841: optional collision diagnostics shared across workers.
    pub(super) collision_diagnostics: Option<Arc<super::ParallelCollisionDiagnostics>>,
    /// Part of #2740: Successor fingerprints per source state, for post-BFS liveness.
    /// `None` when liveness properties are not configured (no overhead).
    pub(super) successors: Option<Arc<super::FxDashMap<Fingerprint, Vec<Fingerprint>>>>,
    /// Part of #3011: Concrete successor states for symmetry witness evaluation.
    pub(super) successor_witnesses: Option<Arc<super::SuccessorWitnessDashMap>>,
    /// Part of #2749: Barrier for worker suspension during periodic work.
    pub(super) barrier: Arc<WorkBarrier>,
    /// Part of #2749: Per-state depth tracking for checkpoint support.
    pub(super) depths: Arc<super::FxDashMap<Fingerprint, usize>>,
    /// Part of #3910: Shared tiered JIT state for parallel promotion tracking.
    #[cfg(feature = "jit")]
    pub(super) tier_state: Option<Arc<crate::parallel::tier_state::SharedTierState>>,
}

/// Per-worker model checking configuration.
///
/// Bundles the TLA+ module, operator definitions, spec config, and
/// checking parameters that each worker thread needs. Cloned per-thread.
pub(super) struct WorkerModelConfig {
    pub(super) module: Arc<Module>,
    pub(super) extended_modules: Arc<Vec<Module>>,
    pub(super) unqualified_modules: Arc<FxHashSet<String>>,
    pub(super) vars: Vec<Arc<str>>,
    pub(super) op_defs: FxHashMap<String, OperatorDef>,
    pub(super) por_actions: Arc<Vec<crate::coverage::DetectedAction>>,
    pub(super) por_independence: Option<Arc<crate::por::IndependenceMatrix>>,
    pub(super) por_visibility: Arc<crate::por::VisibilitySet>,
    pub(super) config: Config,
    pub(super) check_deadlock: bool,
    pub(super) next_name: String,
    pub(super) parallel_tir_next_selection: Option<crate::tir_mode::ParallelNextTirEvalSelection>,
    pub(super) num_workers: usize,
    pub(super) max_states_limit: Option<usize>,
    pub(super) max_depth_limit: Option<usize>,
    pub(super) store_full_states: bool,
    /// Part of #1139: Whether invariants use TLCExt!Trace (requires trace reconstruction)
    pub(super) uses_trace: bool,
    pub(super) var_registry: Arc<VarRegistry>,
    /// Part of #2983: Eval-based implied actions for ModuleRef/INSTANCE properties.
    pub(super) eval_implied_actions: Arc<Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>>,
    /// Part of #3113: Eval-based state invariants for ENABLED-containing state-level terms.
    pub(super) eval_state_invariants: Arc<Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>>,
    /// Part of #582: Continue-on-error mode (TLC -continue semantics)
    pub(super) continue_on_error: bool,
    /// Part of #1066: VIEW operator name for state abstraction fingerprinting.
    pub(super) cached_view_name: Option<String>,
    /// Part of #1102: Base directory for IO builtins path resolution.
    pub(super) input_base_dir: Option<std::path::PathBuf>,
    /// Part of #3011: Symmetry permutations for canonical fingerprinting.
    /// Empty when no SYMMETRY is configured.
    pub(super) mvperms: Arc<Vec<crate::value::MVPerm>>,
    /// Part of #3233: Whether depth tracking is active (checkpoint or fp-only liveness).
    pub(super) track_depths: bool,
    /// Critical RSS threshold in bytes for per-worker inline memory checks.
    /// When set, workers check RSS every 10,000 states and set the stop flag
    /// if this threshold is exceeded, without waiting for the coordinator's
    /// periodic maintenance barrier.
    pub(super) critical_rss_bytes: Option<usize>,
    /// Part of #3621: Compiled bytecode for invariant fast path, shared across workers.
    pub(super) bytecode: Option<Arc<tla_eval::bytecode_vm::CompiledBytecode>>,
    /// Part of #3700: Shared JIT cache for invariant hot-path dispatch.
    /// When `jit` feature is off, `SharedJitInvariantCache = ()` (ZST), so this
    /// field has zero overhead. It remains present to avoid cascading cfg-gates
    /// through the entire preparation pipeline.
    #[cfg_attr(not(feature = "jit"), allow(dead_code))]
    pub(super) jit_cache: Option<crate::parallel::SharedJitInvariantCache>,
    /// Pre-computed ACTION_CONSTRAINT variable dependency analysis.
    pub(super) action_constraint_analysis:
        Option<Arc<crate::checker_ops::ActionConstraintAnalysis>>,
    /// Part of #4053: Skip materialization when spec has no lazy-producing AST nodes.
    pub(super) spec_may_produce_lazy: bool,
}

/// Shared stop-protocol state passed to terminal-event handlers.
///
/// Bundles the atomics, shared maps, and config needed to execute the
/// stop -> snapshot -> finalize -> send sequence (Part of #1911).
pub(super) struct StopCtx<'a> {
    pub(super) stop_flag: &'a AtomicBool,
    pub(super) states_at_stop: &'a OnceLock<usize>,
    pub(super) seen: &'a FxDashMap<Fingerprint, ArrayState>,
    pub(super) seen_fps: &'a dyn FingerprintSet,
    pub(super) store_full_states: bool,
    /// Part of #3175/#3210: whether fingerprint-only liveness graph data is active.
    ///
    /// When true and `store_full_states` is false, workers still maintain the
    /// fingerprint graph (`successors`, `parents`, `depths`) needed for post-BFS
    /// liveness replay, but they no longer clone every explored state into `seen`.
    pub(super) cache_for_liveness: bool,
    /// Part of #2123: admission counter for max_states.
    pub(super) admitted_states: &'a AtomicUsize,
    /// Part of #2123: max_states limit.
    pub(super) max_states_limit: Option<usize>,
    /// Part of #2841: optional collision diagnostics shared across workers.
    pub(super) collision_diagnostics: Option<&'a super::ParallelCollisionDiagnostics>,
}

mod coordination;
#[cfg(test)]
mod coordination_tests;
mod core_adapter;
mod helpers;
mod invariant_dispatch;
mod observer;
mod run_unified;
mod successors;
mod successors_full_state;
mod transport;
mod work_item;
#[cfg(test)]
mod work_item_tests;
mod work_stealing;
mod worker_bfs_ctx;
mod worker_value_lane;

pub(in crate::parallel) use transport::initial_bootstrap_injector_budget;
// send_result accessed by parallel/tests.rs via `worker::send_result`
#[cfg(test)]
pub(super) use coordination::send_result;
pub(super) use run_unified::run_worker_shared_queue; // Part of #3258
pub(super) use run_unified::run_worker_unified;
pub(super) use transport::shared_queue::SharedFrontier; // Part of #3258
pub(super) use work_item::{ArrayStateMode, BfsWorkItem, HandleStateMode};

/// Test-only exposure of `snapshot_states_at_stop` for unit tests in finalize_tests.
/// Part of #2309: allows testing first-writer-wins semantics with zero-count snapshots.
#[cfg(test)]
pub(crate) fn snapshot_states_at_stop_for_test(
    states_at_stop: &OnceLock<usize>,
    seen: &super::FxDashMap<Fingerprint, ArrayState>,
    seen_fps: &dyn FingerprintSet,
    store_full_states: bool,
) {
    coordination::snapshot_states_at_stop(states_at_stop, seen, seen_fps, store_full_states);
}
