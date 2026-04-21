// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parallel Model Checker - Multi-threaded BFS state exploration
//!
//! This module implements parallel state space exploration using:
//! - CAS-backed `ShardedCas` fingerprint deduplication on the default hot path
//! - Work-stealing deques for load balancing
//! - Per-run worker threads spawned for each checker invocation
//!
//! Auxiliary concurrent maps still use `DashMap` where appropriate, but the
//! default checker storage path is no longer a `DashMap`-centric design.
//!
//! # Algorithm
//!
//! The parallel checker uses a work-stealing approach:
//! 1. Main thread generates initial states and distributes them
//! 2. Worker threads explore states using local deques
//! 3. Workers steal from each other when their local queue is empty
//! 4. First worker to find a violation signals all others to stop
//! 5. Results are aggregated at the end
//!
//! The parallel implementation combines contention-aware deduplication, work
//! stealing, and early termination.

use crate::config::Config;
use crate::periodic_liveness::PeriodicLivenessState;
use crate::spec_formula::FairnessConstraint;
use crate::state::{ArrayState, Fingerprint};
use crate::storage::FingerprintSet;
use crate::var_index::VarRegistry;
use rustc_hash::{FxHashMap, FxHashSet};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicUsize};
use std::sync::{Arc, OnceLock};
use std::time::Duration;
use tla_core::ast::{Expr, Module, OperatorDef};
use tla_core::span::Spanned;
use tla_core::FileId;

#[cfg(feature = "jit")]
pub(crate) type SharedJitInvariantCache = Arc<tla_jit::bytecode_lower::JitInvariantCache>;
#[cfg(not(feature = "jit"))]
pub(crate) type SharedJitInvariantCache = ();

#[cfg(feature = "jit")]
pub(crate) type SharedJitNextStateCache = Arc<tla_jit::bytecode_lower::JitNextStateCache>;

#[cfg(feature = "jit")]
pub(crate) mod tier_state;

mod collision_debug;
use collision_debug::ParallelCollisionDiagnostics;

mod shared;

// Re-export shared infrastructure for child modules (checker.rs, worker/, tests).
// `pub(crate)` matches shared.rs item visibility and suppresses unused-import
// warnings for items consumed only by children via `super::`.
pub(crate) use shared::{
    accum_ns, check_and_warn_capacity, check_invariants_array_state, check_state_constraints_array,
    emit_parallel_profile_worker_stats, parallel_preserve_value_fps, parallel_profiling,
    timing_enabled, timing_start, trace_value_for_fp, use_handle_state, use_shared_queue,
    FxBuildHasher, FxDashMap, ParentLog, SuccessorWitnessDashMap, WorkerResult, WorkerStats,
    CAPACITY_NORMAL, WORK_BATCH_SIZE,
};
#[cfg(test)]
pub(crate) use shared::{
    capacity_status_to_u8, parallel_profiling_from_env, CAPACITY_CRITICAL, CAPACITY_WARNING,
    PARALLEL_PROFILING_ENV,
};
#[cfg(any(test, feature = "testing"))]
pub use shared::{set_use_handle_state_override, UseHandleStateGuard};

#[cfg(debug_assertions)]
use crate::check::debug::tla2_debug;

/// Parallel model checker using work-stealing
pub struct ParallelChecker {
    /// Number of worker threads
    num_workers: usize,
    /// Global seen set - concurrent hash map (used when `store_full_states` is true)
    /// Uses FxHasher for faster hashing since Fingerprint is already a 64-bit hash.
    /// Stores ArrayState (compact Box<[Value]>) instead of State (OrdMap) for memory efficiency.
    seen: Arc<FxDashMap<Fingerprint, ArrayState>>,
    /// Seen fingerprints (used when `store_full_states` is false)
    /// Uses FingerprintSet trait which supports both DashSet and MmapFingerprintSet.
    seen_fps: Arc<dyn FingerprintSet>,
    /// Part of #3178: Append-only parent log for trace reconstruction.
    /// Replaces the previous `FxDashMap` to eliminate per-state contention.
    parent_log: Arc<ParentLog>,
    /// Variable registry for ArrayState <-> State conversion
    var_registry: Arc<VarRegistry>,
    /// Whether to store full states for trace reconstruction
    store_full_states: bool,
    /// Flag to signal early termination
    stop_flag: Arc<AtomicBool>,
    /// Part of #2216: Flag indicating at least one worker encountered the depth limit.
    /// Unlike stop_flag, this does NOT terminate workers — they continue processing
    /// remaining states at shallower depths, matching serial BFS semantics.
    depth_limit_reached: Arc<AtomicBool>,
    /// Number of states remaining to explore (for termination detection)
    ///
    /// This counts the number of queued + in-progress states. It is incremented
    /// when a new state is discovered and enqueued, and decremented when a
    /// worker finishes processing a state.
    work_remaining: Arc<AtomicUsize>,
    /// Number of workers currently processing a state (for termination detection)
    ///
    /// Workers increment this when taking work and decrement when done.
    /// Termination requires both work_remaining == 0 AND active_workers == 0.
    active_workers: Arc<AtomicUsize>,
    /// Maximum queue depth seen
    max_queue_depth: Arc<AtomicUsize>,
    /// Maximum BFS depth seen
    max_depth: Arc<AtomicUsize>,
    /// Total transitions counter (atomic for thread safety)
    total_transitions: Arc<AtomicUsize>,
    /// Variable names
    vars: Vec<Arc<str>>,
    /// Operator definitions
    op_defs: FxHashMap<String, OperatorDef>,
    /// Configuration
    config: Config,
    /// Setup/configuration error detected during construction.
    setup_error: Option<crate::check::CheckError>,
    /// Whether to check for deadlocks
    check_deadlock: bool,
    /// Module for worker thread cloning
    module: Arc<Module>,
    /// Extended modules for worker thread cloning
    extended_modules: Arc<Vec<Module>>,
    /// Names of modules that contribute to the unqualified operator namespace.
    ///
    /// This mirrors the sequential checker's semantics:
    /// - `EXTENDS M` imports M unqualified (transitively).
    /// - standalone `INSTANCE M` imports M unqualified (transitively).
    /// - named instances (`I == INSTANCE M WITH ...`) do NOT import M unqualified; they must be
    ///   accessed via `I!Op` and are loaded via `load_instance_module`.
    ///
    /// Loading named-instance modules unqualified can cause operator name collisions (e.g.,
    /// `ClientCentric.TypeOK` shadowing `KVsnap.TypeOK`) and lead to false invariant violations.
    unqualified_modules: Arc<FxHashSet<String>>,
    /// Maximum states to explore (None = unlimited)
    max_states_limit: Option<usize>,
    /// Maximum BFS depth (None = unlimited)
    max_depth_limit: Option<usize>,
    /// Progress callback (called periodically during checking)
    progress_callback: Option<Arc<crate::check::ProgressCallback>>,
    /// How often to report progress (in milliseconds)
    progress_interval_ms: u64,
    /// Continue exploring after finding an invariant violation (TLC -continue mode).
    /// When true, exploration continues until full state space is exhausted,
    /// then reports the first violation found with final stats.
    continue_on_error: bool,
    /// First violation found (used in continue_on_error mode).
    /// Stores (invariant_name, violating_state_fingerprint).
    first_violation: Arc<OnceLock<(String, Fingerprint)>>,
    /// First action-level PROPERTY violation found in continue-on-error mode.
    first_action_property_violation: Arc<OnceLock<(String, Fingerprint)>>,
    /// Cached states for the first continue-on-error trace.
    ///
    /// Populated during finalization when the checker already reconstructs the
    /// user-facing trace. Checkpoint creation reuses this cache so it does not
    /// re-run trace reconstruction after the check has finished.
    first_violation_trace: Arc<OnceLock<Vec<crate::state::State>>>,
    /// ASSUME statements collected from all modules (main + extended).
    /// Each entry is (module_name, assume_expr) to match TLC's error format.
    assumes: Vec<(String, Spanned<Expr>)>,
    /// Part of #1139: Whether any invariant references TLCExt!Trace.
    /// When true, trace context must be set before invariant evaluation.
    uses_trace: bool,
    /// Part of #1906/#2309: Snapshot of `states_count()` at the moment the first
    /// stop event fires. Uses `OnceLock` so that `Some(0)` (valid zero-count
    /// snapshot) is distinguishable from `None` (no snapshot taken). First writer
    /// wins; subsequent `set()` calls are no-ops.
    states_at_stop: Arc<OnceLock<usize>>,
    /// Atomic counter for state-admission control.
    ///
    /// Tracks the number of admitted states precisely across all workers.
    /// Part of #2123: prevents multi-worker max_states overshoot by using
    /// CAS-based reservation instead of periodic seen-set length checks.
    admitted_states: Arc<AtomicUsize>,
    /// Optional fingerprint-collision diagnostics shared across all workers.
    collision_diagnostics: Option<Arc<ParallelCollisionDiagnostics>>,
    /// One-shot guard: prevents re-use of a checker instance after `check()`.
    ///
    /// `check()` does not reset run-state (seen maps, stop_flag, counters,
    /// first_violation OnceLock). A second call would observe stale state,
    /// causing incorrect results. This flag enforces one-shot semantics.
    /// Fix for #1851.
    has_run: AtomicBool,
    /// Base directory for IO builtins (ndJsonDeserialize, JsonDeserialize) path resolution.
    /// Set from the root spec file's parent directory, matching sequential checker behavior.
    input_base_dir: Option<std::path::PathBuf>,
    /// Part of #2740: Successor fingerprints per source state, populated during BFS.
    /// Used for post-BFS liveness checking. Only `Some` when `config.properties` is
    /// non-empty (liveness checking is needed).
    successors: Option<Arc<FxDashMap<Fingerprint, Vec<Fingerprint>>>>,
    /// Initial states cached for fp-only liveness replay.
    ///
    /// Part of #3210: fp-only liveness no longer retains every explored state in
    /// `seen`. The checker keeps only the admitted initial states here and
    /// reconstructs the remaining concrete states from the fingerprint graph on
    /// the cold post-BFS liveness path.
    liveness_init_states: Arc<FxDashMap<Fingerprint, ArrayState>>,
    /// Part of #3011: Concrete successor states for liveness witness evaluation under
    /// symmetry. Keyed by canonical source FP; each entry stores
    /// `(canonical_succ_fp, concrete_succ_ArrayState)` pairs.
    ///
    /// Only `Some` when both symmetry AND liveness properties are active. Without
    /// symmetry, the canonical representative in `seen` is identical to the concrete
    /// state, so witnesses are unnecessary. Matches the sequential checker's
    /// `liveness_cache.successor_states` field.
    successor_witnesses: Option<Arc<SuccessorWitnessDashMap>>,
    /// Part of #2740: Fairness constraints from the SPECIFICATION formula.
    /// Conjoined with the negated property during post-BFS liveness checking,
    /// matching the sequential checker's `liveness_cache.fairness` field.
    fairness: Vec<FairnessConstraint>,
    /// Part of #2762: Whether stuttering transitions are allowed.
    /// `[A]_v` form → true (default), `<<A>>_v` form → false.
    /// Must match the sequential checker's `exploration.stuttering_allowed`.
    stuttering_allowed: bool,
    /// Part of #2772: Whether to auto-create a temp trace file for fingerprint-only mode.
    ///
    /// When true (default): The sequential checker creates a temporary trace file
    /// for counterexample reconstruction if `store_full_states` is false.
    /// When false (--no-trace mode): No trace file is created.
    ///
    /// Note: The parallel checker does not currently support trace files, but this
    /// field is plumbed through to prevent silent config loss from AdaptiveChecker
    /// and to enable future trace file support.
    auto_create_trace_file: bool,
    /// Part of #2772: Best-effort FileId -> source path mapping for TLC-style
    /// line/col error locations.
    ///
    /// When absent for a given FileId (or unreadable), location rendering falls back
    /// to byte offsets (e.g. "bytes 0-0 of module M"). Registering the root module
    /// path also seeds `input_base_dir` so IO builtins stay spec-relative.
    file_id_to_path: FxHashMap<FileId, PathBuf>,
    /// Part of #2749: Barrier for suspending all workers during periodic work
    /// (checkpointing, liveness checking). Workers check this before each dequeue.
    barrier: Arc<WorkBarrier>,
    /// Part of #2749: Per-state depth tracking for parallel checkpoint support.
    /// Mirrors the sequential checker's `trace.depths` FxHashMap. Workers insert
    /// `(fp, depth)` when a new state is admitted, alongside the `parent_log` append.
    /// Used to extract fingerprints and depths during checkpoint creation.
    depths: Arc<FxDashMap<Fingerprint, usize>>,
    /// Part of #2749: Checkpoint save directory. `None` = checkpointing disabled.
    checkpoint_dir: Option<PathBuf>,
    /// Part of #2749: Checkpoint save interval. Default: 5 minutes.
    checkpoint_interval: Duration,
    /// Part of #2752: TLC-style periodic liveness gate state for the main-thread
    /// maintenance loop. Cloned into `finalize_check()` because the checker is
    /// one-shot and tests may lower the thresholds before running.
    periodic_liveness: PeriodicLivenessState,
    /// Part of #2749: Spec path for checkpoint identity validation on resume.
    checkpoint_spec_path: Option<String>,
    /// Part of #2749: Config path for checkpoint identity validation on resume.
    checkpoint_config_path: Option<String>,
    /// Part of #2676: State-level property names promoted to invariant checking.
    /// Populated once during `run_check_inner()` via `OnceLock::set()`. Used to
    /// route violations through `PropertyViolation` (StateLevel) instead of
    /// `InvariantViolation`. Empty (unset) on checkpoint resume path.
    promoted_property_invariants: OnceLock<Vec<String>>,
    /// Part of #2751 Phase 2+3: Optional memory policy for threshold-triggered
    /// checkpoint and graceful stop during BFS exploration.
    memory_policy: Option<crate::memory::MemoryPolicy>,
    /// Part of #3282: Optional disk usage limit in bytes for disk-backed storage.
    disk_limit_bytes: Option<usize>,
    /// Part of #3910: Shared tiered JIT state for parallel promotion tracking.
    /// Workers atomically increment per-action eval counters; the main
    /// coordination thread periodically checks for tier promotions.
    /// Populated once during `run_check_inner()` via `OnceLock::set()`.
    #[cfg(feature = "jit")]
    tier_state: OnceLock<Arc<tier_state::SharedTierState>>,
    /// Part of #4053: Whether the spec can produce lazy values at runtime.
    /// When `false`, materialization is skipped in worker successor processing.
    spec_may_produce_lazy: bool,
}

pub(crate) mod barrier;
pub(crate) use barrier::WorkBarrier;
mod checker;
pub(crate) mod checkpoint;
pub use checker::check_module_parallel;
mod worker;
use worker::{
    run_worker_shared_queue, run_worker_unified, BfsWorkItem, WorkerModelConfig,
    WorkerSharedState,
};
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_transition_constraints;
#[cfg(test)]
pub(crate) use worker::snapshot_states_at_stop_for_test;
