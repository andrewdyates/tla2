// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared runtime infrastructure for the parallel checker.
//!
//! Contains type aliases, helper contracts, profiling utilities, and
//! worker result/stats types used by both `parallel/checker/` and
//! `parallel/worker/`. Extracted from `parallel/mod.rs` as part of #3501.

use crate::check::{CheckError, LimitType};
use crate::state::{states_to_trace_value, ArrayState, Fingerprint, State};
use crate::storage::{CapacityStatus, FingerprintSet};
use crate::var_index::VarRegistry;
use crate::Value;
use dashmap::DashMap;
use rustc_hash::{FxHashMap, FxHasher};
use std::hash::BuildHasherDefault;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{Mutex, OnceLock};

/// FxHasher-based BuildHasher for faster hashing of Fingerprint keys.
/// Since Fingerprint is already a 64-bit hash, FxHasher is much faster than SipHash.
pub(crate) type FxBuildHasher = BuildHasherDefault<FxHasher>;

/// FxHasher-based DashMap for concurrent fingerprint storage.
pub(crate) type FxDashMap<K, V> = DashMap<K, V, FxBuildHasher>;

/// Part of #3178: Append-only parent pointer log for trace reconstruction.
///
/// Replaces the previous `Arc<FxDashMap<Fingerprint, Fingerprint>>` to eliminate
/// per-state DashMap contention on the BFS hot path. Each worker appends to its
/// own shard (indexed by `worker_id`), so the hot path is contention-free.
/// After BFS completes, `build_map()` materializes the log into a HashMap for
/// backward chain walking (cold path only).
pub(crate) struct ParentLog {
    shards: Vec<Mutex<Vec<(Fingerprint, Fingerprint)>>>,
}

impl ParentLog {
    pub(crate) fn new(num_workers: usize) -> Self {
        Self {
            shards: (0..num_workers)
                .map(|_| Mutex::new(Vec::with_capacity(4096)))
                .collect(),
        }
    }

    /// Append a parent pointer from the given worker's shard.
    /// Each worker exclusively owns its shard, so the Mutex is uncontended.
    #[inline]
    pub(crate) fn append(&self, worker_id: usize, succ_fp: Fingerprint, parent_fp: Fingerprint) {
        self.shards[worker_id]
            .lock()
            .expect("invariant: ParentLog shard mutex should not be poisoned")
            .push((succ_fp, parent_fp));
    }

    /// Materialize the log into a HashMap for backward chain walking.
    /// Called once after BFS completes (cold path).
    pub(crate) fn build_map(&self) -> FxHashMap<Fingerprint, Fingerprint> {
        let total: usize = self
            .shards
            .iter()
            .map(|s| {
                s.lock()
                    .expect("invariant: ParentLog shard mutex should not be poisoned")
                    .len()
            })
            .sum();
        let mut map = FxHashMap::with_capacity_and_hasher(total, Default::default());
        for shard in &self.shards {
            for &(succ_fp, parent_fp) in shard
                .lock()
                .expect("invariant: ParentLog shard mutex should not be poisoned")
                .iter()
            {
                map.insert(succ_fp, parent_fp);
            }
        }
        map
    }

    /// Estimate memory bytes consumed by the parent log shards.
    ///
    /// Each shard is a `Vec<(Fingerprint, Fingerprint)>` (16 bytes per entry)
    /// plus `Mutex` overhead. Sums capacity across all shards.
    ///
    /// Part of #4080: OOM safety — parallel internal memory accounting.
    pub(crate) fn estimate_memory_bytes(&self) -> usize {
        let entry_size = std::mem::size_of::<(Fingerprint, Fingerprint)>(); // 16 bytes
        let mutex_overhead = 40; // Mutex<Vec<_>> struct overhead per shard
        let mut total: usize = 0;
        for shard in &self.shards {
            let cap = shard
                .lock()
                .expect("invariant: ParentLog shard mutex should not be poisoned")
                .capacity();
            total = total.saturating_add(cap.saturating_mul(entry_size));
            total = total.saturating_add(mutex_overhead);
        }
        total.saturating_add(std::mem::size_of::<Self>())
    }

    /// Bulk-load entries (used for checkpoint restore).
    pub(crate) fn extend(&self, entries: impl Iterator<Item = (Fingerprint, Fingerprint)>) {
        // Load everything into shard 0 — sharding is for hot-path contention
        // avoidance, not for correctness.
        let mut shard = self.shards[0]
            .lock()
            .expect("invariant: ParentLog shard mutex should not be poisoned");
        shard.extend(entries);
    }
}

/// Part of #3011: Type alias for the successor witness DashMap.
/// Each entry maps a canonical source FP to concrete successor `(canon_fp, ArrayState)` pairs.
/// Used during BFS under symmetry to record concrete successor states for liveness checking.
pub(crate) type SuccessorWitnessDashMap = FxDashMap<Fingerprint, Vec<(Fingerprint, ArrayState)>>;

/// Capacity status encoded as u8 for atomic operations.
/// 0 = Normal, 1 = Warning, 2 = Critical
pub(crate) const CAPACITY_NORMAL: u8 = 0;
pub(crate) const CAPACITY_WARNING: u8 = 1;
pub(crate) const CAPACITY_CRITICAL: u8 = 2;
const HANDLE_STATE_OVERRIDE_UNSET: u8 = 0;
const HANDLE_STATE_OVERRIDE_FALSE: u8 = 1;
const HANDLE_STATE_OVERRIDE_TRUE: u8 = 2;

static FORCE_HANDLE_STATE: AtomicU8 = AtomicU8::new(HANDLE_STATE_OVERRIDE_UNSET);

/// Convert CapacityStatus to u8 for atomic operations.
pub(crate) fn capacity_status_to_u8(status: &CapacityStatus) -> u8 {
    match status {
        CapacityStatus::Normal => CAPACITY_NORMAL,
        CapacityStatus::Warning { .. } => CAPACITY_WARNING,
        CapacityStatus::Critical { .. } => CAPACITY_CRITICAL,
        _ => CAPACITY_NORMAL,
    }
}

/// Check capacity status and emit warning if status has changed.
///
/// Returns the new status value to store in the atomic.
pub(crate) fn check_and_warn_capacity(seen_fps: &dyn FingerprintSet, last_status: &AtomicU8) {
    let status = seen_fps.capacity_status();
    let status_u8 = capacity_status_to_u8(&status);
    let prev_status = last_status.load(Ordering::Relaxed);

    // Only warn if status has changed
    if status_u8 == prev_status {
        return;
    }

    match status {
        CapacityStatus::Normal => {
            // Status improved back to normal - no warning needed
        }
        CapacityStatus::Warning {
            count,
            capacity,
            usage,
        } => {
            eprintln!(
                "Warning: Fingerprint storage at {:.1}% capacity ({} / {} states). \
                 Consider increasing --mmap-fingerprints capacity if state space is larger.",
                usage * 100.0,
                count,
                capacity
            );
        }
        CapacityStatus::Critical {
            count,
            capacity,
            usage,
        } => {
            eprintln!(
                "CRITICAL: Fingerprint storage at {:.1}% capacity ({} / {} states). \
                 Insert failures imminent! Increase --mmap-fingerprints capacity.",
                usage * 100.0,
                count,
                capacity
            );
        }
        _ => {}
    }

    last_status.store(status_u8, Ordering::Relaxed);
}

// Part of #3318: HandleState is the default parallel mode.
// HandleState eliminates Arc atomic contention during state cloning,
// giving 6–14% wall-time improvement across worker counts.
// Set TLA2_DISABLE_HANDLE_STATE=1 to opt out for comparison. Integration tests
// can use `set_use_handle_state_override()` to bypass the cached env lookup.
pub(crate) fn use_handle_state() -> bool {
    match FORCE_HANDLE_STATE.load(Ordering::Relaxed) {
        HANDLE_STATE_OVERRIDE_TRUE => return true,
        HANDLE_STATE_OVERRIDE_FALSE => return false,
        _ => {}
    }
    static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    !crate::debug_env::env_flag_is_set(&FLAG, "TLA2_DISABLE_HANDLE_STATE")
}

/// Temporarily override [`use_handle_state`] for integration tests.
///
/// Production behavior remains env-driven (`TLA2_DISABLE_HANDLE_STATE`), but
/// integration tests need a process-local override because the env lookup is
/// cached on first read.
#[cfg(any(test, feature = "testing"))]
pub fn set_use_handle_state_override(value: bool) -> UseHandleStateGuard {
    let previous = FORCE_HANDLE_STATE.swap(
        if value {
            HANDLE_STATE_OVERRIDE_TRUE
        } else {
            HANDLE_STATE_OVERRIDE_FALSE
        },
        Ordering::Relaxed,
    );
    UseHandleStateGuard { previous }
}

/// RAII guard that restores the previous HandleState override on drop.
#[cfg(any(test, feature = "testing"))]
pub struct UseHandleStateGuard {
    previous: u8,
}

#[cfg(any(test, feature = "testing"))]
impl Drop for UseHandleStateGuard {
    fn drop(&mut self) {
        FORCE_HANDLE_STATE.store(self.previous, Ordering::Relaxed);
    }
}

// Part of #3258: shared-queue transport pilot for cheap-state specs.
// When enabled (TLA2_SHARED_QUEUE=1), workers share a single FIFO frontier
// instead of per-worker deques with work stealing. This matches TLC's
// queue topology for direct throughput comparison.
feature_flag!(pub(crate) use_shared_queue, "TLA2_SHARED_QUEUE");

// Part of #3285, #3805: Per-slot fingerprint cache carry-through on the parallel
// ArrayState queue lane. Default ON since Wave 9: the extra Box<[u64]> allocation
// per enqueued state (~80 bytes for 10 vars) is far cheaper than recomputing N
// value fingerprints on every dequeue via ensure_fp_cache_with_value_fps().
// Set TLA2_NO_PRESERVE_VALUE_FPS=1 to disable.
pub(crate) fn parallel_preserve_value_fps() -> bool {
    static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("TLA2_NO_PRESERVE_VALUE_FPS").is_err())
}

/// Re-export canonical checker_ops functions for parallel-internal use.
///
/// Part of #2356 (Phase 2): invariant evaluation.
/// Part of #2565: constraint evaluation — all 3 functions moved to `checker_ops.rs`
/// as the single canonical implementations shared by both sequential and parallel
/// checker paths. These re-exports preserve the `pub(crate)` import path that
/// `parallel/worker/` and `parallel/checker.rs` use.
pub(crate) use crate::checker_ops::{check_invariants_array_state, check_state_constraints_array};

// Part of #1139: Reconstruct trace value for TLCExt!Trace in parallel mode.
//
// ParallelChecker only supports trace reconstruction when `store_full_states` is enabled
// (parent pointers + in-memory state storage).
pub(crate) fn trace_value_for_fp(
    state_fp: Fingerprint,
    parent_log: &ParentLog,
    seen: &FxDashMap<Fingerprint, ArrayState>,
    var_registry: &VarRegistry,
) -> Value {
    // Part of #3178: Build parent map from the append-only log (cold path).
    let parents = parent_log.build_map();

    // Walk back through parent pointers to collect fingerprint path.
    let mut fps: Vec<Fingerprint> = Vec::new();
    let mut current = state_fp;
    loop {
        fps.push(current);
        match parents.get(&current) {
            Some(parent_ref) => current = *parent_ref,
            None => break, // Reached initial state
        }
    }
    fps.reverse(); // initial -> current

    // Part of #1922: Use explicit loop instead of filter_map to detect and warn
    // about missing fingerprints in release builds. filter_map silently drops
    // missing states, producing truncated counterexample traces — dangerous for
    // a verification tool.
    let mut states: Vec<State> = Vec::with_capacity(fps.len());
    let mut missing_count: usize = 0;
    for fp in &fps {
        match seen.get(fp) {
            Some(arr) => states.push(arr.to_state(var_registry)),
            None => missing_count += 1,
        }
    }
    if missing_count > 0 {
        // eprintln is intentional: tla-check has no tracing subscriber, so
        // tracing::warn! would be silently dropped. This warning MUST reach
        // users in release builds — it indicates a truncated counterexample.
        eprintln!(
            "Warning: trace_value_for_fp: {missing_count}/{} fingerprints not found in \
             seen set — counterexample trace may be incomplete",
            fps.len()
        );
    }

    states_to_trace_value(&states)
}

/// Result from a worker thread
#[derive(Debug)]
pub(crate) enum WorkerResult {
    /// Found an invariant violation
    Violation {
        invariant: String,
        state_fp: Fingerprint,
        stats: WorkerStats,
    },
    /// Found an action-level PROPERTY violation.
    PropertyActionViolation {
        property: String,
        state_fp: Fingerprint,
        stats: WorkerStats,
    },
    /// Found a deadlock
    Deadlock {
        state_fp: Fingerprint,
        stats: WorkerStats,
    },
    /// Worker completed successfully (no violations)
    Done(WorkerStats),
    /// Worker encountered an error
    Error(CheckError, WorkerStats),
    /// Exploration limit was reached
    LimitReached {
        limit_type: LimitType,
        stats: WorkerStats,
    },
}

/// Statistics from a single worker
#[derive(Debug, Clone, Default)]
pub(crate) struct WorkerStats {
    /// Worker identifier used when emitting per-worker profiling summaries.
    pub(crate) worker_id: Option<usize>,
    pub(crate) states_explored: usize,
    pub(crate) transitions: usize,
    /// Profiling: number of work steals from injector/other workers
    pub(crate) steals: usize,
    /// Profiling: steal attempts against the global injector after local-queue miss.
    pub(crate) injector_steal_attempts: usize,
    /// Profiling: successful steals from the global injector.
    pub(crate) injector_steal_successes: usize,
    /// Profiling: number of pushes to global injector
    pub(crate) injector_pushes: usize,
    /// Profiling: peer deque probes after injector stealing fails.
    pub(crate) peer_steal_probes: usize,
    /// Profiling: successful steals from peer deques.
    pub(crate) peer_steal_successes: usize,
    /// Profiling: duplicate fingerprint encounters
    pub(crate) dedup_hits: usize,
    /// Profiling: states pre-admitted via streaming preadmit (#3254)
    pub(crate) streaming_preadmits: usize,
    /// Profiling: parent states that had to rebuild missing `value_fps`.
    pub(crate) base_fp_cache_rebuilds: usize,
    /// Timing: nanoseconds in base-state fp cache preparation (sub-bucket of enum_ns).
    /// Part of #3285: isolates `ensure_fp_cache_with_value_fps` cost.
    pub(crate) enum_base_cache_ns: u64,
    /// Timing: nanoseconds in action evaluation proper (sub-bucket of enum_ns).
    /// Part of #3285: derived as `enum_ns - enum_base_cache_ns - enum_diff_fp_ns`.
    pub(crate) enum_eval_ns: u64,
    /// Timing: nanoseconds in per-diff `compute_diff_fingerprint_with_xor` (sub-bucket of enum_ns).
    /// Part of #3285: isolates streaming sink fingerprint cost.
    pub(crate) enum_diff_fp_ns: u64,
    /// Profiling: empty poll retries (no work found)
    pub(crate) empty_polls: usize,
    /// Profiling: compare_exchange retries while publishing negative work batches.
    pub(crate) work_remaining_cas_retries: usize,
    /// Profiling: active_workers idle->active transitions.
    pub(crate) active_worker_activations: usize,
    /// Profiling: active_workers active->idle transitions.
    pub(crate) active_worker_deactivations: usize,
    /// Timing: nanoseconds spent in enumeration
    pub(crate) enum_ns: u64,
    /// Timing: nanoseconds spent in fingerprint contains check
    pub(crate) contains_ns: u64,
    /// Timing: nanoseconds spent in fingerprint insert
    pub(crate) insert_ns: u64,
    /// Timing: nanoseconds spent in invariant checking
    pub(crate) invariant_ns: u64,
    /// Timing: nanoseconds spent materializing states
    pub(crate) materialize_ns: u64,
    /// Timing: nanoseconds spent evaluating state/action constraints
    pub(crate) constraints_ns: u64,
    /// Part of #606: Disabled action counts by error type
    pub(crate) disabled_choose_failed: usize,
    pub(crate) disabled_not_in_domain: usize,
    pub(crate) disabled_index_out_of_bounds: usize,
    pub(crate) disabled_no_such_field: usize,
    pub(crate) disabled_division_by_zero: usize,
    pub(crate) disabled_type_error: usize,
    /// Part of #3700: JIT invariant cache hits (invariant fully evaluated by JIT).
    pub(crate) jit_hits: usize,
    /// Part of #3700: JIT invariant cache misses (fell back to bytecode/tree-walk).
    pub(crate) jit_misses: usize,
    /// Part of #3935: JIT dispatch — invariant was compiled but returned FallbackNeeded.
    pub(crate) jit_fallback: usize,
    /// Part of #3935: JIT dispatch — invariant was not in the JIT cache at all.
    pub(crate) jit_not_compiled: usize,
    /// Number of fully JIT-covered invariant evaluations cross-checked via the interpreter.
    pub(crate) jit_verify_checked: usize,
    /// Number of JIT/interpreter invariant mismatches observed during cross-checking.
    pub(crate) jit_verify_mismatches: usize,
    /// Part of #3285: Intern attribution counters (populated at worker exit).
    pub(crate) intern_counters: Option<tla_value::InternAttributionCounters>,
    /// Part of #3706: POR — number of states where ample set was a proper subset.
    pub(crate) por_reductions: u64,
    /// Part of #3706: POR — total actions skipped via ample set reduction.
    pub(crate) por_actions_skipped: u64,
    /// Part of #3706: POR — total states processed through POR analysis.
    pub(crate) por_total_states: u64,
    /// Work stealing: maximum observed local queue depth for this worker.
    pub(crate) max_local_queue_depth: usize,
    /// Work stealing: total nanoseconds this worker spent idle (no work available).
    pub(crate) idle_ns: u64,
    /// Work stealing: nanoseconds spent in successful steal operations.
    pub(crate) steal_latency_ns: u64,
    /// Work stealing: total successor states this worker generated (enqueued).
    pub(crate) states_generated: usize,
}

// Part of #3254: promoted to feature_flag! for release-mode timing.
feature_flag!(pub(crate) timing_enabled, "TLA2_TIMING");
#[inline(always)]
pub(crate) fn timing_start() -> Option<std::time::Instant> {
    timing_enabled().then(std::time::Instant::now)
}
#[inline(always)]
pub(crate) fn accum_ns(bucket: &mut u64, started: Option<std::time::Instant>) {
    if let Some(t) = started {
        *bucket += t.elapsed().as_nanos() as u64;
    }
}

pub(crate) const PARALLEL_PROFILING_ENV: &str = "TLA2_PARALLEL_PROFILING";

// Parallel profiling is intentionally release-active because the large scaling
// benchmarks are only practical to diagnose with optimized binaries.
pub(crate) fn parallel_profiling_from_env(cache: &OnceLock<bool>) -> bool {
    *cache.get_or_init(|| {
        std::env::var(PARALLEL_PROFILING_ENV)
            .map(|value| value == "1")
            .unwrap_or(false)
    })
}

pub(crate) fn parallel_profiling() -> bool {
    static FLAG: OnceLock<bool> = OnceLock::new();
    parallel_profiling_from_env(&FLAG)
}

pub(crate) fn emit_parallel_profile_worker_stats(stats: &WorkerStats) {
    if !parallel_profiling() {
        return;
    }
    let Some(worker_id) = stats.worker_id else {
        return;
    };
    let peer_probe_ratio = if stats.peer_steal_successes > 0 {
        stats.peer_steal_probes as f64 / stats.peer_steal_successes as f64
    } else {
        0.0
    };
    eprintln!(
        "=== Parallel Profiling Worker {worker_id} ===\n  States explored: {}\n  States generated: {}\n  Injector steals: attempts={} successes={}\n  Peer steals: probes={} successes={} probe/success={peer_probe_ratio:.1}\n  work_remaining CAS retries: {}\n  active_workers transitions: +{} / -{}\n  Max local queue depth: {}\n  Idle time: {:.2}ms\n  Steal latency: {:.2}ms\n  JIT invariant: hits={} misses={} fallback={} not_compiled={}",
        stats.states_explored,
        stats.states_generated,
        stats.injector_steal_attempts,
        stats.injector_steal_successes,
        stats.peer_steal_probes,
        stats.peer_steal_successes,
        stats.work_remaining_cas_retries,
        stats.active_worker_activations,
        stats.active_worker_deactivations,
        stats.max_local_queue_depth,
        stats.idle_ns as f64 / 1_000_000.0,
        stats.steal_latency_ns as f64 / 1_000_000.0,
        stats.jit_hits,
        stats.jit_misses,
        stats.jit_fallback,
        stats.jit_not_compiled,
    );
    // Part of #3285: Print intern attribution counters if available.
    if let Some(ic) = &stats.intern_counters {
        let total_hits = ic.frozen_string_hits
            + ic.frozen_token_hits
            + ic.frozen_set_hits
            + ic.frozen_int_func_hits
            + ic.overlay_string_hits
            + ic.overlay_token_hits
            + ic.overlay_set_hits
            + ic.overlay_int_func_hits;
        let total_inserts = ic.new_string_inserts + ic.new_set_inserts + ic.new_int_func_inserts;
        eprintln!(
            "  Intern attribution (hits={total_hits} inserts={total_inserts}):\n    frozen:  strings={} tokens={} sets={} int_funcs={}\n    overlay: strings={} tokens={} sets={} int_funcs={}\n    new:     strings={} sets={} int_funcs={}",
            ic.frozen_string_hits, ic.frozen_token_hits, ic.frozen_set_hits, ic.frozen_int_func_hits,
            ic.overlay_string_hits, ic.overlay_token_hits, ic.overlay_set_hits, ic.overlay_int_func_hits,
            ic.new_string_inserts, ic.new_set_inserts, ic.new_int_func_inserts,
        );
    }
    eprintln!("==========================================");
}

/// Batch size for work_remaining counter updates.
/// Updating work_remaining atomically every state causes cache line bouncing.
/// Batching locally and flushing periodically reduces contention.
pub(crate) const WORK_BATCH_SIZE: usize = 256;
