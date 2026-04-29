// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{HashMap, Value};
use std::cell::RefCell;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
// Debug flags, profiling counters, TLC registers, and random seed infrastructure.
// Extracted from core.rs as part of #1219 decomposition.

// Part of #3962: Consolidated RANDOM_BASE_SEED + EVAL_WORKER_COUNT + TLC_REGISTERS
// into a single TLS struct. Previously 3 separate `thread_local!` declarations —
// each access was a separate `_tlv_get_addr` call on macOS (~5ns each). These are
// typically accessed together during TLCGet/TLCSet evaluation, and all cleared
// together in `clear_tlc_registers()`. Now 1 TLS access covers all three.
// Wave 25: PROCESS_START_TIME consolidated here (from builtin_tlc_get.rs) — 1 more
// thread_local eliminated. Accessed only during TLCGet("duration") evaluation.
pub(super) struct EvalDebugState {
    /// Lifecycle: RuntimeSetting. Set once per run; not a cache.
    pub(super) random_base_seed: u64,
    /// Lifecycle: RuntimeSetting. Set once per worker thread; not a cache.
    pub(super) worker_count: usize,
    /// Lifecycle: PerPhase (cleared at phase/run boundaries via clear_tlc_registers).
    /// Not bounded; register count is controlled by the spec author.
    pub(super) tlc_registers: HashMap<i64, Value>,
    /// Part of #3962 Wave 25: Consolidated from builtin_tlc_get.rs PROCESS_START_TIME.
    /// Seconds since Unix epoch at thread-local initialization time.
    /// Used by TLCGet("duration") to compute elapsed time.
    pub(super) process_start_time: i64,
}

thread_local! {
    pub(super) static EVAL_DEBUG_STATE: RefCell<EvalDebugState> =
        RefCell::new(EvalDebugState {
            random_base_seed: 12346,
            worker_count: 1,
            tlc_registers: HashMap::new(),
            process_start_time: {
                use std::time::{SystemTime, UNIX_EPOCH};
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .map(|d| d.as_secs() as i64)
                    .unwrap_or(0)
            },
        });
}

// Emit at most one process-level warning about TLC register thread-local behavior.
static TLC_REGISTERS_PARALLEL_WARNING_EMITTED: AtomicBool = AtomicBool::new(false);

/// Set the worker count visible to eval builtins in the current thread.
///
/// Parallel worker threads call this once during initialization. Sequential paths
/// should keep the default value (`1`).
pub fn set_eval_worker_count(worker_count: usize) {
    let normalized = worker_count.max(1);
    EVAL_DEBUG_STATE.with(|s| s.borrow_mut().worker_count = normalized);
}

#[inline]
fn maybe_warn_parallel_tlc_register_usage() -> bool {
    let workers = EVAL_DEBUG_STATE.with(|s| s.borrow().worker_count);
    if workers <= 1 {
        return false;
    }
    if TLC_REGISTERS_PARALLEL_WARNING_EMITTED.swap(true, Ordering::Relaxed) {
        return false;
    }
    eprintln!(
        "Warning: TLCSet/TLCGet registers are thread-local per worker (TLC IdThread semantics); \
         values written in one worker are not visible to other workers."
    );
    true
}

/// Get the value of a TLC register by integer index.
/// Returns None if the register has not been set.
/// Part of #814: TLC throws error for unset registers; caller decides behavior.
pub(super) fn tlc_register_get(idx: i64) -> Option<Value> {
    let _ = maybe_warn_parallel_tlc_register_usage();
    EVAL_DEBUG_STATE.with(|s| s.borrow().tlc_registers.get(&idx).cloned())
}

/// Set the value of a TLC register by integer index.
/// Part of #814: Matches TLC's TLCSet(i, v) behavior.
pub(super) fn tlc_register_set(idx: i64, value: Value) {
    let _ = maybe_warn_parallel_tlc_register_usage();
    EVAL_DEBUG_STATE.with(|s| {
        s.borrow_mut().tlc_registers.insert(idx, value);
    });
}

/// Get all TLC registers as a function from index to value.
/// Part of #814: Used for TLCGet("all") which returns all register values.
pub(super) fn tlc_registers_get_all() -> HashMap<i64, Value> {
    let _ = maybe_warn_parallel_tlc_register_usage();
    EVAL_DEBUG_STATE.with(|s| s.borrow().tlc_registers.clone())
}

/// Clear all TLC registers (TLCSet/TLCGet storage).
/// Part of #1331: Exposed outside `#[cfg(test)]` so `reset_global_state()` can
/// clear thread-local eval state between model checking runs.
pub fn clear_tlc_registers() {
    EVAL_DEBUG_STATE.with(|s| s.borrow_mut().tlc_registers.clear());
}

#[cfg(test)]
fn reset_tlc_register_parallel_warning_for_test() {
    TLC_REGISTERS_PARALLEL_WARNING_EMITTED.store(false, Ordering::Relaxed);
}

/// Set the base seed for RandomElement operator.
/// This affects the "random" element selection: RandomElement(S) picks an element
/// based on fingerprint(S) mixed with this seed. Changing the seed changes which
/// elements are selected, but the selection remains deterministic for a given seed.
pub fn set_random_seed(seed: u64) {
    EVAL_DEBUG_STATE.with(|s| {
        s.borrow_mut().random_base_seed = seed.wrapping_add(1);
    });
}

/// Read the current random base seed value.
///
/// Part of #3962: Accessor function for consolidated `EVAL_DEBUG_STATE`.
/// Previously callers accessed `RANDOM_BASE_SEED` thread_local directly;
/// now routed through the consolidated struct.
pub(super) fn random_base_seed() -> u64 {
    EVAL_DEBUG_STATE.with(|s| s.borrow().random_base_seed)
}

/// Read the process start time (seconds since Unix epoch).
///
/// Part of #3962 Wave 25: Accessor for consolidated `EVAL_DEBUG_STATE.process_start_time`.
/// Previously accessed via standalone `PROCESS_START_TIME` thread_local in builtin_tlc_get.rs.
pub(super) fn process_start_time() -> i64 {
    EVAL_DEBUG_STATE.with(|s| s.borrow().process_start_time)
}

// Performance profiling counters for eval() - enabled via TLA2_PROFILE_EVAL env var.
// Part of #188: Understanding per-state overhead.

/// Atomic counter for total eval() calls.
pub(super) static EVAL_CALL_COUNT: AtomicU64 = AtomicU64::new(0);

// debug_flag! macro defined in crate::debug_env (via #[macro_use])

feature_flag!(pub(super) profile_eval, "TLA2_PROFILE_EVAL");
debug_flag!(pub(super) debug_prime, "TLA2_DEBUG_PRIME"); // #246
debug_flag!(pub(super) debug_unchanged, "TLA2_DEBUG_UNCHANGED"); // #295
debug_flag!(pub(super) debug_instance_subst, "TLA2_DEBUG_INSTANCE_SUBST"); // #295
debug_flag!(pub(super) debug_module_ref, "TLA2_DEBUG_MODULE_REF"); // #295
debug_flag!(pub(super) debug_or_eval, "TLA2_DEBUG_OR");
debug_flag!(pub(super) debug_zero_cache, "TLA2_DEBUG_ZERO_CACHE");
feature_flag!(pub(crate) debug_bytecode_vm, "TLA2_DEBUG_BYTECODE_VM");

/// Issue #284: Zero-arg operator caching with dependency validation.
///
/// In TLC, LazyValue caching is scoped to a single evaluation. In TLA2, we use dependency-based
/// validation: each cached entry records which locals, state vars, and next-state vars it read.
/// On lookup, `op_cache_entry_valid()` validates that all recorded deps match the current context.
///
/// Part of #346 Phase 4: Instead of clearing `ZERO_ARG_OP_CACHE` at every eval_entry call, we now
/// use state-based invalidation. The cache is only cleared when the state pointer changes,
/// allowing cache hits across multiple eval_entry calls for the same state (e.g., when evaluating
/// multiple actions/invariants). The deps validation ensures correctness for any entries that
/// survive across state transitions.
///
/// Set TLA2_NO_LOCAL_OPS_CACHE=1 to bypass caching entirely for debugging.
#[cfg(debug_assertions)]
pub(super) fn no_local_ops_cache() -> bool {
    use std::sync::OnceLock;
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        let enabled = std::env::var("TLA2_NO_LOCAL_OPS_CACHE").is_ok();
        if enabled {
            eprintln!("[INFO] TLA2_NO_LOCAL_OPS_CACHE enabled - bypassing zero-arg operator cache");
        }
        enabled
    })
}
#[cfg(not(debug_assertions))]
pub(super) fn no_local_ops_cache() -> bool {
    false
}

/// Print eval() profile statistics (call this at end of model checking).
pub fn print_eval_profile_stats() {
    // Part of #3805: Always print zero-arg cache stats if enabled (separate flag).
    crate::cache::zero_arg_cache::print_zero_arg_cache_stats();

    if !profile_eval() {
        return;
    }
    let count = EVAL_CALL_COUNT.swap(0, Ordering::Relaxed);
    eprintln!("\n=== Eval Profile ===");
    eprintln!("  Total eval() calls: {count}");
    eprintln!("  ---");
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    // These tests mutate process-global warning state and should not run concurrently.
    static TEST_GUARD: Mutex<()> = Mutex::new(());

    fn clear_tlc_registers_for_test() {
        EVAL_DEBUG_STATE.with(|s| s.borrow_mut().tlc_registers.clear());
    }

    #[test]
    fn tlc_register_parallel_warning_emits_once() {
        let _guard = TEST_GUARD
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        reset_tlc_register_parallel_warning_for_test();
        set_eval_worker_count(2);
        assert!(maybe_warn_parallel_tlc_register_usage());
        assert!(!maybe_warn_parallel_tlc_register_usage());
        set_eval_worker_count(1);
        assert!(!maybe_warn_parallel_tlc_register_usage());
    }

    #[test]
    fn tlc_register_storage_is_thread_local() {
        let _guard = TEST_GUARD
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        clear_tlc_registers_for_test();
        set_eval_worker_count(1);

        tlc_register_set(7, Value::int(1));
        assert_eq!(tlc_register_get(7), Some(Value::int(1)));

        let child_val = std::thread::spawn(|| {
            set_eval_worker_count(1);
            assert_eq!(tlc_register_get(7), None);
            tlc_register_set(7, Value::int(2));
            tlc_register_get(7)
        })
        .join()
        .expect("thread join");

        assert_eq!(child_val, Some(Value::int(2)));
        assert_eq!(tlc_register_get(7), Some(Value::int(1)));
    }
}
