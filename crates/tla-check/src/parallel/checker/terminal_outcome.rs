// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Terminal outcome types for parallel worker result collection.
//!
//! Part of #1433 Step 4: terminal-outcome precedence is encoded in a single
//! reduction function (`merge_worker_outcome`) instead of scattered ad-hoc
//! `if first_X.is_none()` checks. This makes precedence testable and prevents
//! per-branch condition drift (#1850).

use super::*;
use crate::EvalCheckError;

/// Terminal outcome reported by a worker thread.
///
/// Precedence during collection: Error > Violation > Deadlock > Limit.
/// When multiple workers report different outcomes, `merge_worker_outcome`
/// keeps the higher-precedence one.
///
/// Note: `Done` results don't produce a `TerminalOutcome` — they only
/// contribute stats. Depth-limit and deferred violations (continue-on-error)
/// are resolved from shared atomics after worker collection, not here.
#[derive(Debug)]
pub(super) enum TerminalOutcome {
    /// An evaluation or internal error (highest precedence).
    Error(CheckError),
    /// An invariant violation with the triggering state fingerprint.
    Violation {
        invariant: String,
        state_fp: Fingerprint,
    },
    /// An action-level PROPERTY violation with the triggering state fingerprint.
    PropertyActionViolation {
        property: String,
        state_fp: Fingerprint,
    },
    /// A deadlock (state with no enabled successors).
    Deadlock { state_fp: Fingerprint },
    /// An exploration limit was reached (States or Exit).
    Limit(LimitType),
}

impl TerminalOutcome {
    /// Precedence rank. Lower value = higher priority.
    pub(super) fn precedence(&self) -> u8 {
        match self {
            Self::Error(_) => 0,
            Self::Violation { .. } => 1,
            Self::PropertyActionViolation { .. } => 1,
            Self::Deadlock { .. } => 2,
            Self::Limit(_) => 3,
        }
    }
}

/// Merge two terminal outcomes, keeping the higher-precedence one.
///
/// Error > Violation > Deadlock > Limit.
///
/// This is the single source of truth for worker outcome precedence,
/// replacing the ad-hoc `if first_X.is_none()` checks that were
/// scattered through the collection loop (Part of #1433 Step 4).
pub(super) fn merge_worker_outcome(
    current: TerminalOutcome,
    incoming: TerminalOutcome,
) -> TerminalOutcome {
    if incoming.precedence() < current.precedence() {
        incoming
    } else {
        current
    }
}

/// Aggregate all worker stats including profiling counters.
pub(super) fn aggregate_stats(total: &mut WorkerStats, stats: &WorkerStats) {
    total.states_explored += stats.states_explored;
    total.transitions += stats.transitions;
    total.steals += stats.steals;
    total.injector_steal_attempts += stats.injector_steal_attempts;
    total.injector_steal_successes += stats.injector_steal_successes;
    total.injector_pushes += stats.injector_pushes;
    total.peer_steal_probes += stats.peer_steal_probes;
    total.peer_steal_successes += stats.peer_steal_successes;
    total.dedup_hits += stats.dedup_hits;
    total.streaming_preadmits += stats.streaming_preadmits;
    total.base_fp_cache_rebuilds += stats.base_fp_cache_rebuilds;
    total.empty_polls += stats.empty_polls;
    total.work_remaining_cas_retries += stats.work_remaining_cas_retries;
    total.active_worker_activations += stats.active_worker_activations;
    total.active_worker_deactivations += stats.active_worker_deactivations;
    // Timing stats
    total.enum_ns += stats.enum_ns;
    total.enum_base_cache_ns += stats.enum_base_cache_ns;
    total.enum_eval_ns += stats.enum_eval_ns;
    total.enum_diff_fp_ns += stats.enum_diff_fp_ns;
    total.contains_ns += stats.contains_ns;
    total.insert_ns += stats.insert_ns;
    total.invariant_ns += stats.invariant_ns;
    total.materialize_ns += stats.materialize_ns;
    total.constraints_ns += stats.constraints_ns;
    // Part of #606: Disabled action stats
    total.disabled_choose_failed += stats.disabled_choose_failed;
    total.disabled_not_in_domain += stats.disabled_not_in_domain;
    total.disabled_index_out_of_bounds += stats.disabled_index_out_of_bounds;
    total.disabled_no_such_field += stats.disabled_no_such_field;
    total.disabled_division_by_zero += stats.disabled_division_by_zero;
    total.disabled_type_error += stats.disabled_type_error;
    total.jit_hits += stats.jit_hits;
    total.jit_misses += stats.jit_misses;
    total.jit_fallback += stats.jit_fallback;
    total.jit_not_compiled += stats.jit_not_compiled;
    total.jit_verify_checked += stats.jit_verify_checked;
    total.jit_verify_mismatches += stats.jit_verify_mismatches;
    // Part of #3706: POR stats
    total.por_reductions += stats.por_reductions;
    total.por_actions_skipped += stats.por_actions_skipped;
    total.por_total_states += stats.por_total_states;
    // Work stealing load balance metrics
    if stats.max_local_queue_depth > total.max_local_queue_depth {
        total.max_local_queue_depth = stats.max_local_queue_depth;
    }
    total.idle_ns += stats.idle_ns;
    total.steal_latency_ns += stats.steal_latency_ns;
    total.states_generated += stats.states_generated;
    // Part of #3285: Aggregate intern attribution counters
    if let Some(ic) = &stats.intern_counters {
        let total_ic = total.intern_counters.get_or_insert_with(Default::default);
        total_ic.frozen_string_hits += ic.frozen_string_hits;
        total_ic.frozen_token_hits += ic.frozen_token_hits;
        total_ic.frozen_set_hits += ic.frozen_set_hits;
        total_ic.frozen_int_func_hits += ic.frozen_int_func_hits;
        total_ic.overlay_string_hits += ic.overlay_string_hits;
        total_ic.overlay_token_hits += ic.overlay_token_hits;
        total_ic.overlay_set_hits += ic.overlay_set_hits;
        total_ic.overlay_int_func_hits += ic.overlay_int_func_hits;
        total_ic.new_string_inserts += ic.new_string_inserts;
        total_ic.new_set_inserts += ic.new_set_inserts;
        total_ic.new_int_func_inserts += ic.new_int_func_inserts;
    }
}

impl ParallelChecker {
    /// Classify a `WorkerResult` into stats and an optional terminal outcome.
    ///
    /// ExitRequested errors are converted to `Limit(Exit)` with appropriate
    /// side effects (stop flag, states snapshot), matching the sequential
    /// checker's `check_error_to_result()` at `check/api.rs:343`.
    pub(super) fn classify_worker_result(
        &self,
        result: WorkerResult,
    ) -> (WorkerStats, Option<TerminalOutcome>) {
        match result {
            WorkerResult::Violation {
                invariant,
                state_fp,
                stats,
            } => (
                stats,
                Some(TerminalOutcome::Violation {
                    invariant,
                    state_fp,
                }),
            ),
            WorkerResult::PropertyActionViolation {
                property,
                state_fp,
                stats,
            } => (
                stats,
                Some(TerminalOutcome::PropertyActionViolation { property, state_fp }),
            ),
            WorkerResult::Deadlock { state_fp, stats } => {
                (stats, Some(TerminalOutcome::Deadlock { state_fp }))
            }
            WorkerResult::Done(stats) => (stats, None),
            WorkerResult::Error(e, stats) => {
                // Part of #1875: ExitRequested is a control-flow signal
                // (TLCSet("exit", TRUE)), not a real error. Convert to
                // LimitReached(Exit), matching the sequential checker's
                // check_error_to_result() at check/api.rs:343.
                if let CheckError::Eval(EvalCheckError::Eval(
                    tla_value::error::EvalError::ExitRequested { .. },
                )) = &e
                {
                    // Set stop_flag so other workers terminate gracefully
                    self.stop_flag.store(true, Ordering::SeqCst);
                    // Part of #2165/#2309: ExitRequested can be the first and only
                    // stop signal. Snapshot the current state count now so
                    // final stats do not fall back to a post-exit count.
                    // OnceLock::set is first-writer-wins; no-op if already set.
                    let states_at_exit = self.states_count();
                    let _ = self.states_at_stop.set(states_at_exit);
                    (stats, Some(TerminalOutcome::Limit(LimitType::Exit)))
                } else {
                    (stats, Some(TerminalOutcome::Error(e)))
                }
            }
            WorkerResult::LimitReached { limit_type, stats } => {
                (stats, Some(TerminalOutcome::Limit(limit_type)))
            }
        }
    }
}
