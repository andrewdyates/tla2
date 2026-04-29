// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared types and helpers for BFS successor processing.
//!
//! Part of #2677 Phase 2/3: extracted from `engine.rs` to separate the
//! per-iteration successor generation and pipeline processing from the
//! BFS dispatch loop. Two paths exist: diff-based (fast, incremental
//! fingerprinting) and full-state (fallback, explicit fingerprinting).
//!
//! The processing functions live in `diff_successors.rs` and
//! `full_state_successors.rs`. This file holds shared types and helper
//! methods used by both paths.

use super::super::frontier::BfsFrontier;
#[cfg(debug_assertions)]
use super::super::run_debug::DebugSuccessorCtx;
use super::super::run_helpers::BfsProfile;
use super::super::{ArrayState, CheckResult, Fingerprint, ModelChecker};
use super::iter_state::BfsIterState;
use super::observer::{
    CompositeObserver, ExplorationSignal, StateCompletionCtx, SuccessorObservationCtx,
};
use super::storage_modes::BfsStorage;
use crate::checker_ops::InvariantOutcome;
#[cfg(debug_assertions)]
use crate::var_index::VarRegistry;

/// Outcome of processing one BFS iteration's successors.
#[allow(clippy::large_enum_variant)]
pub(super) enum BfsIterOutcome {
    /// All successors processed normally; continue to next BFS state.
    Continue,
    /// BFS loop should terminate with this result.
    Terminate(CheckResult),
}

/// Metadata for a successor that already passed the read-only dedup pre-filter.
pub(super) struct PendingSuccessor {
    /// Fingerprint of the parent state that generated this successor.
    pub parent_fp: Fingerprint,
    /// Fingerprint of the successor state.
    pub succ_fp: Fingerprint,
    /// BFS depth of the successor (`parent_depth + 1`).
    pub succ_depth: usize,
    /// TLC-compatible level of the successor (`succ_depth + 1`).
    pub succ_level: u32,
}

impl ModelChecker<'_> {
    /// Run state-completion observers with automatic error/terminal handling.
    #[allow(clippy::result_large_err)]
    pub(super) fn run_state_completion_observers<S: BfsStorage>(
        &mut self,
        iter_state: &mut BfsIterState,
        storage: &mut S,
        observer: &mut CompositeObserver,
        successors_empty: bool,
        had_raw_successors: bool,
        full_successors: Option<&[(ArrayState, Fingerprint)]>,
        action_tags: &[Option<usize>],
    ) -> Result<(), BfsIterOutcome> {
        match observer.observe_state_completion(
            self,
            &StateCompletionCtx {
                state_fp: iter_state.fp(),
                state: iter_state.array(),
                successors_empty,
                had_raw_successors,
                full_successors,
                action_tags,
            },
        ) {
            Ok(ExplorationSignal::Continue | ExplorationSignal::Skip) => Ok(()),
            Ok(ExplorationSignal::Stop(result)) => {
                iter_state.return_to(storage, self);
                Err(BfsIterOutcome::Terminate(result))
            }
            Err(error) => Err(BfsIterOutcome::Terminate(
                self.bfs_error_return(iter_state, storage, error),
            )),
        }
    }

    /// Read-only dedup pre-filter with profiling (optimization, not authority).
    ///
    /// Part of #2708: this is Phase 1 of the two-phase dedup pattern — a
    /// read-only `contains_checked` that filters the majority of duplicates
    /// without cloning state. The dedup *authority* is `admit_successor`
    /// (Phase 2), which uses atomic `insert_checked` and handles the
    /// TOCTOU window where another worker inserts between the two phases.
    ///
    /// Part of #2677 Phase 2.
    #[allow(clippy::result_large_err)]
    pub(super) fn check_seen_with_profile<S: BfsStorage>(
        &mut self,
        iter_state: &mut BfsIterState,
        storage: &mut S,
        succ_fp: Fingerprint,
        prof: &mut BfsProfile,
    ) -> Result<bool, BfsIterOutcome> {
        let prof_t = prof.now();
        let result = match self.is_state_seen_checked(succ_fp) {
            Ok(seen) => Ok(seen),
            Err(result) => {
                iter_state.return_to(storage, self);
                Err(BfsIterOutcome::Terminate(result))
            }
        };
        prof.accum_dedup(prof_t);
        result
    }

    /// Handle the result of an implied action check for one transition.
    ///
    /// Returns `Some(result)` if the BFS loop should exit (terminal violation
    /// or error). Returns `None` to continue normal processing.
    ///
    /// Part of #2677 Phase 2.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn handle_implied_action_outcome<S: BfsStorage>(
        &mut self,
        iter_state: &mut BfsIterState,
        storage: &mut S,
        outcome: InvariantOutcome,
        parent_fp: Fingerprint,
        succ: &ArrayState,
        succ_fp: Fingerprint,
        succ_depth: usize,
    ) -> Option<CheckResult> {
        match outcome {
            InvariantOutcome::Ok | InvariantOutcome::ViolationContinued => None,
            InvariantOutcome::Violation { invariant, .. } => {
                if let Err(result) =
                    self.stage_successor_for_terminal_trace(parent_fp, succ, succ_fp, succ_depth)
                {
                    iter_state.return_to(storage, self);
                    return Some(self.finalize_terminal_result_with_storage(result));
                }
                // BUG FIX #2834: Implied actions come from PROPERTY entries, so
                // violations must be reported as PropertyViolation (not
                // InvariantViolation). TLC reports these as property violations.
                self.set_trace_context_for_successor(parent_fp, succ);
                self.stats.max_depth = self.stats.max_depth.max(succ_depth);
                self.stats.states_found = self.states_count();
                if self.record_action_property_violation(invariant.clone(), succ_fp) {
                    self.update_coverage_totals();
                    let trace = self.reconstruct_trace(succ_fp);
                    let candidate = CheckResult::PropertyViolation {
                        property: invariant,
                        kind: crate::check::api::PropertyViolationKind::ActionLevel,
                        trace,
                        stats: self.stats.clone(),
                    };
                    self.clear_trace_context();
                    iter_state.return_to(storage, self);
                    return Some(self.finalize_terminal_result(candidate));
                }
                self.clear_trace_context();
                None
            }
            InvariantOutcome::Error(error) => {
                Some(self.bfs_error_return(iter_state, storage, error))
            }
        }
    }

    /// Check whether a cooperative symbolic engine (PDR) has proved all
    /// invariants hold, allowing BFS to skip per-state invariant evaluation.
    ///
    /// Returns `false` when cooperative mode is inactive (the common case).
    ///
    /// Part of #3773: CDEMC invariant skip when PDR proves safety.
    #[inline]
    pub(super) fn cooperative_invariants_proved(&self) -> bool {
        #[cfg(feature = "z4")]
        if let Some(ref cooperative) = self.cooperative {
            return cooperative.invariants_proved();
        }
        false
    }

    /// Check whether PDR has proved some (but not all) invariants.
    ///
    /// When true, BFS should use the partial-skip path: only check
    /// invariants that have NOT been proved by PDR.
    ///
    /// Returns `false` when cooperative mode is inactive or when either
    /// zero or all invariants are proved.
    ///
    /// Part of #3773, #3810: per-invariant proof tracking for CDEMC.
    #[inline]
    #[allow(dead_code)] // Used when z4 feature is active
    pub(in crate::check) fn cooperative_has_partial_proofs(&self) -> bool {
        #[cfg(feature = "z4")]
        if let Some(ref cooperative) = self.cooperative {
            return cooperative.has_partial_proofs();
        }
        false
    }

    /// Collect the names of invariants that have NOT been proved by PDR.
    ///
    /// Used by BFS to build the subset of `config.invariants` that still
    /// need per-state checking when PDR has proved some invariants.
    ///
    /// Returns `None` when cooperative mode is inactive or when no partial
    /// proofs exist (caller should use the full invariant list or skip all).
    ///
    /// Part of #3773, #3810: per-invariant proof tracking for CDEMC.
    #[allow(dead_code)] // Used when z4 feature is active
    pub(in crate::check) fn cooperative_unproved_invariants(&self) -> Option<Vec<String>> {
        if !self.cooperative_has_partial_proofs() {
            return None;
        }
        #[cfg(feature = "z4")]
        if let Some(ref cooperative) = self.cooperative {
            let mut indices = Vec::new();
            cooperative
                .per_invariant
                .collect_unproved_indices(&mut indices);
            let invariants = &self.config.invariants;
            let unproved: Vec<String> = indices
                .iter()
                .filter_map(|&i| invariants.get(i).cloned())
                .collect();
            if !unproved.is_empty() {
                return Some(unproved);
            }
        }
        None
    }

    /// Check whether the oracle routes ALL actions to `SymbolicOnly`,
    /// meaning BFS should skip successor generation entirely for this state.
    ///
    /// When all actions are `SymbolicOnly`, the symbolic engine (BMC/PDR)
    /// handles all successor generation, and BFS can skip the state without
    /// missing any reachable states -- the symbolic engine covers them.
    ///
    /// Returns `false` when:
    /// - Cooperative mode is inactive (no oracle)
    /// - Any action is `BfsOnly` or `Either` (BFS must still explore those)
    /// - The oracle has zero actions (degenerate case, BFS must explore)
    /// - The z4 feature is not enabled
    ///
    /// Zero overhead when `self.cooperative.is_none()`.
    ///
    /// Part of #3785: CDEMC per-action oracle routing.
    #[inline]
    pub(super) fn cooperative_oracle_skips_all_actions(&self) -> bool {
        #[cfg(feature = "z4")]
        {
            if let Some(ref cooperative) = self.cooperative {
                return cooperative.all_actions_symbolic_only();
            }
        }
        false
    }

    /// Record transition count and update coverage totals.
    ///
    /// Part of #2677 Phase 2.
    pub(super) fn record_transitions(&mut self, count: usize) {
        self.stats.transitions += count;
        if let Some(ref mut coverage) = self.stats.coverage {
            coverage.total_transitions = self.stats.transitions;
        }
    }

    /// Record monolithic successor count to cooperative per-action metrics.
    ///
    /// Only active when cooperative mode is enabled (fused BFS+symbolic).
    /// Zero overhead in non-fused mode: the `cooperative` field is `None`.
    ///
    /// Part of #3784.
    #[inline]
    #[allow(unused_variables)]
    pub(super) fn record_cooperative_monolithic_successors(&self, successor_count: usize) {
        #[cfg(feature = "z4")]
        if let Some(ref cooperative) = self.cooperative {
            cooperative.record_monolithic_firing(successor_count as u64);
        }
    }

    /// Record per-action successor count to cooperative metrics.
    ///
    /// Only active when cooperative mode is enabled (fused BFS+symbolic).
    /// Zero overhead in non-fused mode.
    ///
    /// Part of #3784.
    #[inline]
    #[allow(unused_variables)]
    pub(in crate::check::model_checker) fn record_cooperative_action_successors(
        &self,
        action_id: usize,
        successor_count: usize,
    ) {
        #[cfg(feature = "z4")]
        if let Some(ref cooperative) = self.cooperative {
            cooperative.record_action_firing(action_id, successor_count as u64);
        }
    }

    /// Finish processing a successor after the read-only dedup pre-filter.
    ///
    /// Runs the shared invariant -> authoritative admit -> enqueue sequence used
    /// by the sequential diff/full-state BFS paths once a successor is known to
    /// be worth the more expensive work.
    #[allow(clippy::result_large_err)]
    pub(super) fn finish_prefiltered_successor<
        S: BfsStorage,
        Q: BfsFrontier<Entry = S::QueueEntry>,
    >(
        &mut self,
        iter_state: &mut BfsIterState,
        storage: &mut S,
        queue: &mut Q,
        prof: &mut BfsProfile,
        observer: &mut CompositeObserver,
        succ: ArrayState,
        pending: PendingSuccessor,
    ) -> Result<(), BfsIterOutcome> {
        let PendingSuccessor {
            parent_fp,
            succ_fp,
            succ_depth,
            succ_level,
        } = pending;

        let prof_t_inv = prof.now();
        let signal = match observer.observe_successor(
            self,
            &SuccessorObservationCtx {
                current: iter_state.array(),
                parent_fp,
                succ: &succ,
                succ_fp,
                succ_depth,
                succ_level,
            },
        ) {
            Ok(signal) => signal,
            Err(error) => {
                return Err(BfsIterOutcome::Terminate(
                    self.bfs_error_return(iter_state, storage, error),
                ));
            }
        };
        if prof.do_profile {
            prof.invariant_us += prof_t_inv.elapsed().as_micros() as u64;
        }
        let (jit_hits, jit_misses) = self.take_jit_profile_counters();
        if prof.do_profile {
            prof.jit_hits += jit_hits;
            prof.jit_misses += jit_misses;
        }

        match signal {
            ExplorationSignal::Continue => {}
            ExplorationSignal::Skip => return Ok(()),
            ExplorationSignal::Stop(result) => {
                iter_state.return_to(storage, self);
                return Err(BfsIterOutcome::Terminate(result));
            }
        }

        let entry = match storage.admit_successor(succ_fp, succ, Some(parent_fp), succ_depth, self)
        {
            Ok(Some(entry)) => entry,
            Ok(None) => return Ok(()),
            Err(result) => {
                iter_state.return_to(storage, self);
                return Err(BfsIterOutcome::Terminate(result));
            }
        };

        self.stats.max_depth = self.stats.max_depth.max(succ_depth);
        queue.push(entry);
        self.stats.states_found += 1;
        self.stats.max_queue_depth = self.stats.max_queue_depth.max(queue.len());
        Ok(())
    }

    /// Emit BFS debug header: compute debug flags and conditionally print state line.
    ///
    /// Returns `(state_tlc_fp, need_detail_log, debug_actions_this_state)` where
    /// `need_detail_log` is true when `debug_log_bfs_successors` should be called.
    ///
    /// Part of #2677 Phase 3.
    #[cfg(debug_assertions)]
    pub(super) fn debug_bfs_state_header(
        &self,
        fp: Fingerprint,
        current_array: &ArrayState,
        current_depth: usize,
        succ_count: usize,
        mode: &str,
    ) -> (Option<u64>, bool, bool) {
        let (state_tlc_fp, debug_state, print_state_line, debug_actions_this_state) =
            self.debug_successor_flags(fp, current_array);
        if print_state_line {
            Self::debug_print_state_line(fp, state_tlc_fp, current_depth, succ_count, mode);
        }
        (
            state_tlc_fp,
            debug_state || debug_actions_this_state,
            debug_actions_this_state,
        )
    }

    /// Log detailed successor information for debug builds.
    ///
    /// Wraps `debug_log_successor_details` with a `DebugSuccessorCtx` to avoid
    /// duplicating the 8-field struct construction at each call site.
    ///
    /// Part of #2677 Phase 3.
    #[cfg(debug_assertions)]
    #[allow(clippy::too_many_arguments)]
    pub(super) fn debug_log_bfs_successors(
        &mut self,
        fp: Fingerprint,
        state_tlc_fp: Option<u64>,
        current_depth: usize,
        current_array: &ArrayState,
        registry: &VarRegistry,
        had_raw_successors: bool,
        debug_actions_this_state: bool,
        successors: &[(Fingerprint, ArrayState, Option<usize>)],
    ) {
        self.debug_log_successor_details(&DebugSuccessorCtx {
            fp,
            state_tlc_fp,
            current_depth,
            current_array,
            registry,
            had_raw_successors,
            debug_actions_this_state,
            successors,
        });
    }
}
