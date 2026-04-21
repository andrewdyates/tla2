// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared successor processing context and diff-based successor pipeline.
//!
//! Part of #2492: extracted from `helpers.rs` to separate successor processing
//! from work coordination and worker lifecycle concerns.
//!
//! Full-state successor processing lives in [`successors_full_state`].

use super::super::{FxDashMap, WorkerResult, WorkerStats};
use super::coordination::{record_state_completion_profiled, snapshot_stop_and_send};
use super::core_adapter::ParallelAdapter;
use super::observer::{observe_state_completion, ObservationSignal, StateCompletionCtx};
use super::{InvariantCheckCtx, StopCtx};
use crate::check::model_checker::{run_core_step, CoreStepAction, CoreStepInput};
use crate::eval::EvalCtx;
use crate::state::{compute_diff_fingerprint_with_xor, ArrayState, DiffSuccessor, Fingerprint};
use crate::EvalCheckError;
use crossbeam_channel::Sender;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

// Re-export full-state pipeline types so existing imports continue to work.
pub(super) use super::successors_full_state::{
    finish_full_state_loop, process_full_state_successors, process_one_full_state_diff,
    FullStateLoopState,
};

/// Shared context for successor processing pipelines.
///
/// Groups the 13 parameters common to both [`process_full_state_successors`] and
/// [`process_diff_successors`], reducing their signatures from 19/17 params
/// to 7/5 params respectively.
///
/// Part of #2356 Step 3d: parameter reduction toward TLC's single-Worker.run()
/// pattern where shared context is held in struct fields, not passed as args.
pub(super) struct SuccessorProcessCtx<'a, 'inv> {
    pub(super) inv_ctx: &'a InvariantCheckCtx<'inv>,
    pub(super) stop: &'a StopCtx<'inv>,
    pub(super) result_tx: &'a Sender<WorkerResult>,
    pub(super) stats: &'a mut WorkerStats,
    pub(super) check_deadlock: bool,
    pub(super) succ_depth: usize,
    pub(super) succ_level: u32,
    pub(super) local_work_delta: &'a mut isize,
    pub(super) work_remaining: &'a AtomicUsize,
    pub(super) max_depth_atomic: &'a AtomicUsize,
    pub(super) total_transitions: &'a AtomicUsize,
    /// Part of #2740: Optional successor cache for post-BFS liveness checking.
    /// When `Some`, all successor fps (including to already-seen states) are
    /// collected and stored per source state.
    pub(super) successors_cache: &'a Option<Arc<FxDashMap<Fingerprint, Vec<Fingerprint>>>>,
    /// Part of #3011: Concrete successor witness states for symmetry liveness.
    /// `None` when symmetry OR liveness is not active.
    pub(super) successor_witnesses_cache: &'a Option<Arc<super::super::SuccessorWitnessDashMap>>,
    /// Part of #3011: Symmetry permutations for canonical fingerprinting.
    pub(super) mvperms: &'a [crate::value::MVPerm],
    /// Part of #4053: Skip materialization when spec has no lazy-producing AST nodes.
    pub(super) spec_may_produce_lazy: bool,
}

impl SuccessorProcessCtx<'_, '_> {
    /// Initialize liveness successor cache if liveness checking is active.
    ///
    /// Part of #2356 Step 3d: extracted from duplicate setup in both
    /// `process_full_state_successors` and `process_diff_successors`.
    pub(super) fn init_liveness_cache(&self) -> Option<Vec<Fingerprint>> {
        if self.successors_cache.is_some() {
            Some(Vec::new())
        } else {
            None
        }
    }

    /// Check for deadlock when a state has no successors.
    ///
    /// Evaluates terminal state predicate before reporting deadlock. Terminal
    /// states (e.g., "SAT"/"UNSAT" in solver specs) are intentional end points
    /// and should not be reported as deadlocks.
    ///
    /// Returns `true` if the worker must stop (deadlock or error sent to channel).
    ///
    /// Part of #2356 Step 3d: extracted from duplicate deadlock checks in both
    /// `process_full_state_successors` and `process_diff_successors`.
    pub(super) fn check_deadlock_if_no_successors(
        &mut self,
        ctx: &mut EvalCtx,
        parent_arr: &ArrayState,
        parent_fp: Fingerprint,
        has_successors: bool,
    ) -> bool {
        match observe_state_completion(
            ctx,
            self.inv_ctx,
            self.stop,
            self.result_tx,
            self.stats,
            &StateCompletionCtx {
                state_fp: parent_fp,
                state: parent_arr,
                has_successors,
            },
            self.check_deadlock,
        ) {
            Ok(ObservationSignal::Continue | ObservationSignal::Skip) => false,
            Ok(ObservationSignal::Stop) => true,
            Ok(ObservationSignal::Invariant(_)) => {
                debug_assert!(
                    false,
                    "state completion observers should not emit invariant outcomes"
                );
                false
            }
            Err(error) => {
                snapshot_stop_and_send(ctx, self.stats, self.stop, self.result_tx, |stats| {
                    WorkerResult::Error(error, stats)
                });
                true
            }
        }
    }

    /// Check eval-based implied actions for a transition (#2983).
    /// Returns `true` if the caller should stop (violation or error), `false` to continue.
    pub(super) fn check_eval_implied_actions_pre_admit(
        &mut self,
        ctx: &mut EvalCtx,
        parent_arr: &ArrayState,
        succ_arr: &ArrayState,
        succ_fp: Fingerprint,
    ) -> bool {
        match crate::checker_ops::check_eval_implied_actions_for_transition(
            ctx,
            self.inv_ctx.eval_implied_actions,
            parent_arr,
            succ_arr,
            succ_fp,
        ) {
            crate::checker_ops::InvariantOutcome::Ok
            | crate::checker_ops::InvariantOutcome::ViolationContinued => false,
            crate::checker_ops::InvariantOutcome::Violation {
                invariant,
                state_fp,
            } => {
                if self.inv_ctx.continue_on_error {
                    let _ = self
                        .inv_ctx
                        .first_action_property_violation
                        .set((invariant, state_fp));
                    false
                } else {
                    snapshot_stop_and_send(ctx, self.stats, self.stop, self.result_tx, |stats| {
                        WorkerResult::PropertyActionViolation {
                            property: invariant,
                            state_fp,
                            stats,
                        }
                    });
                    true
                }
            }
            crate::checker_ops::InvariantOutcome::Error(error) => {
                snapshot_stop_and_send(ctx, self.stats, self.stop, self.result_tx, |stats| {
                    WorkerResult::Error(error, stats)
                });
                true
            }
        }
    }

    /// Run the core admit→check→enqueue step for one successor via `ParallelAdapter`.
    ///
    /// Creates a temporary `ParallelAdapter` from the shared context fields, executes
    /// `run_core_step`, and returns the action. This eliminates duplicated adapter
    /// construction in `process_full_state_successors` and `process_diff_successors`.
    ///
    /// Part of #2356 Step 3d: deduplicated adapter construction.
    pub(super) fn run_core_step_for<F>(
        &mut self,
        ctx: &mut EvalCtx,
        input: &CoreStepInput<'_>,
        enqueue: &F,
    ) -> Result<CoreStepAction<bool>, bool>
    where
        F: Fn(ArrayState, usize),
    {
        let mut adapter = ParallelAdapter {
            ctx,
            inv_ctx: self.inv_ctx,
            stop: self.stop,
            result_tx: self.result_tx,
            stats: self.stats,
            local_work_delta: self.local_work_delta,
            work_remaining: self.work_remaining,
            max_depth_atomic: self.max_depth_atomic,
            enqueue_fn: |succ: &ArrayState, depth: usize| {
                enqueue(succ.clone(), depth);
            },
        };
        run_core_step(&mut adapter, input)
    }

    /// Handle state completion bookkeeping (shared between state and diff paths).
    ///
    /// Performs: work delta decrement / negative batch flush and liveness
    /// successor cache storage. Positive deltas stay local until the worker
    /// crosses an idle, barrier, or stop boundary.
    ///
    /// Part of #2356 Step 3d: extracted from identical post-loop code in both
    /// `process_full_state_successors` and `process_diff_successors`.
    pub(super) fn flush_work_completion(
        &mut self,
        state_fp: Fingerprint,
        succ_fps_for_liveness: Option<Vec<Fingerprint>>,
        succ_witnesses_for_liveness: Option<Vec<(Fingerprint, ArrayState)>>,
    ) {
        record_state_completion_profiled(
            self.local_work_delta,
            self.work_remaining,
            Some(self.stats),
        );

        // Part of #2740: Store collected successor fps for post-BFS liveness checking.
        if let (Some(cache), Some(fps)) = (self.successors_cache, succ_fps_for_liveness) {
            cache.insert(state_fp, fps);
        }

        // Part of #3011: Store concrete successor witness states for symmetry liveness.
        if let (Some(cache), Some(witnesses)) =
            (self.successor_witnesses_cache, succ_witnesses_for_liveness)
        {
            cache.insert(state_fp, witnesses);
        }
    }
}

/// Per-state context for full-state successor processing.
///
/// Bundles the parameters that are constant across all successors of a single
/// parent state, reducing argument counts in [`process_one_full_state_diff`]
/// and [`process_full_state_successors`].
///
/// Part of #3308: argument count reduction.
pub(super) struct FullStateSuccessorCtx<'a> {
    pub(super) cached_view_name: &'a Option<String>,
    pub(super) current_arr: &'a ArrayState,
    pub(super) fp: Fingerprint,
    pub(super) current_level: u32,
}

/// Process diff-based successors: deadlock check, incremental fingerprinting,
/// dedup, invariant checking, and enqueuing.
///
/// This is the diff-based counterpart to [`process_full_state_successors`]. It handles
/// the optimized path where successor states are represented as diffs from the
/// base state, enabling incremental fingerprinting.
///
/// Used only when VIEW, state constraints, and action constraints are all absent
/// (those require full-state enumeration via `process_full_state_successors`).
///
/// Part of #2356 (Phase 2): extracted from inline diff processing in `run_array.rs`
/// to reduce duplication and converge toward the TLC single-Worker.run() pattern.
///
/// Called by [`WorkerBfsCtx::process_diffs`] after depth/level computation.
///
/// Returns `true` if the worker must stop (violation, error, or deadlock sent
/// to `result_tx`).
pub(super) fn process_diff_successors<F>(
    ctx: &mut EvalCtx,
    spc: &mut SuccessorProcessCtx<'_, '_>,
    base_array: &ArrayState,
    parent_fp: Fingerprint,
    diffs: Vec<DiffSuccessor>,
    enqueue: F,
) -> bool
where
    F: Fn(ArrayState, usize),
{
    // Part of #2356 Step 3d: shared deadlock + liveness cache init.
    if spc.check_deadlock_if_no_successors(ctx, base_array, parent_fp, !diffs.is_empty()) {
        return true;
    }
    let mut succ_fps_for_liveness = spc.init_liveness_cache();

    spc.stats.transitions += diffs.len();
    spc.total_transitions
        .fetch_add(diffs.len(), Ordering::Relaxed);

    // Part of #2356 Step 3b: compute once before loop.
    let has_eval_implied_actions = !spc.inv_ctx.eval_implied_actions.is_empty();

    // Part of #3023: Pre-allocate scratch buffer for successor materialization.
    // Reused across loop iterations to avoid Box<[Value]> alloc+free per successor.
    // For specs with ~95% duplicate rate, this saves ~19 out of 20 allocations.
    let mut scratch = ArrayState::new(base_array.len());

    for mut diff in diffs {
        // Part of #2018: Materialize lazy values (SetPred, LazyFunc, Closure)
        // before fingerprinting. Without this, parallel mode uses
        // process-local IDs for fingerprints (#1989 non-determinism).
        if let Err(e) = crate::materialize::materialize_diff_changes(ctx, &mut diff.changes, spc.spec_may_produce_lazy) {
            snapshot_stop_and_send(ctx, spc.stats, spc.stop, spc.result_tx, |stats| {
                WorkerResult::Error(EvalCheckError::Eval(e).into(), stats)
            });
            return true;
        }

        // Part of #328: Compute fingerprint incrementally from diff changes.
        let (succ_fp, combined_xor) =
            compute_diff_fingerprint_with_xor(base_array, &diff.changes, spc.inv_ctx.var_registry);

        // Part of #2740: Record successor fp for liveness checking.
        if let Some(ref mut fps) = succ_fps_for_liveness {
            fps.push(succ_fp);
        }

        // Part of #3023: Materialize into scratch buffer instead of allocating.
        // Reuses the existing Box<[Value]> allocation — only N Value clones, no malloc.
        diff.materialize_into(&mut scratch, base_array, succ_fp, combined_xor);

        // Part of #2983: Eval-based implied actions for ModuleRef/INSTANCE properties.
        // Part of #3140: Skip stuttering transitions.
        if has_eval_implied_actions
            && succ_fp != parent_fp
            && spc.check_eval_implied_actions_pre_admit(ctx, base_array, &scratch, succ_fp)
        {
            return true;
        }

        // Part of #2356 Step 3c: Core admit→check→enqueue via shared reducer.
        // Part of #2356 Step 3d: adapter construction deduplicated via shared method.
        let input = CoreStepInput {
            parent_fp,
            succ: &scratch,
            succ_fp,
            succ_depth: spc.succ_depth,
            succ_level: spc.succ_level,
        };
        match spc.run_core_step_for(ctx, &input, &enqueue) {
            Ok(CoreStepAction::SkipDuplicate) | Ok(CoreStepAction::Enqueue) => {}
            Ok(CoreStepAction::Stop(_)) => return true,
            Err(_e) => {
                // Part of #2793: Log error detail before stopping.
                debug_eprintln!(
                    crate::check::debug::tla2_debug(),
                    "[parallel-worker] core step error (diff): {}",
                    _e
                );
                return true;
            }
        }
    }

    // Diff-based path: no witness collection (symmetry disables diffs via
    // supports_diffs, so successor_witnesses_cache is always None here).
    spc.flush_work_completion(parent_fp, succ_fps_for_liveness, None);

    false
}
