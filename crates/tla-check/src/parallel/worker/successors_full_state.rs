// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Full-state successor processing pipeline.
//!
//! Handles the primary BFS successor path where each successor is materialized
//! as a full `ArrayState` from a `DiffSuccessor`. Includes VIEW fingerprinting,
//! constraint checking, symmetry canonicalization, and implied action evaluation.
//!
//! Part of #3472: extracted from `successors.rs` to bring both files under
//! the 500-line limit.

use super::super::{accum_ns, timing_start, WorkerResult};
use super::coordination::{flush_transition_batch, snapshot_stop_and_send};
use super::helpers::compute_view_fingerprint_array;
use super::observer::{observe_candidate_successor, ObservationSignal, SuccessorObservationCtx};
use super::successors::{FullStateSuccessorCtx, SuccessorProcessCtx};
use crate::check::model_checker::{CoreStepAction, CoreStepInput};
use crate::eval::EvalCtx;
use crate::state::{
    compute_canonical_fingerprint_from_compact_array, compute_diff_fingerprint_with_xor,
    compute_fingerprint_from_compact_array, ArrayState, DiffSuccessor, Fingerprint,
};
use crate::EvalCheckError;

pub(super) struct FullStateLoopState {
    succ_fps_for_liveness: Option<Vec<Fingerprint>>,
    succ_witnesses_for_liveness: Option<Vec<(Fingerprint, ArrayState)>>,
    transition_batch: usize,
    has_eval_implied_actions: bool,
    has_constraints: bool,
    scratch: ArrayState,
}

impl FullStateLoopState {
    pub(super) fn new(spc: &SuccessorProcessCtx<'_, '_>, current_arr: &ArrayState) -> Self {
        // Part of #3011: Collect concrete successor states under symmetry for liveness
        // witness evaluation. Only allocated when both symmetry AND liveness are active.
        let succ_witnesses_for_liveness = if spc.successor_witnesses_cache.is_some() {
            Some(Vec::new())
        } else {
            None
        };

        Self {
            succ_fps_for_liveness: spc.init_liveness_cache(),
            succ_witnesses_for_liveness,
            transition_batch: 0,
            has_eval_implied_actions: !spc.inv_ctx.eval_implied_actions.is_empty(),
            has_constraints: !spc.inv_ctx.config.constraints.is_empty()
                || !spc.inv_ctx.config.action_constraints.is_empty(),
            // Part of #3023: Reuse one scratch buffer across all successors.
            scratch: ArrayState::new(current_arr.len()),
        }
    }
}

pub(super) fn finish_full_state_loop(
    spc: &mut SuccessorProcessCtx<'_, '_>,
    state_fp: Fingerprint,
    mut loop_state: FullStateLoopState,
) {
    flush_transition_batch(spc.total_transitions, &mut loop_state.transition_batch);
    spc.flush_work_completion(
        state_fp,
        loop_state.succ_fps_for_liveness,
        loop_state.succ_witnesses_for_liveness,
    );
}

pub(super) fn process_one_full_state_diff<F>(
    ctx: &mut EvalCtx,
    spc: &mut SuccessorProcessCtx<'_, '_>,
    state_ctx: &FullStateSuccessorCtx<'_>,
    loop_state: &mut FullStateLoopState,
    mut diff: DiffSuccessor,
    enqueue: &F,
) -> bool
where
    F: Fn(ArrayState, usize),
{
    // Part of #1102: action constraints evaluate in current-state context.
    ctx.set_tlc_level(state_ctx.current_level);

    // Part of #3254: Time materialize + fingerprint as one bucket.
    let t_mat = timing_start();

    // Part of #3022: Materialize diff changes before materializing the full
    // ArrayState. This ensures lazy values are resolved before fingerprinting.
    if let Err(e) = crate::materialize::materialize_diff_changes(ctx, &mut diff.changes, spc.spec_may_produce_lazy) {
        flush_transition_batch(spc.total_transitions, &mut loop_state.transition_batch);
        snapshot_stop_and_send(ctx, spc.stats, spc.stop, spc.result_tx, |stats| {
            WorkerResult::Error(EvalCheckError::Eval(e).into(), stats)
        });
        return true;
    }

    // Part of #3022: Materialize DiffSuccessor directly into ArrayState,
    // bypassing the DiffSuccessor→ArrayState→State→ArrayState chain.
    let (succ_fp_from_diff, combined_xor) = compute_diff_fingerprint_with_xor(
        state_ctx.current_arr,
        &diff.changes,
        spc.inv_ctx.var_registry,
    );
    diff.materialize_into(
        &mut loop_state.scratch,
        state_ctx.current_arr,
        succ_fp_from_diff,
        combined_xor,
    );
    accum_ns(&mut spc.stats.materialize_ns, t_mat);

    // Part of #3254: Time constraint check separately (MCBoulanger hot path).
    let t_con = timing_start();
    let constraint_signal = match observe_candidate_successor(
        ctx,
        spc.inv_ctx,
        spc.stop,
        spc.result_tx,
        spc.stats,
        &SuccessorObservationCtx {
            current: state_ctx.current_arr,
            parent_fp: state_ctx.fp,
            succ: &loop_state.scratch,
            succ_fp: succ_fp_from_diff,
            succ_depth: spc.succ_depth,
            succ_level: spc.succ_level,
        },
    ) {
        Ok(signal) => signal,
        Err(error) => {
            flush_transition_batch(spc.total_transitions, &mut loop_state.transition_batch);
            snapshot_stop_and_send(ctx, spc.stats, spc.stop, spc.result_tx, |stats| {
                WorkerResult::Error(error, stats)
            });
            return true;
        }
    };
    if loop_state.has_constraints {
        accum_ns(&mut spc.stats.constraints_ns, t_con);
    }
    match constraint_signal {
        ObservationSignal::Continue => {}
        ObservationSignal::Skip => return false,
        ObservationSignal::Stop => return true,
        ObservationSignal::Invariant(_) => {
            debug_assert!(
                false,
                "candidate successor observers should not emit invariant outcomes"
            );
        }
    }
    spc.stats.transitions += 1;
    loop_state.transition_batch += 1;

    // Part of #2018: Materialize lazy values remaining in base state slots.
    // Diff changes were already materialized above; this handles inherited slots.
    let t_mat2 = timing_start();
    if let Err(e) = crate::materialize::materialize_array_state(ctx, &mut loop_state.scratch, spc.spec_may_produce_lazy) {
        flush_transition_batch(spc.total_transitions, &mut loop_state.transition_batch);
        snapshot_stop_and_send(ctx, spc.stats, spc.stop, spc.result_tx, |stats| {
            WorkerResult::Error(EvalCheckError::Eval(e).into(), stats)
        });
        return true;
    }

    let succ_fp = if let Some(ref view_name) = state_ctx.cached_view_name {
        match compute_view_fingerprint_array(ctx, &loop_state.scratch, view_name, spc.succ_level) {
            Ok(fp) => fp,
            Err(e) => {
                flush_transition_batch(spc.total_transitions, &mut loop_state.transition_batch);
                snapshot_stop_and_send(ctx, spc.stats, spc.stop, spc.result_tx, |stats| {
                    WorkerResult::Error(e, stats)
                });
                return true;
            }
        }
    } else if !spc.mvperms.is_empty() {
        compute_canonical_fingerprint_from_compact_array(
            loop_state.scratch.values(),
            spc.inv_ctx.var_registry,
            spc.mvperms,
        )
    } else {
        // No VIEW and no symmetry: reuse the diff-computed fingerprint.
        // Both compute_diff_fingerprint_with_xor and compute_fingerprint_from_array
        // use the same XOR + finalize algorithm, and the base state is already
        // materialized (from the BFS queue), so the results are identical.
        // This avoids a Vec<Value> allocation + O(n) rehash per successor.
        debug_assert_eq!(
            succ_fp_from_diff,
            {
                compute_fingerprint_from_compact_array(
                    loop_state.scratch.values(),
                    spc.inv_ctx.var_registry,
                )
            },
            "diff-computed fingerprint must match full recomputation"
        );
        succ_fp_from_diff
    };

    accum_ns(&mut spc.stats.materialize_ns, t_mat2);

    if !spc.mvperms.is_empty() {
        loop_state.scratch.set_cached_fingerprint(succ_fp);
    }

    if let Some(ref mut fps) = loop_state.succ_fps_for_liveness {
        fps.push(succ_fp);
    }

    if let Some(ref mut witnesses) = loop_state.succ_witnesses_for_liveness {
        witnesses.push((succ_fp, loop_state.scratch.clone()));
    }

    if loop_state.has_eval_implied_actions
        && succ_fp != state_ctx.fp
        && spc.check_eval_implied_actions_pre_admit(
            ctx,
            state_ctx.current_arr,
            &loop_state.scratch,
            succ_fp,
        )
    {
        flush_transition_batch(spc.total_transitions, &mut loop_state.transition_batch);
        return true;
    }

    let input = CoreStepInput {
        parent_fp: state_ctx.fp,
        succ: &loop_state.scratch,
        succ_fp,
        succ_depth: spc.succ_depth,
        succ_level: spc.succ_level,
    };
    match spc.run_core_step_for(ctx, &input, enqueue) {
        Ok(CoreStepAction::SkipDuplicate) | Ok(CoreStepAction::Enqueue) => false,
        Ok(CoreStepAction::Stop(_)) => {
            flush_transition_batch(spc.total_transitions, &mut loop_state.transition_batch);
            true
        }
        Err(_e) => {
            debug_eprintln!(
                crate::check::debug::tla2_debug(),
                "[parallel-worker] core step error: {}",
                _e
            );
            flush_transition_batch(spc.total_transitions, &mut loop_state.transition_batch);
            true
        }
    }
}

/// Process full-state successors: deadlock check, VIEW fingerprinting,
/// constraint checking, dedup, invariant checking, and enqueuing.
///
/// Part of #3022: Takes `&ArrayState` + `Vec<DiffSuccessor>` instead of
/// `&State` + `Vec<State>`. This eliminates 3 redundant O(n) conversions per
/// successor (State→ArrayState at call site, ArrayState→State inside enumerate,
/// State→ArrayState per successor in processing). Successors are materialized
/// from DiffSuccessor directly into ArrayState, matching TLC's single-representation
/// pipeline.
///
/// Called by [`WorkerBfsCtx::enumerate_and_process`] after array-based enumeration.
///
/// Returns `true` if the worker must stop (violation, error, or deadlock sent
/// to `result_tx`).
pub(super) fn process_full_state_successors<F>(
    ctx: &mut EvalCtx,
    spc: &mut SuccessorProcessCtx<'_, '_>,
    state_ctx: &FullStateSuccessorCtx<'_>,
    diffs: Vec<DiffSuccessor>,
    had_raw_successors: bool,
    enqueue: F,
) -> bool
where
    F: Fn(ArrayState, usize),
{
    if spc.check_deadlock_if_no_successors(
        ctx,
        state_ctx.current_arr,
        state_ctx.fp,
        had_raw_successors,
    ) {
        return true;
    }
    let mut loop_state = FullStateLoopState::new(spc, state_ctx.current_arr);

    for diff in diffs {
        if process_one_full_state_diff(ctx, spc, state_ctx, &mut loop_state, diff, &enqueue) {
            return true;
        }
    }
    finish_full_state_loop(spc, state_ctx.fp, loop_state);
    false
}
