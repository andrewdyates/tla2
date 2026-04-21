// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Loop-invariant BFS worker context.
//!
//! Part of #2356: extracted from `successors/` to bring it under the
//! 500-line file size limit. `WorkerBfsCtx` groups the 11 parameters that
//! persist across the entire BFS loop; it creates a short-lived
//! [`SuccessorProcessCtx`] per parent state for the actual pipeline.

use super::super::{accum_ns, timing_start, FxDashMap, WorkerResult, WorkerStats};
use super::coordination::snapshot_stop_and_send;
use super::successors::{
    finish_full_state_loop, process_diff_successors, process_full_state_successors,
    process_one_full_state_diff, FullStateLoopState, FullStateSuccessorCtx, SuccessorProcessCtx,
};
use super::{InvariantCheckCtx, StopCtx};
use crate::coverage::DetectedAction;
use crate::enumerate::{
    enumerate_successors_array_as_diffs, enumerate_successors_array_as_diffs_into, DiffSink,
};
use crate::eval::EvalCtx;
use crate::por::{IndependenceMatrix, VisibilitySet};
use crate::state::{ArrayState, DiffSuccessor, Fingerprint};
use crate::EvalCheckError;
use crossbeam_channel::Sender;
use std::ops::ControlFlow;
use std::sync::atomic::AtomicUsize;
use std::sync::Arc;
use tla_core::ast::OperatorDef;
use tla_eval::tir::TirProgram;

/// Loop-invariant BFS worker context.
///
/// Groups the 11 parameters that persist across the entire BFS loop.
/// `succ_depth` and `succ_level` are computed once by the unified
/// `run_bfs_worker` loop and passed in per-call.
/// [`SuccessorProcessCtx`] is a short-lived struct created per-state from this
/// context with the pre-computed depth/level fields.
///
/// Part of #2356/#1931: enables a shared enumeration + processing method that
/// eliminates duplicate code between sequential and parallel paths.
pub(super) struct WorkerBfsCtx<'a, 'inv> {
    pub(super) ctx: &'a mut EvalCtx,
    pub(super) inv_ctx: &'a InvariantCheckCtx<'inv>,
    pub(super) stop: &'a StopCtx<'inv>,
    pub(super) result_tx: &'a Sender<WorkerResult>,
    pub(super) stats: &'a mut WorkerStats,
    pub(super) check_deadlock: bool,
    pub(super) local_work_delta: &'a mut isize,
    pub(super) work_remaining: &'a AtomicUsize,
    pub(super) max_depth_atomic: &'a AtomicUsize,
    pub(super) total_transitions: &'a AtomicUsize,
    pub(super) successors_cache: &'a Option<Arc<FxDashMap<Fingerprint, Vec<Fingerprint>>>>,
    /// Part of #3011: Concrete successor witness states for symmetry liveness.
    pub(super) successor_witnesses_cache: &'a Option<Arc<super::super::SuccessorWitnessDashMap>>,
    /// Part of #3011: Symmetry permutations for canonical fingerprinting.
    pub(super) mvperms: &'a [crate::value::MVPerm],
    /// Part of #4053: Skip materialization when spec has no lazy-producing AST nodes.
    pub(super) spec_may_produce_lazy: bool,
}

struct ConstrainedFullStateSink<'spc, 'a, 'inv, F>
where
    F: Fn(ArrayState, usize),
{
    spc: &'spc mut SuccessorProcessCtx<'a, 'inv>,
    current_arr: &'spc ArrayState,
    parent_fp: Fingerprint,
    current_level: u32,
    loop_state: &'spc mut FullStateLoopState,
    enqueue: &'spc F,
    count: usize,
    stopped: bool,
    inline_processing_ns: u64,
}

impl<'spc, 'a, 'inv, F> ConstrainedFullStateSink<'spc, 'a, 'inv, F>
where
    F: Fn(ArrayState, usize),
{
    fn new(
        spc: &'spc mut SuccessorProcessCtx<'a, 'inv>,
        current_arr: &'spc ArrayState,
        parent_fp: Fingerprint,
        current_level: u32,
        loop_state: &'spc mut FullStateLoopState,
        enqueue: &'spc F,
    ) -> Self {
        Self {
            spc,
            current_arr,
            parent_fp,
            current_level,
            loop_state,
            enqueue,
            count: 0,
            stopped: false,
            inline_processing_ns: 0,
        }
    }

    fn inline_processing_ns(&self) -> u64 {
        self.inline_processing_ns
    }
}

impl<F> DiffSink for ConstrainedFullStateSink<'_, '_, '_, F>
where
    F: Fn(ArrayState, usize),
{
    fn push(&mut self, _diff: DiffSuccessor) -> ControlFlow<()> {
        unreachable!("ConstrainedFullStateSink requires DiffSink::push_with_ctx")
    }

    fn push_with_ctx(&mut self, ctx: &mut EvalCtx, diff: DiffSuccessor) -> ControlFlow<()> {
        if self.stopped {
            return ControlFlow::Break(());
        }

        self.count += 1;
        let t_process = timing_start();
        // Part of #3278: constrained streaming enumerates and reduces on the
        // same EvalCtx. Guard the reducer's temporary bindings so constraint
        // checks and invariant evaluation cannot leak state back into the
        // still-active enumerator.
        let _scope_guard = ctx.scope_guard();
        let _state_guard = ctx.bind_state_env_guard(self.current_arr.env_ref());
        let state_ctx = FullStateSuccessorCtx {
            cached_view_name: &None,
            current_arr: self.current_arr,
            fp: self.parent_fp,
            current_level: self.current_level,
        };
        let should_stop = process_one_full_state_diff(
            ctx,
            self.spc,
            &state_ctx,
            self.loop_state,
            diff,
            self.enqueue,
        );
        accum_ns(&mut self.inline_processing_ns, t_process);
        if should_stop {
            self.stopped = true;
            return ControlFlow::Break(());
        }

        ControlFlow::Continue(())
    }

    fn count(&self) -> usize {
        self.count
    }

    fn is_stopped(&self) -> bool {
        self.stopped
    }
}

#[inline]
fn constrained_streaming_enum_ns(total_ns: u64, inline_processing_ns: u64) -> u64 {
    total_ns.saturating_sub(inline_processing_ns)
}

impl<'a, 'inv> WorkerBfsCtx<'a, 'inv> {
    /// Enumerate successors for a state and process them through the shared
    /// CoreStepAdapter pipeline.
    ///
    /// Part of #3022: Takes `&ArrayState` directly and uses
    /// `enumerate_successors_array_as_diffs` to avoid triple ArrayState<->State
    /// conversions. The previous implementation took `&State`, which required
    /// converting ArrayState→State at the call site, State→ArrayState inside
    /// `enumerate_successors`, and State→ArrayState for each successor in
    /// `process_full_state_successors`.
    ///
    /// Returns `true` if the worker should stop.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn enumerate_and_process<F>(
        &mut self,
        def: &OperatorDef,
        vars: &[Arc<str>],
        cached_view_name: &Option<String>,
        tir_leaf: Option<&TirProgram<'_>>,
        current_array: &ArrayState,
        fp: Fingerprint,
        current_level: u32,
        succ_depth: usize,
        succ_level: u32,
        enqueue: F,
    ) -> bool
    where
        F: Fn(ArrayState, usize),
    {
        // Set TLCGet("level") for current state's Next evaluation.
        self.ctx.set_tlc_level(current_level);

        // RAII guard restores env on drop, including early-return paths (Part of #2738)
        let _scope_guard = self.ctx.scope_guard();
        // Part of #3022: bind_state_array_guard uses O(1) array indexing instead
        // of iterating State's OrdMap entries.
        let _state_guard = self.ctx.bind_state_env_guard(current_array.env_ref());

        // Part of #3022: Use array-as-diffs enumeration to avoid the
        // State→ArrayState→DiffSuccessor→ArrayState→State→ArrayState chain.
        // enumerate_successors_array_as_diffs works entirely in ArrayState space.
        let t_enum = timing_start();
        let diffs =
            match enumerate_successors_array_as_diffs(self.ctx, def, current_array, vars, tir_leaf)
            {
                Ok(Some(d)) => d,
                Ok(None) => Vec::new(),
                Err(e) => {
                    snapshot_stop_and_send(
                        self.ctx,
                        self.stats,
                        self.stop,
                        self.result_tx,
                        |stats| WorkerResult::Error(EvalCheckError::Eval(e).into(), stats),
                    );
                    return true;
                }
            };
        accum_ns(&mut self.stats.enum_ns, t_enum);
        let had_raw_successors = !diffs.is_empty();

        drop(_state_guard);
        drop(_scope_guard);

        let ctx = &mut *self.ctx;
        let stats = &mut *self.stats;
        let local_work_delta = &mut *self.local_work_delta;
        let mut spc = SuccessorProcessCtx {
            inv_ctx: self.inv_ctx,
            stop: self.stop,
            result_tx: self.result_tx,
            stats,
            check_deadlock: self.check_deadlock,
            succ_depth,
            succ_level,
            local_work_delta,
            work_remaining: self.work_remaining,
            max_depth_atomic: self.max_depth_atomic,
            total_transitions: self.total_transitions,
            successors_cache: self.successors_cache,
            successor_witnesses_cache: self.successor_witnesses_cache,
            mvperms: self.mvperms,
            spec_may_produce_lazy: self.spec_may_produce_lazy,
        };
        let state_ctx = FullStateSuccessorCtx {
            cached_view_name,
            current_arr: current_array,
            fp,
            current_level,
        };
        process_full_state_successors(
            ctx,
            &mut spc,
            &state_ctx,
            diffs,
            had_raw_successors,
            enqueue,
        )
    }

    /// Enumerate per-action successors, filter them through POR's ample-set
    /// selection, then process only the chosen diffs through the shared reducer.
    ///
    /// This mirrors the sequential checker's POR path: actions are considered
    /// enabled only if they retain at least one successor after constraint
    /// filtering, but deadlock detection still consults the raw unfiltered
    /// successor count.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn enumerate_and_process_with_por<F>(
        &mut self,
        def: &OperatorDef,
        vars: &[Arc<str>],
        actions: &[DetectedAction],
        independence: &IndependenceMatrix,
        visibility: &VisibilitySet,
        cached_view_name: &Option<String>,
        current_array: &ArrayState,
        fp: Fingerprint,
        current_level: u32,
        succ_depth: usize,
        succ_level: u32,
        enqueue: F,
    ) -> bool
    where
        F: Fn(ArrayState, usize),
    {
        if actions.is_empty() {
            return self.enumerate_and_process(
                def,
                vars,
                cached_view_name,
                None,
                current_array,
                fp,
                current_level,
                succ_depth,
                succ_level,
                enqueue,
            );
        }

        self.ctx.set_tlc_level(current_level);
        let _scope_guard = self.ctx.scope_guard();
        let _state_guard = self.ctx.bind_state_env_guard(current_array.env_ref());

        let mut action_def = OperatorDef {
            name: def.name.clone(),
            params: def.params.clone(),
            body: actions[0].expr.clone(),
            local: def.local,
            contains_prime: def.contains_prime,
            guards_depend_on_prime: false,
            has_primed_param: def.has_primed_param,
            is_recursive: false,
            self_call_count: 0,
        };
        let has_constraints = !self.inv_ctx.config.constraints.is_empty()
            || !self.inv_ctx.config.action_constraints.is_empty();
        let mut had_raw_successors = false;
        let mut per_action_diffs: Vec<(usize, Vec<DiffSuccessor>)> =
            Vec::with_capacity(actions.len());

        for (action_idx, action) in actions.iter().enumerate() {
            action_def.body = action.expr.clone();
            let t_enum = timing_start();
            let diffs = match enumerate_successors_array_as_diffs(
                self.ctx,
                &action_def,
                current_array,
                vars,
                None,
            ) {
                Ok(Some(diffs)) => diffs,
                Ok(None) => Vec::new(),
                Err(error) => {
                    snapshot_stop_and_send(
                        self.ctx,
                        self.stats,
                        self.stop,
                        self.result_tx,
                        |stats| WorkerResult::Error(EvalCheckError::Eval(error).into(), stats),
                    );
                    return true;
                }
            };
            accum_ns(&mut self.stats.enum_ns, t_enum);

            if !diffs.is_empty() {
                had_raw_successors = true;
            }

            if !has_constraints {
                if !diffs.is_empty() {
                    per_action_diffs.push((action_idx, diffs));
                }
                continue;
            }

            let mut valid_diffs = Vec::with_capacity(diffs.len());
            for mut diff in diffs {
                let t_mat = timing_start();
                if let Err(error) =
                    crate::materialize::materialize_diff_changes(self.ctx, &mut diff.changes, self.spec_may_produce_lazy)
                {
                    snapshot_stop_and_send(
                        self.ctx,
                        self.stats,
                        self.stop,
                        self.result_tx,
                        |stats| WorkerResult::Error(EvalCheckError::Eval(error).into(), stats),
                    );
                    return true;
                }
                let mut succ = diff.materialize(current_array, self.inv_ctx.var_registry);
                if let Err(error) = crate::materialize::materialize_array_state(self.ctx, &mut succ, self.spec_may_produce_lazy)
                {
                    snapshot_stop_and_send(
                        self.ctx,
                        self.stats,
                        self.stop,
                        self.result_tx,
                        |stats| WorkerResult::Error(EvalCheckError::Eval(error).into(), stats),
                    );
                    return true;
                }
                accum_ns(&mut self.stats.materialize_ns, t_mat);

                let t_con = timing_start();
                let passes_constraints =
                    match super::invariant_dispatch::check_successor_constraints_array(
                        self.ctx,
                        self.inv_ctx.config,
                        current_array,
                        &succ,
                        self.inv_ctx.action_constraint_analysis,
                    ) {
                        Ok(passes) => passes,
                        Err(error) => {
                            snapshot_stop_and_send(
                                self.ctx,
                                self.stats,
                                self.stop,
                                self.result_tx,
                                |stats| WorkerResult::Error(error, stats),
                            );
                            return true;
                        }
                    };
                accum_ns(&mut self.stats.constraints_ns, t_con);

                if passes_constraints {
                    valid_diffs.push(diff);
                }
            }

            if !valid_diffs.is_empty() {
                per_action_diffs.push((action_idx, valid_diffs));
            }
        }

        drop(_state_guard);
        drop(_scope_guard);

        let selected_diffs = if per_action_diffs.len() > 1 {
            let enabled_indices: Vec<usize> =
                per_action_diffs.iter().map(|(idx, _)| *idx).collect();
            let ample_result =
                crate::por::compute_ample_set(&enabled_indices, independence, visibility);

            // Part of #3706: Record POR stats on the worker.
            self.stats.por_total_states += 1;
            if ample_result.reduced {
                self.stats.por_reductions += 1;
                self.stats.por_actions_skipped +=
                    (enabled_indices.len() - ample_result.actions.len()) as u64;
                let ample_set: rustc_hash::FxHashSet<usize> =
                    ample_result.actions.into_iter().collect();
                per_action_diffs
                    .into_iter()
                    .filter(|(idx, _)| ample_set.contains(idx))
                    .flat_map(|(_, diffs)| diffs)
                    .collect()
            } else {
                per_action_diffs
                    .into_iter()
                    .flat_map(|(_, diffs)| diffs)
                    .collect()
            }
        } else {
            // Single action or zero — no POR computation needed, but still
            // count for reporting consistency.
            if !per_action_diffs.is_empty() {
                self.stats.por_total_states += 1;
            }
            per_action_diffs
                .into_iter()
                .flat_map(|(_, diffs)| diffs)
                .collect()
        };

        let ctx = &mut *self.ctx;
        let stats = &mut *self.stats;
        let local_work_delta = &mut *self.local_work_delta;
        let mut spc = SuccessorProcessCtx {
            inv_ctx: self.inv_ctx,
            stop: self.stop,
            result_tx: self.result_tx,
            stats,
            check_deadlock: self.check_deadlock,
            succ_depth,
            succ_level,
            local_work_delta,
            work_remaining: self.work_remaining,
            max_depth_atomic: self.max_depth_atomic,
            total_transitions: self.total_transitions,
            successors_cache: self.successors_cache,
            successor_witnesses_cache: self.successor_witnesses_cache,
            mvperms: self.mvperms,
            spec_may_produce_lazy: self.spec_may_produce_lazy,
        };
        let state_ctx = FullStateSuccessorCtx {
            cached_view_name,
            current_arr: current_array,
            fp,
            current_level,
        };
        process_full_state_successors(
            ctx,
            &mut spc,
            &state_ctx,
            selected_diffs,
            had_raw_successors,
            enqueue,
        )
    }

    /// Process diff-based successors with depth/level computation.
    ///
    /// Wraps [`process_diff_successors`] with `SuccessorProcessCtx` construction,
    /// using the pre-computed `succ_depth` and `succ_level` from the unified loop.
    ///
    /// Part of #2356.
    pub(super) fn process_diffs<F>(
        &mut self,
        base_array: &ArrayState,
        parent_fp: Fingerprint,
        succ_depth: usize,
        succ_level: u32,
        diffs: Vec<DiffSuccessor>,
        enqueue: F,
    ) -> bool
    where
        F: Fn(ArrayState, usize),
    {
        let ctx = &mut *self.ctx;
        let stats = &mut *self.stats;
        let local_work_delta = &mut *self.local_work_delta;
        let mut spc = SuccessorProcessCtx {
            inv_ctx: self.inv_ctx,
            stop: self.stop,
            result_tx: self.result_tx,
            stats,
            check_deadlock: self.check_deadlock,
            succ_depth,
            succ_level,
            local_work_delta,
            work_remaining: self.work_remaining,
            max_depth_atomic: self.max_depth_atomic,
            total_transitions: self.total_transitions,
            successors_cache: self.successors_cache,
            successor_witnesses_cache: self.successor_witnesses_cache,
            mvperms: self.mvperms,
            spec_may_produce_lazy: self.spec_may_produce_lazy,
        };
        process_diff_successors(ctx, &mut spc, base_array, parent_fp, diffs, enqueue)
    }

    /// Enumerate constrained successors through the sink API and process each
    /// diff inline through the shared constrained full-state reducer.
    ///
    /// Part of #3273: removes the intermediate `Vec<DiffSuccessor>` barrier
    /// for constrained full-state specs by routing emitted diffs directly from
    /// the enumerator into `process_one_full_state_diff`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn enumerate_and_process_constrained_streaming<F>(
        &mut self,
        def: &OperatorDef,
        vars: &[Arc<str>],
        tir_leaf: Option<&TirProgram<'_>>,
        current_arr: &ArrayState,
        fp: Fingerprint,
        current_level: u32,
        succ_depth: usize,
        succ_level: u32,
        enqueue: F,
    ) -> bool
    where
        F: Fn(ArrayState, usize),
    {
        let ctx = &mut *self.ctx;
        let stats = &mut *self.stats;
        let local_work_delta = &mut *self.local_work_delta;
        ctx.set_tlc_level(current_level);

        let mut spc = SuccessorProcessCtx {
            inv_ctx: self.inv_ctx,
            stop: self.stop,
            result_tx: self.result_tx,
            stats,
            check_deadlock: self.check_deadlock,
            succ_depth,
            succ_level,
            local_work_delta,
            work_remaining: self.work_remaining,
            max_depth_atomic: self.max_depth_atomic,
            total_transitions: self.total_transitions,
            successors_cache: self.successors_cache,
            successor_witnesses_cache: self.successor_witnesses_cache,
            mvperms: self.mvperms,
            spec_may_produce_lazy: self.spec_may_produce_lazy,
        };
        let mut loop_state = FullStateLoopState::new(&spc, current_arr);

        let t_enum = timing_start();
        let (enum_result, total_count, stopped, inline_processing_ns) = {
            let _scope_guard = ctx.scope_guard();
            let _state_guard = ctx.bind_state_env_guard(current_arr.env_ref());
            let mut sink = ConstrainedFullStateSink::new(
                &mut spc,
                current_arr,
                fp,
                current_level,
                &mut loop_state,
                &enqueue,
            );
            let result = enumerate_successors_array_as_diffs_into(
                ctx,
                def,
                current_arr,
                vars,
                &mut sink,
                tir_leaf,
            );
            (
                result,
                sink.count(),
                sink.is_stopped(),
                sink.inline_processing_ns(),
            )
        };
        if let Some(t) = t_enum {
            // The constrained streaming sink runs materialize/constraint/admit
            // work inline during enumeration. Subtract that nested reducer time
            // so `enum_ns` remains a partition of pure successor generation.
            spc.stats.enum_ns +=
                constrained_streaming_enum_ns(t.elapsed().as_nanos() as u64, inline_processing_ns);
        }

        match enum_result {
            Ok(()) => {
                if stopped {
                    return true;
                }

                if spc.check_deadlock_if_no_successors(ctx, current_arr, fp, total_count > 0) {
                    return true;
                }

                finish_full_state_loop(&mut spc, fp, loop_state);
                false
            }
            Err(e) => {
                // Flush any transitions accumulated by push_with_ctx before
                // the enumerator errored, so total_transitions is accurate.
                finish_full_state_loop(&mut spc, fp, loop_state);
                snapshot_stop_and_send(ctx, spc.stats, spc.stop, spc.result_tx, |stats| {
                    WorkerResult::Error(EvalCheckError::Eval(e).into(), stats)
                });
                true
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::constrained_streaming_enum_ns;

    #[test]
    fn test_constrained_streaming_enum_ns_excludes_inline_processing() {
        assert_eq!(constrained_streaming_enum_ns(17, 5), 12);
    }

    #[test]
    fn test_constrained_streaming_enum_ns_saturates_at_zero() {
        assert_eq!(constrained_streaming_enum_ns(5, 17), 0);
    }
}
