// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Diff-based successor processing for BFS iterations.
//!
//! Part of #2677 Phase 2/3: the diff (incremental fingerprinting) path
//! for successor generation and pipeline processing.
//!
//! Called from the BFS loop in `engine.rs` when `storage.use_diffs()` is true.
//! Uses shared helpers from `successor_processing.rs`.
//!
//! Part of #2963: Fused single-pass pipeline matching TLC's `Worker.addElement()`
//! pattern. Each new successor is admitted, invariant-checked, and enqueued inline
//! during the diff loop — eliminating the intermediate `new_successors` Vec and
//! enabling early termination on invariant violations.
//!
//! Part of #3027 Phase 3: Streaming path with split borrows. For the common case
//! (no implied actions, no constraints), uses `ClosureSink` to do fingerprinting
//! and dedup inline during enumeration. Only ~5% of successors (new states) are
//! collected for deferred invariant checking.

#[cfg(debug_assertions)]
use super::super::debug::debug_states;
use super::super::frontier::BfsFrontier;
use super::super::run_helpers::BfsProfile;
#[cfg(debug_assertions)]
use super::super::ArrayState;
use super::super::{compute_diff_fingerprint_with_xor, Fingerprint, ModelChecker};
use super::iter_state::BfsIterState;
use super::observer::{CompositeObserver, ExplorationSignal, SuccessorObservationCtx};
use super::storage_modes::BfsStorage;
use super::successor_processing::{BfsIterOutcome, PendingSuccessor};
use super::BfsStepParams;
#[cfg(debug_assertions)]
use crate::state::DiffSuccessor;
#[cfg(debug_assertions)]
use crate::var_index::VarRegistry;
use crate::EvalCheckError;

#[cfg(debug_assertions)]
struct BatchDiffDebugCtx<'a> {
    fp: Fingerprint,
    state_tlc_fp: Option<u64>,
    current_depth: usize,
    current_array: &'a ArrayState,
    registry: &'a VarRegistry,
    had_raw_successors: bool,
    debug_actions_this_state: bool,
}

impl ModelChecker<'_> {
    #[cfg(debug_assertions)]
    fn debug_log_batch_diff_successors(
        &mut self,
        ctx: BatchDiffDebugCtx<'_>,
        diffs: &[DiffSuccessor],
    ) {
        let succ_data: Vec<(Fingerprint, ArrayState, Option<usize>)> = diffs
            .iter()
            .map(|diff| {
                let succ_state = diff.materialize(ctx.current_array, ctx.registry);
                (diff.fingerprint, succ_state, Some(diff.num_changes()))
            })
            .collect();
        self.debug_log_bfs_successors(
            ctx.fp,
            ctx.state_tlc_fp,
            ctx.current_depth,
            ctx.current_array,
            ctx.registry,
            ctx.had_raw_successors,
            ctx.debug_actions_this_state,
            &succ_data,
        );
    }

    /// Process diff-based successors for one BFS iteration.
    ///
    /// Returns `Some(outcome)` if diffs were available and processed,
    /// or `None` if diff generation returned `Ok(None)` (caller should
    /// fall through to the full-state path).
    ///
    /// Part of #2677 Phase 2, fused in #2963.
    ///
    /// Uses a fused single-pass pipeline: each new successor is admitted,
    /// invariant-checked, and enqueued inline — eliminating the intermediate
    /// `new_successors` Vec and `run_core_step_batch` call. This matches
    /// the full-state path's pattern (Part of #2881 Step 1) and enables
    /// early termination on invariant violations.
    pub(super) fn process_diff_successors<S: BfsStorage, Q: BfsFrontier<Entry = S::QueueEntry>>(
        &mut self,
        iter_state: &mut BfsIterState,
        storage: &mut S,
        queue: &mut Q,
        params: &BfsStepParams<'_>,
        prof: &mut BfsProfile,
    ) -> Option<BfsIterOutcome> {
        let &BfsStepParams {
            registry,
            current_depth,
            succ_depth,
            current_level: _current_level,
            succ_level,
        } = params;
        // current_depth is used only in #[cfg(debug_assertions)] blocks below
        let _ = current_depth;

        // POR reduces a per-action enabled set. The diff path enumerates the
        // monolithic Next body, so fall back to the full-state path when POR is on.
        if self.por.independence.is_some() {
            return None;
        }

        // Part of #3910: When JIT is ready for all actions, skip the diff path
        // and fall through to the full-state batch path which has JIT dispatch
        // wired. This routes monolithic states through JIT-compiled native code.
        if self.jit_monolithic_ready() {
            return None;
        }

        // Part of #3968: When hybrid JIT is ready (some but not all actions
        // compiled), skip the diff path and fall through to the full-state
        // batch path which routes through per-action dispatch. This enables
        // compiled actions to use JIT while uncompiled actions use interpreter.
        if self.jit_hybrid_ready() {
            return None;
        }

        // Part of #3987: When compiled xxh3 fingerprinting is active, skip the
        // diff path. Diff fingerprinting uses `compute_diff_fingerprint_with_xor`
        // which produces FP64-compatible hashes, incompatible with xxh3. The
        // full-state path routes through `array_state_fingerprint()` which
        // dispatches to xxh3 when the flag is active, maintaining consistency.
        if self.jit_compiled_fp_active {
            return None;
        }

        // Part of #3294: TIR gate removed — streaming path now threads tir_leaf
        // through enumerate_successors_array_as_diffs_into, so TIR eval works
        // on both streaming and batch diff paths.

        // Part of #3027 Phase 3: Try streaming path for the common case.
        // Streaming uses split borrows to do fingerprint + dedup inline during
        // enumeration, collecting only new (post-dedup) diffs for deferred
        // invariant checking. Falls back to the batch path below for specs
        // with implied actions or constraints (which need ctx per-successor).
        let has_eval_implied_actions = !self.compiled.eval_implied_actions.is_empty();
        let has_constraints =
            !self.config.constraints.is_empty() || !self.config.action_constraints.is_empty();

        if !has_eval_implied_actions && !has_constraints {
            return self
                .process_diff_successors_streaming(iter_state, storage, queue, params, prof);
        }

        // Batch path: implied actions or constraints require ctx per-successor.
        let fp = iter_state.fp();

        let prof_t0 = prof.now();
        let diff_result = match self.generate_successors_as_diffs_raw(iter_state.array()) {
            Ok(Some(result)) => result,
            Ok(None) => {
                prof.accum_succ_gen(prof_t0);
                return None; // Fall through to full-state path
            }
            Err(e) => {
                prof.accum_succ_gen(prof_t0);
                return Some(BfsIterOutcome::Terminate(
                    self.bfs_error_return(iter_state, storage, e),
                ));
            }
        };
        prof.accum_succ_gen(prof_t0);
        let diffs = diff_result.successors;

        #[cfg(debug_assertions)]
        let (state_tlc_fp, need_detail_log, debug_actions_this_state) =
            self.debug_bfs_state_header(fp, iter_state.array(), current_depth, diffs.len(), "diff");

        #[cfg(debug_assertions)]
        if need_detail_log {
            self.debug_log_batch_diff_successors(
                BatchDiffDebugCtx {
                    fp,
                    state_tlc_fp,
                    current_depth,
                    current_array: iter_state.array(),
                    registry,
                    had_raw_successors: diff_result.had_raw_successors,
                    debug_actions_this_state,
                },
                &diffs,
            );
        }

        // Process diffs: materialize, fingerprint, dedup, admit, invariant, enqueue
        let mut succ_fps_for_liveness: Option<Vec<Fingerprint>> = self
            .liveness_cache
            .cache_for_liveness
            .then(|| Vec::with_capacity(diffs.len()));
        let mut candidate_observer = CompositeObserver::candidate_successors(has_constraints);
        let has_trace_inv = !self.config.trace_invariants.is_empty();
        let skip_inv = self.cooperative_invariants_proved();
        let mut admitted_observer =
            CompositeObserver::admitted_successors_maybe_skip(has_trace_inv, skip_inv);
        let mut observable_successor_count = 0usize;

        // Part of #1281: TLC level is NOT set to succ_level here.
        // The transport layer already sets current_level before calling
        // process_diff_successors. ACTION_CONSTRAINT expressions that
        // reference TLCGet("level") should see the current (parent) state's
        // level, not the successor's level. The invariant observer sets
        // succ_level internally via check_successor_invariant.
        // (The diff path never has VIEW — VIEW forces the full-state path —
        // so there is no VIEW fingerprinting concern here.)

        // ================================================================
        // Fused pass: materialize → fingerprint → constraint observers →
        // implied actions → dedup → admit → invariant observer → enqueue.
        //
        // Part of #2963: replaces the former collect-then-batch approach
        // (collect new_successors Vec → run_core_step_batch) with inline
        // processing that enables early termination on invariant violations.
        // Matches the full-state path's fused pattern (Part of #2881).
        //
        // Part of #3990: Scratch buffer optimization. Pre-allocate a single
        // scratch ArrayState and use `materialize_into` per diff instead of
        // `into_array_state_with_fp` (which clones the base Box<[CompactValue]>
        // every time). Since ~95% of successors are duplicates discarded after
        // dedup, this eliminates ~19 out of 20 Box allocations per parent state.
        // Only the ~5% that pass dedup are cloned for admission. This matches
        // the parallel worker path (successors.rs) which already uses this pattern.
        // ================================================================
        let mut scratch = super::super::ArrayState::new(iter_state.array().len());
        for mut diff in diffs {
            // Materialize lazy values before fingerprinting.
            // Returns true if any values were actually changed (lazy → concrete).
            let _materialized =
                match crate::materialize::materialize_diff_changes(&self.ctx, &mut diff.changes, self.compiled.spec_may_produce_lazy) {
                    Ok(m) => m,
                    Err(e) => {
                        return Some(BfsIterOutcome::Terminate(self.bfs_error_return(
                            iter_state,
                            storage,
                            EvalCheckError::Eval(e).into(),
                        )));
                    }
                };

            let (succ_fp, combined_xor) =
                compute_diff_fingerprint_with_xor(iter_state.array(), &diff.changes, registry);
            // Part of #3990: Materialize into scratch buffer instead of allocating.
            // Reuses the existing Box<[CompactValue]> — only N CompactValue clones, no malloc.
            diff.materialize_into(&mut scratch, iter_state.array(), succ_fp, combined_xor);

            match candidate_observer.observe_successor(
                self,
                &SuccessorObservationCtx {
                    current: iter_state.array(),
                    parent_fp: fp,
                    succ: &scratch,
                    succ_fp,
                    succ_depth,
                    succ_level,
                },
            ) {
                Ok(ExplorationSignal::Continue) => {}
                Ok(ExplorationSignal::Skip) => continue,
                Ok(ExplorationSignal::Stop(result)) => {
                    iter_state.return_to(storage, self);
                    return Some(BfsIterOutcome::Terminate(result));
                }
                Err(error) => {
                    return Some(BfsIterOutcome::Terminate(
                        self.bfs_error_return(iter_state, storage, error),
                    ));
                }
            }

            observable_successor_count += 1;
            prof.count_successors(1);
            self.record_transitions(1);

            if let Some(ref mut fps) = succ_fps_for_liveness {
                fps.push(succ_fp);
            }

            // Eval-based implied actions (#2983, #3354 Slice 4)
            // Part of #3140: Skip stuttering transitions.
            if has_eval_implied_actions && succ_fp != fp {
                let outcome = crate::checker_ops::check_eval_implied_actions_for_transition(
                    &mut self.ctx,
                    &self.compiled.eval_implied_actions,
                    iter_state.array(),
                    &scratch,
                    succ_fp,
                );
                if let Some(result) = self.handle_implied_action_outcome(
                    iter_state, storage, outcome, fp, &scratch, succ_fp, succ_depth,
                ) {
                    return Some(BfsIterOutcome::Terminate(result));
                }
            }

            // Dedup check (after implied action check, shared helper Part of #2677)
            let already_seen =
                match self.check_seen_with_profile(iter_state, storage, succ_fp, prof) {
                    Ok(seen) => seen,
                    Err(outcome) => return Some(outcome),
                };
            if already_seen {
                #[cfg(debug_assertions)]
                if debug_states() {
                    let action =
                        self.debug_action_label_for_transition_array(iter_state.array(), &scratch);
                    eprintln!("DUP STATE {succ_fp} from {fp} via {action}");
                }
                continue;
            }

            prof.count_new_state();

            // Part of #3990: Only clone for the ~5% of successors that pass dedup
            // and need heap-owned storage for admission to the seen set + queue.
            let succ = scratch.clone();
            if let Err(outcome) = self.finish_prefiltered_successor(
                iter_state,
                storage,
                queue,
                prof,
                &mut admitted_observer,
                succ,
                PendingSuccessor {
                    parent_fp: fp,
                    succ_fp,
                    succ_depth,
                    succ_level,
                },
            ) {
                return Some(outcome);
            }
        }

        let mut state_observer =
            CompositeObserver::state_completion(self.exploration.check_deadlock, false);
        if let Err(outcome) = self.run_state_completion_observers(
            iter_state,
            storage,
            &mut state_observer,
            observable_successor_count == 0,
            diff_result.had_raw_successors,
            None,
            &[],
        ) {
            return Some(outcome);
        }

        // Cache liveness fingerprints (mode-specific)
        if let Err(error) = storage.cache_diff_liveness(fp, succ_fps_for_liveness, self) {
            return Some(BfsIterOutcome::Terminate(
                self.bfs_error_return(iter_state, storage, error),
            ));
        }

        // Part of #3784: record monolithic successor count to cooperative metrics.
        self.record_cooperative_monolithic_successors(observable_successor_count);

        // Part of #3850: record monolithic action eval for tiered JIT.
        self.record_action_eval_for_tier(0, observable_successor_count as u64);

        // Part of #3910: record JIT next-state dispatch for `--show-tiers` report.
        self.record_monolithic_next_state_dispatch();

        // Return current state to storage (after all successors processed).
        iter_state.return_to(storage, self);

        Some(BfsIterOutcome::Continue)
    }
}
