// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Streaming full-state successor processing (Part of #3027).
//!
//! Applies the Phase A/B split-borrow pattern (from `diff_successors_streaming.rs`)
//! to the full-state successor path. During Phase A, enumeration streams through
//! a `ClosureSink` that performs fingerprinting and dedup inline. Only new
//! (post-dedup) DiffSuccessors (~5% of successors) are collected for Phase B
//! processing (materialize → invariant → admit → enqueue).
//!
//! This eliminates the intermediate `Vec<ArrayState>` from
//! `generate_successors_filtered_array`, matching TLC's `Worker.addElement()`
//! streaming functor pattern.
//!
//! ## When This Path Is Used
//!
//! The full-state path is triggered when `use_diffs()` returns false:
//! - VIEW present (fingerprints use canonical form)
//! - Symmetry present (permutation-based dedup)
//! - Inline liveness active (needs full state data for liveness evaluation)
//!
//! The streaming variant handles the common subset: no implied actions,
//! no constraints, no action tagging (liveness provenance). Specs with
//! implied actions or constraints fall back to the batch path.
//!
//! ## Liveness Handling
//!
//! When `cache_for_liveness` is active, Phase A collects fingerprints for ALL
//! successors (including duplicates). For `record_inline_liveness_results`,
//! new DiffSuccessors are materialized to ArrayStates in an intermediate step
//! between phases. For duplicate successors, only fingerprints are cached
//! (sufficient for `cache_full_liveness` which extracts fps from the slice).
//!
//! When `inline_liveness_active()`, ALL successors need full ArrayStates for
//! liveness property evaluation. In this case, ALL DiffSuccessors are collected
//! during Phase A and materialized between phases. The streaming still saves
//! the intermediate `Vec<ArrayState>` from generation (one fewer allocation).

use std::ops::ControlFlow;

use super::super::frontier::BfsFrontier;
use super::super::run_helpers::BfsProfile;
use super::super::{
    compute_diff_fingerprint_with_xor, ArrayState, CheckError, Fingerprint, ModelChecker,
};
use super::iter_state::BfsIterState;
use super::observer::CompositeObserver;
use super::storage_modes::BfsStorage;
use super::successor_processing::{BfsIterOutcome, PendingSuccessor};
use super::BfsStepParams;
use crate::enumerate::{ClosureSink, DiffSink};
use crate::state::DiffSuccessor;
use crate::storage::LookupOutcome;
use crate::var_index::VarRegistry;
use crate::{ConfigCheckError, EvalCheckError};

struct StreamingFullLivenessBuffers {
    needs_all_diffs: bool,
    all_diffs_for_liveness: Vec<(DiffSuccessor, Fingerprint, Option<u64>)>,
    all_succ_fps: Vec<Fingerprint>,
}

impl ModelChecker<'_> {
    #[allow(clippy::result_large_err)]
    fn cache_streaming_full_state_liveness<S: BfsStorage>(
        &mut self,
        iter_state: &mut BfsIterState,
        storage: &mut S,
        registry: &VarRegistry,
        parent_fp: Fingerprint,
        buffers: StreamingFullLivenessBuffers,
        observer: &mut CompositeObserver,
    ) -> Result<(), BfsIterOutcome> {
        let StreamingFullLivenessBuffers {
            needs_all_diffs,
            all_diffs_for_liveness,
            all_succ_fps,
        } = buffers;

        if needs_all_diffs {
            let mut liveness_data: Vec<(ArrayState, Fingerprint)> =
                Vec::with_capacity(all_diffs_for_liveness.len());
            for (diff, succ_fp, cached_xor) in all_diffs_for_liveness {
                let mut arr = if let Some(xor) = cached_xor {
                    diff.into_array_state_with_fp(iter_state.array(), succ_fp, xor)
                } else {
                    let precomputed = if succ_fp.0 != 0 { Some(succ_fp) } else { None };
                    diff.into_array_state(iter_state.array(), registry, precomputed)
                };
                if let Err(e) = crate::materialize::materialize_array_state(
                    &self.ctx,
                    &mut arr,
                    self.compiled.spec_may_produce_lazy,
                ) {
                    return Err(BfsIterOutcome::Terminate(self.bfs_error_return(
                        iter_state,
                        storage,
                        EvalCheckError::Eval(e).into(),
                    )));
                }
                liveness_data.push((arr, succ_fp));
            }

            if let Err(outcome) = self.run_state_completion_observers(
                iter_state,
                storage,
                observer,
                liveness_data.is_empty(),
                false,
                Some(&liveness_data),
                &[],
            ) {
                return Err(outcome);
            }

            if let Err(error) = storage.cache_full_liveness(parent_fp, &liveness_data, self) {
                return Err(BfsIterOutcome::Terminate(
                    self.bfs_error_return(iter_state, storage, error),
                ));
            }
            return Ok(());
        }

        if !all_succ_fps.is_empty() {
            if let Err(error) = self
                .liveness_cache
                .successors
                .insert(parent_fp, all_succ_fps)
            {
                return Err(BfsIterOutcome::Terminate(
                    self.bfs_error_return(iter_state, storage, error),
                ));
            }
            return Ok(());
        }

        if let Err(error) = storage.cache_full_liveness(parent_fp, &[], self) {
            return Err(BfsIterOutcome::Terminate(
                self.bfs_error_return(iter_state, storage, error),
            ));
        }
        Ok(())
    }

    /// Streaming variant of full-state successor processing (Part of #3027).
    ///
    /// Uses split borrows to separate `&mut self.ctx` (for enumeration) from
    /// `&self.state_storage` (for dedup), enabling inline fingerprinting and
    /// dedup during enumeration. Only new (post-dedup) DiffSuccessors are
    /// collected for Phase B processing.
    ///
    /// Precondition: no implied actions, no constraints, no action tagging.
    /// Caller checks these before invoking.
    ///
    /// Returns `BfsIterOutcome` (always Some — unlike diff streaming, this
    /// path does not return None for fallback).
    pub(super) fn process_full_state_successors_streaming<
        S: BfsStorage,
        Q: BfsFrontier<Entry = S::QueueEntry>,
    >(
        &mut self,
        iter_state: &mut BfsIterState,
        storage: &mut S,
        queue: &mut Q,
        params: &BfsStepParams<'_>,
        prof: &mut BfsProfile,
    ) -> BfsIterOutcome {
        let &BfsStepParams {
            registry,
            current_depth: _current_depth,
            succ_depth,
            current_level: _current_level,
            succ_level,
        } = params;
        let fp = iter_state.fp();
        let current_array = iter_state.array();
        let raw_next_name = match self.trace.cached_next_name.clone() {
            Some(name) => name,
            None => {
                return BfsIterOutcome::Terminate(self.bfs_error_return(
                    iter_state,
                    storage,
                    ConfigCheckError::MissingNext.into(),
                ));
            }
        };
        let cache_for_liveness = self.liveness_cache.cache_for_liveness;
        let inline_liveness = self.inline_liveness_active();
        // Need ALL successor diffs when:
        // - inline liveness: record_inline_liveness_results needs full states
        // - symmetry + liveness: cache_full_liveness caches states for symmetry
        let needs_all_diffs =
            inline_liveness || (cache_for_liveness && !self.symmetry.perms.is_empty());

        // ================================================================
        // Phase A: Enumeration with inline dedup (split borrows)
        //
        // The borrow conflict: enumeration needs `&mut self.ctx`, but dedup
        // needs `&self.state_storage.seen_fps`. Rust allows disjoint field
        // borrows when explicit, so we extract individual fields from `self`.
        //
        // The closure does fingerprint + dedup inline during enumeration.
        // Only new states (~5% of successors) are collected for Phase B.
        // ================================================================
        let prof_t0 = prof.now();

        // Accumulators — captured by the ClosureSink closure.
        //
        // new_diffs: DiffSuccessors that passed dedup (need Phase B processing).
        // all_diffs_for_liveness: when needs_all_diffs, ALL DiffSuccessors are
        //   collected for liveness evaluation / symmetry caching (including dupes).
        // all_succ_fps: fingerprints for ALL successors (for cache_full_liveness
        //   when full states aren't collected).
        let mut new_diffs: Vec<(DiffSuccessor, Fingerprint, Option<u64>)> = Vec::new();
        let mut all_diffs_for_liveness: Vec<(DiffSuccessor, Fingerprint, Option<u64>)> = Vec::new();
        let mut all_succ_fps: Vec<Fingerprint> = Vec::new();
        let mut total_count: usize = 0;
        let mut storage_fault: Option<crate::storage::StorageFault> = None;
        let mut leaf_tir_used = false;

        // Phase A body: split borrows for enumeration + inline dedup.
        let enum_result: Result<bool, CheckError> = (|| {
            // Split borrows: extract ctx separately from other fields.
            let ctx = &mut self.ctx;
            let module = &self.module;
            let compiled = &self.compiled;
            let state_storage = &self.state_storage;
            let tir_parity = &self.tir_parity;
            let trace = &self.trace;

            let _state_guard = ctx.bind_state_env_guard(current_array.env_ref());

            // Use cached resolved name to avoid per-state resolve_op_name + String alloc.
            let resolved_next_name = trace
                .cached_resolved_next_name
                .as_deref()
                .unwrap_or_else(|| ctx.resolve_op_name(&raw_next_name));
            let def = module
                .op_defs
                .get(resolved_next_name)
                .ok_or(ConfigCheckError::MissingNext)?;

            // Part of #3294: extract TIR leaf for streaming path.
            // TirProgram borrows from tir_parity (immutable), disjoint from ctx (mutable).
            let tir_program = tir_parity.as_ref().and_then(|p| {
                p.make_tir_program_for_selected_leaf_eval_name(&raw_next_name, resolved_next_name)
            });

            let enum_registry = ctx.var_registry().clone();

            // ClosureSink: fingerprint + dedup inline, collect only new states.
            let mut sink = ClosureSink::new(|diff: DiffSuccessor| -> ControlFlow<()> {
                total_count += 1;

                // Fingerprint computation (standalone, no ctx needed).
                let (succ_fp, cached_xor) = if diff.fingerprint.0 == 0 {
                    let (fp_val, xor) = compute_diff_fingerprint_with_xor(
                        current_array,
                        &diff.changes,
                        &enum_registry,
                    );
                    (fp_val, Some(xor))
                } else {
                    (diff.fingerprint, None)
                };

                // Collect for liveness caching.
                if needs_all_diffs {
                    // Inline liveness or symmetry: need full states, collect diffs.
                    all_diffs_for_liveness.push((diff.clone(), succ_fp, cached_xor));
                } else if cache_for_liveness {
                    // Only fps needed (no symmetry, no inline liveness).
                    all_succ_fps.push(succ_fp);
                }

                // Inline dedup: check against seen fingerprint set.
                match state_storage.seen_fps.contains_checked(succ_fp) {
                    LookupOutcome::Present => return ControlFlow::Continue(()),
                    LookupOutcome::StorageFault(fault) => {
                        storage_fault = Some(fault);
                        return ControlFlow::Break(());
                    }
                    LookupOutcome::Absent => {}
                    _ => unreachable!(),
                }

                // New state (~5%) — collect for Phase B processing.
                new_diffs.push((diff, succ_fp, cached_xor));
                ControlFlow::Continue(())
            });

            // Part of #3354 Slice 1: unified-only successor generation.
            // All successor enumeration routes through the canonical AST/TIR
            // unified path. The compiled split-action dispatch is removed.
            // Part of #3923: pc-guard hoisting — pass pc_var_idx to the unified
            // enumerator so Or branches with non-matching pc guards are skipped.
            // Part of #3805: pc_var_idx is set independently of the dispatch table,
            // enabling guard hoisting for multi-process PlusCal specs.
            let pc_var_idx = compiled.pc_var_idx;
            leaf_tir_used = tir_program.is_some();
            crate::enumerate::enumerate_successors_array_as_diffs_into_with_pc_hoist(
                ctx,
                &def,
                current_array,
                &module.vars,
                &mut sink,
                tir_program.as_ref(),
                pc_var_idx,
            )
            .map_err(EvalCheckError::Eval)?;

            let had_raw = sink.count() > 0;
            Ok(had_raw)
        })();

        let had_raw_successors = match enum_result {
            Ok(had) => had,
            Err(e) => {
                prof.accum_succ_gen(prof_t0);
                return BfsIterOutcome::Terminate(self.bfs_error_return(iter_state, storage, e));
            }
        };
        prof.accum_succ_gen(prof_t0);

        if let Some(fault) = storage_fault {
            iter_state.return_to(storage, self);
            return BfsIterOutcome::Terminate(self.storage_fault_result(fault));
        }

        #[cfg(debug_assertions)]
        {
            let _ = self.debug_bfs_state_header(
                fp,
                current_array,
                _current_depth,
                total_count,
                "full-stream",
            );
        }

        let current_array_for_tir =
            (self.tir_parity.is_some() && !leaf_tir_used).then(|| current_array.clone());

        let mut state_observer =
            CompositeObserver::state_completion(self.exploration.check_deadlock, false);
        if let Err(outcome) = self.run_state_completion_observers(
            iter_state,
            storage,
            &mut state_observer,
            total_count == 0,
            had_raw_successors,
            None,
            &[],
        ) {
            return outcome;
        }

        prof.count_successors(total_count);
        self.record_transitions(total_count);

        self.ctx.set_tlc_level(succ_level);

        let mut liveness_observer = CompositeObserver::state_completion(false, inline_liveness);
        if let Err(outcome) = self.cache_streaming_full_state_liveness(
            iter_state,
            storage,
            registry,
            fp,
            StreamingFullLivenessBuffers {
                needs_all_diffs,
                all_diffs_for_liveness,
                all_succ_fps,
            },
            &mut liveness_observer,
        ) {
            return outcome;
        }

        // ================================================================
        // Phase B: Process new (post-dedup) diffs with full &mut self.
        //
        // Only the ~5% of successors that passed dedup are processed here.
        // Each needs: materialize → invariant → admit → enqueue.
        // ================================================================
        let has_trace_inv = !self.config.trace_invariants.is_empty();
        let skip_inv = self.cooperative_invariants_proved();
        let mut admitted_observer =
            CompositeObserver::admitted_successors_maybe_skip(has_trace_inv, skip_inv);
        for (mut diff, succ_fp, cached_xor) in new_diffs {
            prof.count_new_state();

            // Materialize lazy values in diff changes.
            let materialized = match crate::materialize::materialize_diff_changes(
                &self.ctx,
                &mut diff.changes,
                self.compiled.spec_may_produce_lazy,
            ) {
                Ok(m) => m,
                Err(e) => {
                    return BfsIterOutcome::Terminate(self.bfs_error_return(
                        iter_state,
                        storage,
                        EvalCheckError::Eval(e).into(),
                    ));
                }
            };

            // If materialization changed values, recompute fingerprint and
            // re-check dedup (the pre-materialization fp may now differ).
            let (final_fp, combined_xor) = if materialized {
                let (fp_val, xor) =
                    compute_diff_fingerprint_with_xor(iter_state.array(), &diff.changes, registry);
                if fp_val != succ_fp {
                    let already_seen =
                        match self.check_seen_with_profile(iter_state, storage, fp_val, prof) {
                            Ok(seen) => seen,
                            Err(outcome) => return outcome,
                        };
                    if already_seen {
                        continue;
                    }
                }
                (fp_val, xor)
            } else {
                let xor = cached_xor.unwrap_or_else(|| {
                    compute_diff_fingerprint_with_xor(iter_state.array(), &diff.changes, registry).1
                });
                (succ_fp, xor)
            };

            let succ = diff.into_array_state_with_fp(iter_state.array(), final_fp, combined_xor);

            // Part of #3352: compiled split-action success bypassed the TIR
            // replay hook on the streaming full-state path, so selected bare
            // INSTANCE wrappers never recorded Next-side TIR execution here.
            // Keep compiled-action-first enumeration, but match the batch path
            // by replaying TIR on admitted successors when leaf TIR did not run.
            if self.tir_parity.is_some() && !leaf_tir_used {
                let tir_current_array = current_array_for_tir
                    .as_ref()
                    .expect("TIR replay snapshot should exist when replay is enabled");
                match self.transition_holds_via_tir(&raw_next_name, tir_current_array, &succ) {
                    Ok(true) => {}
                    Ok(false) => continue,
                    Err(error) => {
                        return BfsIterOutcome::Terminate(
                            self.bfs_error_return(iter_state, storage, error),
                        );
                    }
                }
                if let Err(error) =
                    self.maybe_check_tir_parity_transition(&raw_next_name, tir_current_array, &succ)
                {
                    return BfsIterOutcome::Terminate(
                        self.bfs_error_return(iter_state, storage, error),
                    );
                }
            }

            if let Err(outcome) = self.finish_prefiltered_successor(
                iter_state,
                storage,
                queue,
                prof,
                &mut admitted_observer,
                succ,
                PendingSuccessor {
                    parent_fp: fp,
                    succ_fp: final_fp,
                    succ_depth,
                    succ_level,
                },
            ) {
                return outcome;
            }
        }

        // Part of #3784: record monolithic successor count to cooperative metrics.
        self.record_cooperative_monolithic_successors(total_count);

        // Part of #3850: record monolithic action eval for tiered JIT.
        self.record_action_eval_for_tier(0, total_count as u64);

        // Part of #3910: record JIT next-state dispatch for `--show-tiers` report.
        self.record_monolithic_next_state_dispatch();

        // Return current state to storage.
        iter_state.return_to(storage, self);

        BfsIterOutcome::Continue
    }
}
