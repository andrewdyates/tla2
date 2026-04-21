// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Full-state successor processing for BFS iterations.
//!
//! Part of #2677 Phase 2/3: the full-state (explicit fingerprinting) path
//! for successor generation and pipeline processing. This is the fallback
//! path when diff-based processing is unavailable or returns `None`.
//!
//! Called from the BFS loop in `engine.rs`. Uses shared helpers from
//! `successor_processing.rs`.
//!
//! Part of #2881 Step 1: fused successor processing — materialize, fingerprint,
//! implied actions, dedup, invariant check, and enqueue happen in a single pass
//! per successor. This eliminates the intermediate `Vec<(ArrayState, Fingerprint)>`,
//! enables early termination on invariant violations, and matches TLC's
//! `Worker.addElement()` streaming pattern.

use super::super::frontier::BfsFrontier;
use super::super::run_helpers::BfsProfile;
use super::super::{ArrayState, Fingerprint, ModelChecker};
use super::iter_state::BfsIterState;
use super::observer::{CompositeObserver, ExplorationSignal, SuccessorObservationCtx};
use super::storage_modes::BfsStorage;
use super::successor_processing::{BfsIterOutcome, PendingSuccessor};
use super::BfsStepParams;
use crate::EvalCheckError;

impl ModelChecker<'_> {
    #[allow(clippy::result_large_err)]
    fn cache_full_state_batch_liveness<S: BfsStorage>(
        &mut self,
        iter_state: &mut BfsIterState,
        storage: &mut S,
        parent_fp: Fingerprint,
        liveness_data: &[(ArrayState, Fingerprint)],
    ) -> Result<(), BfsIterOutcome> {
        if let Err(error) = storage.cache_full_liveness(parent_fp, liveness_data, self) {
            return Err(BfsIterOutcome::Terminate(
                self.bfs_error_return(iter_state, storage, error),
            ));
        }
        Ok(())
    }

    /// Process full-state successors for one BFS iteration.
    ///
    /// Part of #2677 Phase 2, refactored in #2881 Step 1.
    ///
    /// Uses a fused single-pass pipeline matching TLC's `Worker.addElement()`
    /// pattern: each successor is materialized, fingerprinted, checked for
    /// implied actions, deduped, invariant-checked, and enqueued in one pass.
    /// This eliminates the intermediate `Vec<(ArrayState, Fingerprint)>` and
    /// enables early termination on invariant violations — if the first
    /// successor violates an invariant, remaining successors are not processed.
    pub(super) fn process_full_state_successors<
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
            registry: _registry,
            current_depth: _current_depth,
            succ_depth,
            current_level,
            succ_level,
        } = params;
        let fp = iter_state.fp();
        let has_eval_implied_actions = !self.compiled.eval_implied_actions.is_empty();
        let cache_for_liveness = self.liveness_cache.cache_for_liveness;
        let _next_uses_tir_eval = self.cached_next_uses_tir_eval();

        // Part of #3027: Try streaming path for the common case.
        // Streaming uses split borrows to do fingerprint + dedup inline during
        // enumeration. Falls back to the batch path below for specs with implied
        // actions, constraints, action tagging, VIEW, symmetry, or coverage
        // collection (which need ctx/state-aware fingerprinting or tagged generation).
        //
        // Part of #3294: TIR eval no longer gates streaming — tir_leaf is now
        // threaded through the streaming enumeration API.
        let has_constraints =
            !self.config.constraints.is_empty() || !self.config.action_constraints.is_empty();
        // POR currently runs through the per-action batch dispatcher, which computes
        // enabled actions and applies ample-set reduction before materialization.
        let has_por = self.por.independence.is_some();
        // Part of #3354 Slice 1: per-action tagging requires compiled split
        // actions which are being removed from the sequential checker.
        // The tagged path is disabled; monolithic enumeration is always used.
        let use_tagged = false;
        let has_coverage = self.coverage.collect && !self.coverage.actions.is_empty();
        let has_symmetry = !self.symmetry.perms.is_empty();
        let has_view = self.compiled.cached_view_name.is_some();

        // Part of #4034: Try compiled BFS step first. This performs the entire
        // BFS inner loop (action dispatch, inline fingerprinting, dedup,
        // invariant checking) in a single native Cranelift-compiled function.
        // The compiled step uses its own AtomicFpSet for first-level dedup;
        // successors still pass through the model checker's global seen set.
        //
        // This path is only available when ALL actions AND ALL invariants
        // are JIT-compiled and the state is fully flat (no compound types).
        // It bypasses implied actions, constraints, POR, coverage, symmetry,
        // and VIEW — those features require the interpreter path.
        #[cfg(feature = "jit")]
        if self.compiled_bfs_step.is_some()
            && !has_eval_implied_actions
            && !has_constraints
            && !has_por
            && !has_coverage
            && !has_symmetry
            && !has_view
        {
            if let Some(output) = self.try_compiled_bfs_step(iter_state.array()) {
                return self.process_compiled_bfs_output(
                    iter_state, storage, queue, params, prof, output,
                );
            }
        }

        // Part of #3910: When JIT is ready for all actions, skip streaming and
        // use the batch path below which has JIT dispatch wired. This ensures
        // JIT-compiled native code is used instead of the interpreter.
        //
        // Part of #4030: When JIT is ready and validation is complete, use the
        // fused path that does JIT eval + fingerprint + dedup inline — zero
        // intermediate Vec allocations for duplicate states.
        #[cfg(feature = "jit")]
        let jit_ready = self.jit_monolithic_ready();
        #[cfg(not(feature = "jit"))]
        let jit_ready = false;

        if jit_ready {
            // Part of #4030: Fused JIT dispatch path. Runs JIT actions inline
            // with fingerprint + dedup, eliminating per-action Vec clones.
            //
            // During the validation period (first N states after JIT activation),
            // we use the old two-phase path which collects successors into a Vec
            // for cross-checking against the interpreter. After validation
            // completes, the fused path is used.
            #[cfg(feature = "jit")]
            {
                if self.jit_validation_remaining == 0 {
                    // Post-validation: fused zero-allocation path.
                    return self.process_jit_fused_successors(
                        iter_state,
                        storage,
                        queue,
                        params,
                        prof,
                        has_eval_implied_actions,
                        has_constraints,
                        cache_for_liveness,
                    );
                }
                // Validation still active: use old two-phase path for cross-checking.
                let prof_t0 = prof.now();
                let jit_flat_result = self.try_jit_monolithic_successors(iter_state.array());
                if let Some(jit_flat_succs) = jit_flat_result {
                    prof.accum_succ_gen(prof_t0);
                    return self.process_jit_flat_successors(
                        iter_state,
                        storage,
                        queue,
                        params,
                        prof,
                        jit_flat_succs,
                        has_eval_implied_actions,
                        has_constraints,
                        cache_for_liveness,
                    );
                }
            }
        }

        if !jit_ready
            && !has_eval_implied_actions
            && !has_constraints
            && !has_por
            && !use_tagged
            && !has_coverage
            && !has_symmetry
            && !has_view
        {
            return self
                .process_full_state_successors_streaming(iter_state, storage, queue, params, prof);
        }

        // Batch path: specs with implied actions, constraints, action tagging,
        // coverage collection, VIEW, or symmetry, or JIT not available.

        // Interpreter path: JIT not available or returned None.
        let prof_t0 = prof.now();
        let (succ_result, succ_action_tags) =
        // Step 1: Generate all successors (batch).
        // Part of #3100: Use tagged generation when liveness provenance map is active,
        // so we can skip re-evaluating ActionPred leaves whose action tag is known.
        if use_tagged {
            match self.generate_successors_filtered_array_tagged(iter_state.array()) {
                Ok((result, tags)) => (result, tags),
                Err(e) => {
                    return BfsIterOutcome::Terminate(
                        self.bfs_error_return(iter_state, storage, e),
                    );
                }
            }
        } else {
            match self.generate_successors_array_raw(iter_state.array()) {
                Ok(result) => {
                    let tags = vec![None; result.successors.len()];
                    (result, tags)
                }
                Err(e) => {
                    return BfsIterOutcome::Terminate(
                        self.bfs_error_return(iter_state, storage, e),
                    );
                }
            }
        };
        let valid_successors = succ_result.successors;
        prof.accum_succ_gen(prof_t0);

        // Part of #4013: Check if any successor has an action tag (from JIT or
        // tagged generation). When true, collect tags for liveness provenance.
        let has_action_tags = use_tagged;

        #[cfg(debug_assertions)]
        let (state_tlc_fp, need_detail_log, debug_actions_this_state) = self
            .debug_bfs_state_header(
                fp,
                iter_state.array(),
                _current_depth,
                valid_successors.len(),
                "",
            );

        self.ctx.set_tlc_level(succ_level);

        let succ_count = valid_successors.len();
        let mut candidate_observer = CompositeObserver::candidate_successors(has_constraints);
        let has_trace_inv = !self.config.trace_invariants.is_empty();
        let skip_inv = self.cooperative_invariants_proved();
        let mut admitted_observer =
            CompositeObserver::admitted_successors_maybe_skip(has_trace_inv, skip_inv);
        let mut observable_successor_count = 0usize;

        // When liveness caching is active, collect successor data for the
        // storage-mode-specific `cache_full_liveness` method. When inactive
        // (the common performance-critical case), no allocation or cloning.
        let mut liveness_data: Vec<(ArrayState, Fingerprint)> = if cache_for_liveness {
            Vec::with_capacity(succ_count)
        } else {
            Vec::new()
        };
        // Part of #3100, #4013: Parallel vector of action tags for liveness provenance.
        // Enabled when tagged generation is used OR JIT produced action tags.
        let mut liveness_action_tags: Vec<Option<usize>> = if has_action_tags {
            Vec::with_capacity(succ_count)
        } else {
            Vec::new()
        };

        // Debug logging data (only in debug builds)
        #[cfg(debug_assertions)]
        let mut debug_succ_data: Vec<(Fingerprint, ArrayState, Option<usize>)> = if need_detail_log
        {
            Vec::with_capacity(succ_count)
        } else {
            Vec::new()
        };

        // ================================================================
        // Fused pass: materialize → fingerprint → constraint observers →
        // implied actions → dedup → invariant observer → enqueue.
        //
        // Part of #2881 Step 1: replaces the former 3-pass approach
        // (fingerprint-all → implied-actions-all → core-step-batch) with a
        // single pass that enables early termination on invariant violations.
        // ================================================================
        for (mut arr, action_tag) in valid_successors.into_iter().zip(succ_action_tags) {
            // --- Materialize lazy values ---
            if let Err(e) = crate::materialize::materialize_array_state(&self.ctx, &mut arr, self.compiled.spec_may_produce_lazy) {
                return BfsIterOutcome::Terminate(self.bfs_error_return(
                    iter_state,
                    storage,
                    EvalCheckError::Eval(e).into(),
                ));
            }

            // --- Fingerprint ---
            let prof_t_fp = prof.now();
            let succ_fp = match self.array_state_fingerprint(&mut arr) {
                Ok(fp_val) => fp_val,
                Err(e) => {
                    return BfsIterOutcome::Terminate(
                        self.bfs_error_return(iter_state, storage, e),
                    );
                }
            };
            prof.accum_fingerprint(prof_t_fp);

            // Part of #1281: ACTION_CONSTRAINT expressions reference TLCGet("level")
            // which should see the *current* (parent) state's level, not the
            // successor's level. The eval context was set to succ_level above
            // (for VIEW fingerprinting), so toggle to current_level for constraint
            // evaluation, then restore succ_level afterwards.
            if has_constraints {
                self.ctx.set_tlc_level(current_level);
            }
            match candidate_observer.observe_successor(
                self,
                &SuccessorObservationCtx {
                    current: iter_state.array(),
                    parent_fp: fp,
                    succ: &arr,
                    succ_fp,
                    succ_depth,
                    succ_level,
                },
            ) {
                Ok(ExplorationSignal::Continue) => {
                    if has_constraints {
                        self.ctx.set_tlc_level(succ_level);
                    }
                }
                Ok(ExplorationSignal::Skip) => {
                    if has_constraints {
                        self.ctx.set_tlc_level(succ_level);
                    }
                    continue;
                }
                Ok(ExplorationSignal::Stop(result)) => {
                    iter_state.return_to(storage, self);
                    return BfsIterOutcome::Terminate(result);
                }
                Err(error) => {
                    return BfsIterOutcome::Terminate(
                        self.bfs_error_return(iter_state, storage, error),
                    );
                }
            }

            observable_successor_count += 1;
            prof.count_successors(1);
            self.record_transitions(1);

            // --- Collect for liveness caching ---
            if cache_for_liveness {
                liveness_data.push((arr.clone(), succ_fp));
                if has_action_tags {
                    liveness_action_tags.push(action_tag);
                }
            }

            // --- Debug data ---
            #[cfg(debug_assertions)]
            if need_detail_log {
                debug_succ_data.push((succ_fp, arr.clone(), None));
            }

            // --- Eval-based implied actions (#2983, #3354 Slice 4) ---
            // Part of #3140: Skip stuttering transitions.
            if has_eval_implied_actions && succ_fp != fp {
                let outcome = crate::checker_ops::check_eval_implied_actions_for_transition(
                    &mut self.ctx,
                    &self.compiled.eval_implied_actions,
                    iter_state.array(),
                    &arr,
                    succ_fp,
                );
                if let Some(result) = self.handle_implied_action_outcome(
                    iter_state, storage, outcome, fp, &arr, succ_fp, succ_depth,
                ) {
                    return BfsIterOutcome::Terminate(result);
                }
            }

            // --- Inline core step: dedup → invariant → admit → enqueue ---
            // Two-phase dedup: the read-only prefilter avoids cloning most
            // duplicates, while `admit_successor` remains the authority for the
            // TOCTOU window where another worker wins the insert race.
            // Fatal invariant traces are staged on the terminal path only,
            // keeping the common case clone-free.
            let prof_t_dedup = prof.now();
            let is_seen = match self.is_state_seen_checked(succ_fp) {
                Ok(seen) => seen,
                Err(result) => {
                    iter_state.return_to(storage, self);
                    return BfsIterOutcome::Terminate(result);
                }
            };
            if is_seen {
                prof.accum_dedup(prof_t_dedup);
                continue;
            }
            prof.accum_dedup(prof_t_dedup);

            if let Err(outcome) = self.finish_prefiltered_successor(
                iter_state,
                storage,
                queue,
                prof,
                &mut admitted_observer,
                arr,
                PendingSuccessor {
                    parent_fp: fp,
                    succ_fp,
                    succ_depth,
                    succ_level,
                },
            ) {
                return outcome;
            }
        }

        // --- Post-loop: debug logging (before return_to, needs iter_state.array()) ---
        #[cfg(debug_assertions)]
        if need_detail_log {
            self.debug_log_bfs_successors(
                fp,
                state_tlc_fp,
                _current_depth,
                iter_state.array(),
                _registry,
                succ_result.had_raw_successors,
                debug_actions_this_state,
                &debug_succ_data,
            );
        }

        let liveness_tags = if has_action_tags {
            &liveness_action_tags[..]
        } else {
            &[]
        };
        let mut state_observer = CompositeObserver::state_completion(
            self.exploration.check_deadlock,
            self.inline_liveness_active(),
        );
        if let Err(outcome) = self.run_state_completion_observers(
            iter_state,
            storage,
            &mut state_observer,
            observable_successor_count == 0,
            succ_result.had_raw_successors,
            cache_for_liveness.then_some(liveness_data.as_slice()),
            liveness_tags,
        ) {
            return outcome;
        }
        if let Err(outcome) =
            self.cache_full_state_batch_liveness(iter_state, storage, fp, &liveness_data)
        {
            return outcome;
        }

        // Part of #3784: record monolithic successor count to cooperative metrics.
        self.record_cooperative_monolithic_successors(observable_successor_count);

        // Part of #3850: record monolithic action eval for tiered JIT.
        // This is the interpreter path (JIT exits via fused/two-phase above).
        self.record_action_eval_for_tier(0, observable_successor_count as u64);
        // Part of #3910: record JIT next-state dispatch for `--show-tiers` report.
        self.record_monolithic_next_state_dispatch();

        // Return parent state to storage.
        iter_state.return_to(storage, self);

        BfsIterOutcome::Continue
    }

    /// Fused JIT action dispatch + BFS dedup pipeline.
    ///
    /// Runs JIT-compiled actions inline with fingerprint and dedup checks,
    /// eliminating intermediate Vec allocations. Each action's output is
    /// fingerprinted directly from the reusable scratch buffer. Only new
    /// (non-duplicate) states are unflattened to ArrayState.
    ///
    /// This replaces the two-phase approach (try_jit_monolithic_successors
    /// collecting JitFlatSuccessors + process_jit_flat_successors iterating
    /// them), which cloned the output and input buffers for every enabled
    /// action. Since ~80-95% of successors are duplicates, the two-phase
    /// approach wasted those clones.
    ///
    /// Part of #4030: Eliminate per-action Vec clone overhead in JIT dispatch.
    #[cfg(feature = "jit")]
    #[allow(clippy::too_many_arguments)]
    fn process_jit_fused_successors<
        S: BfsStorage,
        Q: BfsFrontier<Entry = S::QueueEntry>,
    >(
        &mut self,
        iter_state: &mut BfsIterState,
        storage: &mut S,
        queue: &mut Q,
        params: &BfsStepParams<'_>,
        prof: &mut BfsProfile,
        has_eval_implied_actions: bool,
        has_constraints: bool,
        cache_for_liveness: bool,
    ) -> BfsIterOutcome {
        use super::super::invariants::{
            fingerprint_jit_flat_successor, fingerprint_jit_flat_successor_incremental,
            unflatten_i64_to_array_state_with_input,
        };
        use super::super::run_helpers::JIT_WARMUP_THRESHOLD;

        let &BfsStepParams {
            registry: _registry,
            current_depth: _current_depth,
            succ_depth,
            current_level,
            succ_level,
        } = params;
        let fp = iter_state.fp();
        let num_actions = self.jit_action_lookup_keys.len();

        // Extract state_var_count from the cache.
        let state_var_count = match self.jit_next_state_cache.as_ref() {
            Some(c) => c.state_var_count(),
            None => {
                // Should not happen — caller checked jit_monolithic_ready.
                return self
                    .process_full_state_successors_streaming(iter_state, storage, queue, params, prof);
            }
        };

        // Flatten parent state for JIT evaluation.
        if !self.prepare_jit_next_state(iter_state.array()) {
            return self
                .process_full_state_successors_streaming(iter_state, storage, queue, params, prof);
        }

        // Part of #4030: Warmup timing tracks ONLY JIT eval time (not fingerprint/dedup)
        // for fair comparison with the interpreter's successor-generation-only timing.
        let warmup_sampling = self.jit_perf_monitor.2 < JIT_WARMUP_THRESHOLD;

        // Part of #4030: Defer jit_state_scratch clone to the cold path.
        // Only 5-20% of successors are new (non-duplicate). The remaining 80-95%
        // are duplicates where the clone would be wasted. We snapshot lazily
        // only when a new state needs unflatten with compound variable support.
        // For all-scalar states, the input snapshot is never needed.
        let state_all_scalar = self.jit_state_all_scalar;
        let mut jit_input_snapshot: Option<Vec<i64>> = None;

        // Get the registry for flat fingerprinting (O(1) Arc clone).
        let registry = self.ctx.var_registry().clone();

        #[cfg(debug_assertions)]
        let (_state_tlc_fp, need_detail_log, debug_actions_this_state) = self
            .debug_bfs_state_header(
                fp,
                iter_state.array(),
                _current_depth,
                0, // count not yet known
                "[jit-fused]",
            );

        self.ctx.set_tlc_level(succ_level);

        let mut candidate_observer = CompositeObserver::candidate_successors(has_constraints);
        let has_trace_inv = !self.config.trace_invariants.is_empty();
        let skip_inv = self.cooperative_invariants_proved();
        let mut admitted_observer =
            CompositeObserver::admitted_successors_maybe_skip(has_trace_inv, skip_inv);
        let mut observable_successor_count = 0usize;
        let mut had_raw = false;
        let mut enabled_action_count = 0usize;

        let mut liveness_data: Vec<(ArrayState, Fingerprint)> = if cache_for_liveness {
            Vec::with_capacity(num_actions)
        } else {
            Vec::new()
        };
        let mut liveness_action_tags: Vec<Option<usize>> = Vec::new();

        #[cfg(debug_assertions)]
        let mut debug_succ_data: Vec<(Fingerprint, ArrayState, Option<usize>)> =
            if need_detail_log {
                Vec::with_capacity(num_actions)
            } else {
                Vec::new()
            };

        // Ensure scratch buffer is sized correctly.
        if self.jit_action_out_scratch.len() < state_var_count {
            self.jit_action_out_scratch.resize(state_var_count, 0);
        }

        // Part of #4030: Track cumulative JIT eval time separately from
        // fingerprint/dedup for fair warmup gate comparison.
        let mut jit_eval_ns: u64 = 0;

        // === Fused JIT action loop + BFS dedup pipeline ===
        // For each action: eval via JIT, fingerprint from scratch, dedup, unflatten only if new.
        for action_idx in 0..num_actions {
            // Check key validity (empty = can't be JIT-compiled).
            if self.jit_action_lookup_keys[action_idx].is_empty() {
                // Action can't be JIT-compiled — fall back to interpreter for entire state.
                // This shouldn't happen since jit_all_next_state_compiled is checked by caller,
                // but handle gracefully.
                return self.fallback_to_interpreter_path(
                    iter_state, storage, queue, params, prof,
                );
            }

            // Part of #4030: Skip compound scratch clearing for all-scalar states.
            // clear_compound_scratch() touches a thread-local (TLS access) per action.
            // For specs where all state variables are ints/bools, the compound scratch
            // is never used — skipping it saves one TLS access per action per state.
            if !state_all_scalar {
                tla_jit::abi::clear_compound_scratch();
            }

            self.next_state_dispatch.total += 1;

            // Part of #4030: Time only the JIT eval, not fingerprint/dedup.
            let eval_t0 = if warmup_sampling {
                Some(std::time::Instant::now())
            } else {
                None
            };

            // Evaluate the action via JIT into the reusable scratch buffer.
            let eval_result = {
                let cache = match self.jit_next_state_cache.as_ref() {
                    Some(c) => c,
                    None => {
                        return self.fallback_to_interpreter_path(
                            iter_state, storage, queue, params, prof,
                        );
                    }
                };
                let key = &self.jit_action_lookup_keys[action_idx];
                cache.eval_action_into(
                    key,
                    &self.jit_state_scratch,
                    &mut self.jit_action_out_scratch,
                )
            };

            // Accumulate JIT eval time (excludes fingerprint/dedup).
            if let Some(t0) = eval_t0 {
                jit_eval_ns += t0.elapsed().as_nanos() as u64;
            }

            match eval_result {
                Some(Ok(true)) => {
                    // Action enabled — successor is in jit_action_out_scratch.
                    self.next_state_dispatch.jit_hit += 1;
                    had_raw = true;
                    enabled_action_count += 1;

                    // --- Fingerprint directly from scratch buffer (no clone!) ---
                    // Part of #4030: Try incremental fingerprint first (O(changed_vars)),
                    // fall back to full scan (O(total_vars)) if parent lacks fp_cache
                    // or compound variables changed. Both return (Fingerprint, combined_xor)
                    // so admitted states can propagate combined_xor for their own successors.
                    let prof_t_fp = prof.now();
                    let (succ_fp, succ_combined_xor, mut arr_opt) =
                        match fingerprint_jit_flat_successor_incremental(
                            iter_state.array(),
                            &self.jit_action_out_scratch,
                            &self.jit_state_scratch,
                            state_var_count,
                            &registry,
                        )
                        .or_else(|| {
                            // Incremental failed (no fp_cache, compound changed, or buffer mismatch).
                            // Fall back to full O(n) scan.
                            let input_ref = jit_input_snapshot.as_deref();
                            fingerprint_jit_flat_successor(
                                iter_state.array(),
                                &self.jit_action_out_scratch,
                                state_var_count,
                                input_ref,
                                &registry,
                            )
                        }) {
                            Some((flat_fp, xor)) => (flat_fp, Some(xor), None),
                            None => {
                                // Compound variable modified — need full unflatten for fingerprint.
                                // Part of #4030: Snapshot now (first time only).
                                if jit_input_snapshot.is_none() {
                                    jit_input_snapshot = Some(self.jit_state_scratch.clone());
                                }
                                let mut arr = unflatten_i64_to_array_state_with_input(
                                    iter_state.array(),
                                    &self.jit_action_out_scratch,
                                    state_var_count,
                                    jit_input_snapshot.as_deref(),
                                );
                                if let Err(e) = crate::materialize::materialize_array_state(
                                    &self.ctx,
                                    &mut arr,
                                    self.compiled.spec_may_produce_lazy,
                                ) {
                                    return BfsIterOutcome::Terminate(self.bfs_error_return(
                                        iter_state,
                                        storage,
                                        EvalCheckError::Eval(e).into(),
                                    ));
                                }
                                let fp_val = match self.array_state_fingerprint(&mut arr) {
                                    Ok(f) => f,
                                    Err(e) => {
                                        return BfsIterOutcome::Terminate(
                                            self.bfs_error_return(iter_state, storage, e),
                                        );
                                    }
                                };
                                // combined_xor is available from the arr's fp_cache after
                                // array_state_fingerprint sets it.
                                let xor = arr.fp_cache.as_ref().map(|c| c.combined_xor);
                                (fp_val, xor, Some(arr))
                            }
                        };
                    prof.accum_fingerprint(prof_t_fp);

                    // --- Dedup check (no allocation for duplicates!) ---
                    let prof_t_dedup = prof.now();
                    let is_seen = match self.is_state_seen_checked(succ_fp) {
                        Ok(seen) => seen,
                        Err(result) => {
                            iter_state.return_to(storage, self);
                            return BfsIterOutcome::Terminate(result);
                        }
                    };
                    if is_seen {
                        prof.accum_dedup(prof_t_dedup);
                        // Hot path: duplicate state — ZERO allocation for this action.
                        continue;
                    }
                    prof.accum_dedup(prof_t_dedup);

                    // --- New state: unflatten only now (cold path) ---
                    let mut arr = match arr_opt.take() {
                        Some(a) => a,
                        None => {
                            // Scalar fast-path fingerprint succeeded but state is new.
                            // Part of #4030: Snapshot now if not yet done.
                            if jit_input_snapshot.is_none() {
                                jit_input_snapshot = Some(self.jit_state_scratch.clone());
                            }
                            let mut a = unflatten_i64_to_array_state_with_input(
                                iter_state.array(),
                                &self.jit_action_out_scratch,
                                state_var_count,
                                jit_input_snapshot.as_deref(),
                            );
                            if let Err(e) = crate::materialize::materialize_array_state(
                                &self.ctx, &mut a, self.compiled.spec_may_produce_lazy,
                            ) {
                                return BfsIterOutcome::Terminate(self.bfs_error_return(
                                    iter_state,
                                    storage,
                                    EvalCheckError::Eval(e).into(),
                                ));
                            }
                            a
                        }
                    };

                    // Part of #4030: Store combined_xor so this state can participate
                    // in incremental fingerprinting when it becomes a BFS parent.
                    if let Some(xor) = succ_combined_xor {
                        arr.set_cached_fingerprint_with_xor(succ_fp, xor);
                    } else {
                        arr.set_cached_fingerprint(succ_fp);
                    }

                    // --- Constraint observers ---
                    if has_constraints {
                        self.ctx.set_tlc_level(current_level);
                    }
                    match candidate_observer.observe_successor(
                        self,
                        &SuccessorObservationCtx {
                            current: iter_state.array(),
                            parent_fp: fp,
                            succ: &arr,
                            succ_fp,
                            succ_depth,
                            succ_level,
                        },
                    ) {
                        Ok(ExplorationSignal::Continue) => {
                            if has_constraints {
                                self.ctx.set_tlc_level(succ_level);
                            }
                        }
                        Ok(ExplorationSignal::Skip) => {
                            if has_constraints {
                                self.ctx.set_tlc_level(succ_level);
                            }
                            continue;
                        }
                        Ok(ExplorationSignal::Stop(result)) => {
                            iter_state.return_to(storage, self);
                            return BfsIterOutcome::Terminate(result);
                        }
                        Err(error) => {
                            return BfsIterOutcome::Terminate(
                                self.bfs_error_return(iter_state, storage, error),
                            );
                        }
                    }

                    observable_successor_count += 1;
                    prof.count_successors(1);
                    self.record_transitions(1);

                    // --- Collect for liveness caching ---
                    if cache_for_liveness {
                        liveness_data.push((arr.clone(), succ_fp));
                        liveness_action_tags.push(Some(action_idx));
                    }

                    // --- Debug data ---
                    #[cfg(debug_assertions)]
                    if need_detail_log {
                        debug_succ_data.push((succ_fp, arr.clone(), Some(action_idx)));
                    }

                    // --- Eval-based implied actions ---
                    if has_eval_implied_actions && succ_fp != fp {
                        let outcome =
                            crate::checker_ops::check_eval_implied_actions_for_transition(
                                &mut self.ctx,
                                &self.compiled.eval_implied_actions,
                                iter_state.array(),
                                &arr,
                                succ_fp,
                            );
                        if let Some(result) = self.handle_implied_action_outcome(
                            iter_state, storage, outcome, fp, &arr, succ_fp, succ_depth,
                        ) {
                            return BfsIterOutcome::Terminate(result);
                        }
                    }

                    // --- Invariant check + admit + enqueue ---
                    if let Err(outcome) = self.finish_prefiltered_successor(
                        iter_state,
                        storage,
                        queue,
                        prof,
                        &mut admitted_observer,
                        arr,
                        PendingSuccessor {
                            parent_fp: fp,
                            succ_fp,
                            succ_depth,
                            succ_level,
                        },
                    ) {
                        return outcome;
                    }
                }
                Some(Ok(false)) => {
                    // Action disabled (guard=false) — no successor, no allocation.
                    self.next_state_dispatch.jit_hit += 1;
                }
                Some(Err(_)) => {
                    self.next_state_dispatch.jit_error += 1;
                    self.jit_monolithic_disabled = true;
                    return self.fallback_to_interpreter_path(
                        iter_state, storage, queue, params, prof,
                    );
                }
                None => {
                    // Not compiled or FallbackNeeded — abandon fused path.
                    let has_action = self
                        .jit_next_state_cache
                        .as_ref()
                        .map_or(false, |c| {
                            c.contains_action(&self.jit_action_lookup_keys[action_idx])
                        });
                    if has_action {
                        self.next_state_dispatch.jit_fallback += 1;
                    } else {
                        self.next_state_dispatch.jit_not_compiled += 1;
                    }
                    return self.fallback_to_interpreter_path(
                        iter_state, storage, queue, params, prof,
                    );
                }
            }
        }

        // Part of #4030: Record JIT diagnostic timing.
        if self.jit_diag_enabled {
            static DIAG_COUNT: std::sync::atomic::AtomicU64 =
                std::sync::atomic::AtomicU64::new(0);
            let count = DIAG_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            if count < 10 || count % 100_000 == 0 {
                eprintln!(
                    "[jit-diag] state {}: fused dispatch, {} enabled actions, {} new states",
                    count,
                    enabled_action_count,
                    observable_successor_count,
                );
            }
        }

        // Part of #4030: Warmup gate timing — use only JIT eval time (not
        // fingerprint/dedup) for fair comparison with interpreter timing.
        // Previously, the entire fused-path elapsed time was attributed to JIT,
        // making JIT appear ~57% slower than it actually was.
        if warmup_sampling {
            self.jit_perf_monitor.0 += jit_eval_ns;
            self.jit_perf_monitor.2 += 1;
        }

        // Part of #4031: Warmup gate decision.
        if self.jit_perf_monitor.2 == JIT_WARMUP_THRESHOLD {
            self.evaluate_jit_warmup_gate();
            // If warmup gate disabled JIT, the next state will route to interpreter.
            // Current state's successors were already processed correctly above.
        }

        // --- Post-loop ---
        #[cfg(debug_assertions)]
        if need_detail_log {
            self.debug_log_bfs_successors(
                fp,
                _state_tlc_fp,
                _current_depth,
                iter_state.array(),
                _registry,
                had_raw,
                debug_actions_this_state,
                &debug_succ_data,
            );
        }

        let liveness_tags = if !liveness_action_tags.is_empty() {
            &liveness_action_tags[..]
        } else {
            &[]
        };
        let mut state_observer = CompositeObserver::state_completion(
            self.exploration.check_deadlock,
            self.inline_liveness_active(),
        );
        if let Err(outcome) = self.run_state_completion_observers(
            iter_state,
            storage,
            &mut state_observer,
            observable_successor_count == 0,
            had_raw,
            cache_for_liveness.then_some(liveness_data.as_slice()),
            liveness_tags,
        ) {
            return outcome;
        }
        if let Err(outcome) =
            self.cache_full_state_batch_liveness(iter_state, storage, fp, &liveness_data)
        {
            return outcome;
        }

        self.record_cooperative_monolithic_successors(observable_successor_count);

        iter_state.return_to(storage, self);
        BfsIterOutcome::Continue
    }

    /// Fall back to the interpreter path when JIT fused dispatch encounters an error.
    ///
    /// Part of #4030: Clean fallback from fused JIT to interpreter.
    #[cfg(feature = "jit")]
    fn fallback_to_interpreter_path<
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
        // Use the streaming interpreter path as fallback.
        self.process_full_state_successors_streaming(iter_state, storage, queue, params, prof)
    }

    /// Process JIT flat successors with deferred unflatten (legacy two-phase path).
    ///
    /// Used during the JIT validation period (first N states after JIT activation)
    /// where successor counts are cross-checked against the interpreter. After
    /// validation completes, the fused path (process_jit_fused_successors) is used
    /// instead, eliminating per-action Vec clones.
    ///
    /// Part of #4032: Eliminate per-action unflatten.
    #[cfg(feature = "jit")]
    #[allow(clippy::too_many_arguments)]
    fn process_jit_flat_successors<
        S: BfsStorage,
        Q: BfsFrontier<Entry = S::QueueEntry>,
    >(
        &mut self,
        iter_state: &mut BfsIterState,
        storage: &mut S,
        queue: &mut Q,
        params: &BfsStepParams<'_>,
        prof: &mut BfsProfile,
        flat_succs: Vec<(super::super::run_helpers::JitFlatSuccessor, Option<usize>)>,
        has_eval_implied_actions: bool,
        has_constraints: bool,
        cache_for_liveness: bool,
    ) -> BfsIterOutcome {
        let &BfsStepParams {
            registry: _registry,
            current_depth: _current_depth,
            succ_depth,
            current_level,
            succ_level,
        } = params;
        let fp = iter_state.fp();

        let has_action_tags = flat_succs.iter().any(|(_, tag)| tag.is_some());

        #[cfg(debug_assertions)]
        let (state_tlc_fp, need_detail_log, debug_actions_this_state) = self
            .debug_bfs_state_header(
                fp,
                iter_state.array(),
                _current_depth,
                flat_succs.len(),
                "[jit-flat]",
            );

        self.ctx.set_tlc_level(succ_level);

        let succ_count = flat_succs.len();
        let mut candidate_observer = CompositeObserver::candidate_successors(has_constraints);
        let has_trace_inv = !self.config.trace_invariants.is_empty();
        let skip_inv = self.cooperative_invariants_proved();
        let mut admitted_observer =
            CompositeObserver::admitted_successors_maybe_skip(has_trace_inv, skip_inv);
        let mut observable_successor_count = 0usize;

        let mut liveness_data: Vec<(ArrayState, Fingerprint)> = if cache_for_liveness {
            Vec::with_capacity(succ_count)
        } else {
            Vec::new()
        };
        let mut liveness_action_tags: Vec<Option<usize>> = if has_action_tags {
            Vec::with_capacity(succ_count)
        } else {
            Vec::new()
        };

        #[cfg(debug_assertions)]
        let mut debug_succ_data: Vec<(Fingerprint, ArrayState, Option<usize>)> =
            if need_detail_log {
                Vec::with_capacity(succ_count)
            } else {
                Vec::new()
            };

        let had_raw = !flat_succs.is_empty();

        // Get the registry for flat fingerprinting.
        let registry = self.ctx.var_registry().clone();

        for (flat_succ, action_tag) in flat_succs {
            // --- Step 1: Try flat fingerprint (no Value allocation) ---
            let prof_t_fp = prof.now();
            let (succ_fp, mut arr_opt) =
                if let Some(flat_fp) = flat_succ.try_flat_fingerprint(iter_state.array(), &registry)
                {
                    // Fast path: fingerprint computed directly from flat buffer.
                    (flat_fp, None)
                } else {
                    // Fallback: compound variable was modified, need full unflatten.
                    let mut arr = flat_succ.to_array_state(iter_state.array());
                    if let Err(e) =
                        crate::materialize::materialize_array_state(&self.ctx, &mut arr, self.compiled.spec_may_produce_lazy)
                    {
                        return BfsIterOutcome::Terminate(self.bfs_error_return(
                            iter_state,
                            storage,
                            EvalCheckError::Eval(e).into(),
                        ));
                    }
                    let fp_val = match self.array_state_fingerprint(&mut arr) {
                        Ok(f) => f,
                        Err(e) => {
                            return BfsIterOutcome::Terminate(
                                self.bfs_error_return(iter_state, storage, e),
                            );
                        }
                    };
                    (fp_val, Some(arr))
                };
            prof.accum_fingerprint(prof_t_fp);

            // --- Step 2: Dedup check (no Value allocation for duplicates) ---
            let prof_t_dedup = prof.now();
            let is_seen = match self.is_state_seen_checked(succ_fp) {
                Ok(seen) => seen,
                Err(result) => {
                    iter_state.return_to(storage, self);
                    return BfsIterOutcome::Terminate(result);
                }
            };
            if is_seen {
                prof.accum_dedup(prof_t_dedup);
                continue;
            }
            prof.accum_dedup(prof_t_dedup);

            // --- Step 3: New state — unflatten if not done already ---
            let mut arr = match arr_opt.take() {
                Some(a) => a,
                None => {
                    let mut a = flat_succ.to_array_state(iter_state.array());
                    if let Err(e) =
                        crate::materialize::materialize_array_state(&self.ctx, &mut a, self.compiled.spec_may_produce_lazy)
                    {
                        return BfsIterOutcome::Terminate(self.bfs_error_return(
                            iter_state,
                            storage,
                            EvalCheckError::Eval(e).into(),
                        ));
                    }
                    a
                }
            };

            arr.set_cached_fingerprint(succ_fp);

            // --- Constraint observers ---
            if has_constraints {
                self.ctx.set_tlc_level(current_level);
            }
            match candidate_observer.observe_successor(
                self,
                &SuccessorObservationCtx {
                    current: iter_state.array(),
                    parent_fp: fp,
                    succ: &arr,
                    succ_fp,
                    succ_depth,
                    succ_level,
                },
            ) {
                Ok(ExplorationSignal::Continue) => {
                    if has_constraints {
                        self.ctx.set_tlc_level(succ_level);
                    }
                }
                Ok(ExplorationSignal::Skip) => {
                    if has_constraints {
                        self.ctx.set_tlc_level(succ_level);
                    }
                    continue;
                }
                Ok(ExplorationSignal::Stop(result)) => {
                    iter_state.return_to(storage, self);
                    return BfsIterOutcome::Terminate(result);
                }
                Err(error) => {
                    return BfsIterOutcome::Terminate(
                        self.bfs_error_return(iter_state, storage, error),
                    );
                }
            }

            observable_successor_count += 1;
            prof.count_successors(1);
            self.record_transitions(1);

            if cache_for_liveness {
                liveness_data.push((arr.clone(), succ_fp));
                if has_action_tags {
                    liveness_action_tags.push(action_tag);
                }
            }

            #[cfg(debug_assertions)]
            if need_detail_log {
                debug_succ_data.push((succ_fp, arr.clone(), None));
            }

            if has_eval_implied_actions && succ_fp != fp {
                let outcome = crate::checker_ops::check_eval_implied_actions_for_transition(
                    &mut self.ctx,
                    &self.compiled.eval_implied_actions,
                    iter_state.array(),
                    &arr,
                    succ_fp,
                );
                if let Some(result) = self.handle_implied_action_outcome(
                    iter_state, storage, outcome, fp, &arr, succ_fp, succ_depth,
                ) {
                    return BfsIterOutcome::Terminate(result);
                }
            }

            if let Err(outcome) = self.finish_prefiltered_successor(
                iter_state,
                storage,
                queue,
                prof,
                &mut admitted_observer,
                arr,
                PendingSuccessor {
                    parent_fp: fp,
                    succ_fp,
                    succ_depth,
                    succ_level,
                },
            ) {
                return outcome;
            }
        }

        #[cfg(debug_assertions)]
        if need_detail_log {
            self.debug_log_bfs_successors(
                fp,
                state_tlc_fp,
                _current_depth,
                iter_state.array(),
                _registry,
                had_raw,
                debug_actions_this_state,
                &debug_succ_data,
            );
        }

        let liveness_tags = if has_action_tags {
            &liveness_action_tags[..]
        } else {
            &[]
        };
        let mut state_observer = CompositeObserver::state_completion(
            self.exploration.check_deadlock,
            self.inline_liveness_active(),
        );
        if let Err(outcome) = self.run_state_completion_observers(
            iter_state,
            storage,
            &mut state_observer,
            observable_successor_count == 0,
            had_raw,
            cache_for_liveness.then_some(liveness_data.as_slice()),
            liveness_tags,
        ) {
            return outcome;
        }
        if let Err(outcome) =
            self.cache_full_state_batch_liveness(iter_state, storage, fp, &liveness_data)
        {
            return outcome;
        }

        self.record_cooperative_monolithic_successors(observable_successor_count);

        iter_state.return_to(storage, self);
        BfsIterOutcome::Continue
    }

    /// Process the output of a compiled BFS step with deferred unflatten.
    ///
    /// Uses the same zero-allocation-for-duplicates pattern as the fused JIT
    /// dispatch path: flat fingerprint first (no Value allocation), dedup
    /// check, and only unflatten to ArrayState for genuinely new states.
    /// Since 80-95% of successors are duplicates, this avoids most of the
    /// ArrayState allocation overhead.
    ///
    /// The compiled step provides fast native successor generation (action
    /// dispatch + inline fingerprint + first-level dedup via AtomicFpSet);
    /// this method performs second-level dedup against the model checker's
    /// global seen set and handles invariant checking with proper trace
    /// reconstruction.
    ///
    /// Part of #3988: Compiled BFS step with deferred unflatten.
    /// Part of #4034: Wire CompiledBfsStep into model checker BFS loop.
    #[cfg(feature = "jit")]
    fn process_compiled_bfs_output<
        S: BfsStorage,
        Q: BfsFrontier<Entry = S::QueueEntry>,
    >(
        &mut self,
        iter_state: &mut BfsIterState,
        storage: &mut S,
        queue: &mut Q,
        params: &BfsStepParams<'_>,
        prof: &mut BfsProfile,
        output: tla_jit::FlatBfsStepOutput,
    ) -> BfsIterOutcome {
        use super::super::invariants::{
            fingerprint_jit_flat_successor, unflatten_i64_to_array_state_with_input,
        };

        let &BfsStepParams {
            registry: _registry,
            current_depth: _current_depth,
            succ_depth,
            current_level: _current_level,
            succ_level,
        } = params;
        let fp = iter_state.fp();
        let cache_for_liveness = self.liveness_cache.cache_for_liveness;
        let state_var_count = self
            .compiled_bfs_step
            .as_ref()
            .map_or(0, |s| s.state_len());
        let had_raw_successors = output.generated_count > 0;
        let succ_count = output.successor_count();

        prof.count_successors(succ_count);
        self.record_transitions(succ_count);

        self.ctx.set_tlc_level(succ_level);

        // Get the registry for flat fingerprinting (clone to avoid borrow conflict).
        let registry = self.ctx.var_registry().clone();

        let has_trace_inv = !self.config.trace_invariants.is_empty();
        let skip_inv = self.cooperative_invariants_proved();
        let mut admitted_observer =
            CompositeObserver::admitted_successors_maybe_skip(has_trace_inv, skip_inv);
        let mut observable_successor_count = 0usize;

        let mut liveness_data: Vec<(ArrayState, Fingerprint)> = if cache_for_liveness {
            Vec::with_capacity(succ_count)
        } else {
            Vec::new()
        };

        // Fused pass with deferred unflatten: for each flat successor from
        // the compiled step, try flat fingerprinting first (zero allocation),
        // then dedup, and only unflatten to ArrayState for new states.
        // iter_successors() yields &[i64] slices directly from the flat buffer.
        for flat_succ in output.iter_successors() {
            // --- Step 1: Try flat fingerprint (no Value allocation) ---
            let prof_t_fp = prof.now();
            let (succ_fp, mut arr_opt) = match fingerprint_jit_flat_successor(
                iter_state.array(),
                flat_succ,
                state_var_count,
                None, // No JIT input snapshot for compiled step
                &registry,
            ) {
                Some((flat_fp, _xor)) => (flat_fp, None),
                None => {
                    // Compound variable modified — need full unflatten for fingerprint.
                    let mut arr = unflatten_i64_to_array_state_with_input(
                        iter_state.array(),
                        flat_succ,
                        state_var_count,
                        None,
                    );
                    if let Err(e) =
                        crate::materialize::materialize_array_state(&self.ctx, &mut arr, self.compiled.spec_may_produce_lazy)
                    {
                        return BfsIterOutcome::Terminate(self.bfs_error_return(
                            iter_state,
                            storage,
                            crate::EvalCheckError::Eval(e).into(),
                        ));
                    }
                    let fp_val = match self.array_state_fingerprint(&mut arr) {
                        Ok(f) => f,
                        Err(e) => {
                            return BfsIterOutcome::Terminate(
                                self.bfs_error_return(iter_state, storage, e),
                            );
                        }
                    };
                    (fp_val, Some(arr))
                }
            };
            prof.accum_fingerprint(prof_t_fp);

            // --- Step 2: Dedup check (no allocation for duplicates!) ---
            let prof_t_dedup = prof.now();
            let is_seen = match self.is_state_seen_checked(succ_fp) {
                Ok(seen) => seen,
                Err(result) => {
                    iter_state.return_to(storage, self);
                    return BfsIterOutcome::Terminate(result);
                }
            };
            if is_seen {
                prof.accum_dedup(prof_t_dedup);
                // Hot path: duplicate state — ZERO allocation.
                continue;
            }
            prof.accum_dedup(prof_t_dedup);

            // --- Step 3: New state — unflatten only now (cold path) ---
            let mut arr = match arr_opt.take() {
                Some(a) => a,
                None => {
                    // Scalar fast-path fingerprint succeeded but state is new.
                    let mut a = unflatten_i64_to_array_state_with_input(
                        iter_state.array(),
                        flat_succ,
                        state_var_count,
                        None,
                    );
                    if let Err(e) =
                        crate::materialize::materialize_array_state(&self.ctx, &mut a, self.compiled.spec_may_produce_lazy)
                    {
                        return BfsIterOutcome::Terminate(self.bfs_error_return(
                            iter_state,
                            storage,
                            crate::EvalCheckError::Eval(e).into(),
                        ));
                    }
                    a
                }
            };

            arr.set_cached_fingerprint(succ_fp);
            observable_successor_count += 1;

            if cache_for_liveness {
                liveness_data.push((arr.clone(), succ_fp));
            }

            // finish_prefiltered_successor handles invariant checking,
            // trace recording, and enqueuing the successor.
            if let Err(outcome) = self.finish_prefiltered_successor(
                iter_state,
                storage,
                queue,
                prof,
                &mut admitted_observer,
                arr,
                PendingSuccessor {
                    parent_fp: fp,
                    succ_fp,
                    succ_depth,
                    succ_level,
                },
            ) {
                return outcome;
            }
        }

        let mut state_observer = CompositeObserver::state_completion(
            self.exploration.check_deadlock,
            self.inline_liveness_active(),
        );
        if let Err(outcome) = self.run_state_completion_observers(
            iter_state,
            storage,
            &mut state_observer,
            observable_successor_count == 0,
            had_raw_successors,
            cache_for_liveness.then_some(liveness_data.as_slice()),
            &[], // No action tags from compiled step
        ) {
            return outcome;
        }
        if let Err(outcome) =
            self.cache_full_state_batch_liveness(iter_state, storage, fp, &liveness_data)
        {
            return outcome;
        }

        self.record_cooperative_monolithic_successors(observable_successor_count);

        iter_state.return_to(storage, self);
        BfsIterOutcome::Continue
    }
}
