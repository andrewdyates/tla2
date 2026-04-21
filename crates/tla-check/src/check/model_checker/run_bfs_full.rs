// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Full-state BFS mode: initial state generation and BFS exploration loop.
//!
//! This module handles the `store_full_states` path where `ArrayState` objects
//! are kept in a `HashMap` for trace reconstruction.

use super::bfs::FullStateStorage;
#[cfg(debug_assertions)]
use super::debug::debug_states;
use super::{
    check_error_to_result, ArrayState, CheckResult, Fingerprint, ModelChecker, State, Trace,
    VecDeque,
};
use crate::{ConfigCheckError, EvalCheckError};

impl ModelChecker<'_> {
    /// Generate initial states, then apply state constraints (CONSTRAINT directive).
    ///
    /// Part of #2133 (phase 2): shared fallback helper used by both full-state
    /// and no-trace initialization paths to avoid duplicated filtering logic.
    #[allow(clippy::result_large_err)]
    pub(in crate::check) fn constrained_initial_states(
        &mut self,
        init_name: &str,
    ) -> Result<Vec<State>, CheckResult> {
        let initial_states = self
            .generate_initial_states(init_name)
            .map_err(|error| check_error_to_result(error, &self.stats))?;

        let registry = self.ctx.var_registry().clone();
        let mut constrained_initial_states = Vec::with_capacity(initial_states.len());
        for state in initial_states {
            let arr = ArrayState::from_state(&state, &registry);
            match self.check_state_constraints_array(&arr) {
                Ok(true) => constrained_initial_states.push(state),
                Ok(false) => {}
                Err(error) => {
                    return Err(check_error_to_result(error, &self.stats));
                }
            }
        }

        Ok(constrained_initial_states)
    }

    /// Process a single initial state through all pre-admission checks.
    ///
    /// Part of #2473: shared helper used by both full-state and no-trace init paths
    /// to eliminate duplicated constraint/materialize/fingerprint/invariant logic.
    ///
    /// Performs (in order): state constraint checking (if `check_constraints`), lazy
    /// value materialization, fingerprinting, deduplication, and invariant checking.
    ///
    /// Returns:
    /// - `Ok(None)` — state pruned by constraints or duplicate fingerprint
    /// - `Ok(Some((fp, violation)))` — state should be admitted; `violation` is `Some`
    ///   if an invariant was violated (continue-on-error mode)
    /// - `Err(CheckResult)` — fatal error (eval error, storage fault)
    #[allow(clippy::result_large_err)]
    pub(in crate::check) fn check_init_state(
        &mut self,
        arr: &mut ArrayState,
        check_constraints: bool,
    ) -> Result<Option<(Fingerprint, Option<String>)>, CheckResult> {
        // Check state constraints (CONSTRAINT directive) if not already filtered
        if check_constraints {
            match self.check_state_constraints_array(arr) {
                Ok(true) => {}
                Ok(false) => return Ok(None),
                Err(e) => {
                    return Err(check_error_to_result(e, &self.stats));
                }
            }
        }

        // Part of #2018: Materialize lazy values before fingerprinting.
        // Part of #2356/#2777: Route through check_error_to_result so
        // ExitRequested maps to LimitReached(Exit).
        if let Err(e) = crate::materialize::materialize_array_state(&self.ctx, arr, self.compiled.spec_may_produce_lazy) {
            return Err(check_error_to_result(
                EvalCheckError::Eval(e).into(),
                &self.stats,
            ));
        }

        // Compute fingerprint for deduplication.
        //
        // Part of #2708: the dedup check that was here (`is_state_seen_checked`)
        // created a TOCTOU gap — the caller performs the actual atomic
        // `mark_state_seen_*` insertion, so a separate contains_checked is
        // redundant for sequential mode and racy for parallel mode. The caller
        // now uses the InsertOutcome from `mark_state_seen_*` to decide whether
        // to enqueue, matching TLC's FPSet.put() single-operation pattern.
        let fp = self
            .array_state_fingerprint(arr)
            .map_err(|e| CheckResult::from_error(e, self.stats.clone()))?;

        // Check invariants
        // Part of #1117: Set trace context for TLCExt Trace support
        self.set_trace_context_for_init_array(arr);
        let violation = match self.check_invariants_array(arr) {
            Ok(v) => {
                self.clear_trace_context();
                v
            }
            Err(e) => {
                self.clear_trace_context();
                return Err(check_error_to_result(e, &self.stats));
            }
        };
        if violation.is_some() {
            return Ok(Some((fp, violation)));
        }

        // Check property init predicates (#2834): non-Always state-level terms
        // from PROPERTY entries (e.g., M!Init in "M!Init /\ [][M!Next]_M!vars").
        let init_pred_violation = match crate::checker_ops::check_property_init_predicates(
            &mut self.ctx,
            &self.compiled.property_init_predicates,
            arr,
        ) {
            Ok(v) => v,
            Err(e) => return Err(check_error_to_result(e, &self.stats)),
        };

        Ok(Some((fp, init_pred_violation)))
    }

    /// Handle an invariant violation during init-state processing.
    ///
    /// Part of #2473: shared helper for violation recording/trace-construction.
    /// The `make_trace_state` closure lazily constructs the State for the error
    /// trace, avoiding allocation in the continue-on-error case.
    ///
    /// Returns `Ok(())` if continue_on_error absorbed the violation, or
    /// `Err(CheckResult)` (InvariantViolation or PropertyViolation) if the checker should stop.
    #[allow(clippy::result_large_err)]
    pub(in crate::check) fn handle_init_violation(
        &mut self,
        violation: String,
        fp: Fingerprint,
        make_trace_state: impl FnOnce() -> State,
    ) -> Result<(), CheckResult> {
        if self.record_invariant_violation(violation.clone(), fp) {
            let trace = Trace::from_states(vec![make_trace_state()]);
            // Part of #2676: check if this invariant was promoted from a PROPERTY entry.
            return Err(
                if self
                    .compiled
                    .promoted_property_invariants
                    .contains(&violation)
                {
                    CheckResult::PropertyViolation {
                        property: violation,
                        kind: crate::check::api::PropertyViolationKind::StateLevel,
                        trace,
                        stats: self.stats.clone(),
                    }
                } else {
                    CheckResult::InvariantViolation {
                        invariant: violation,
                        trace,
                        stats: self.stats.clone(),
                    }
                },
            );
        }
        Ok(())
    }

    /// Generate initial states for full-state BFS mode.
    ///
    /// Tries streaming enumeration first (avoids Vec<State> OrdMap overhead),
    /// then falls back to the Vec<State> path. Returns the initial BFS queue
    /// or an early CheckResult on error/violation.
    #[allow(clippy::result_large_err)]
    pub(in crate::check) fn init_states_full_state(
        &mut self,
        init_name: &str,
        registry: &crate::var_index::VarRegistry,
    ) -> Result<VecDeque<(Fingerprint, usize)>, CheckResult> {
        // Part of #3305: streaming invariant scan — O(1) memory per state.
        // For specs like Einstein (~199M init states), this finds invariant
        // violations without materializing the full state space into BulkStateStorage.
        self.scan_init_invariants_streaming(init_name)?;

        let mut queue: VecDeque<(Fingerprint, usize)> = VecDeque::new();
        let mut init_generated: usize = 0;
        let used_streaming = if let Some(bulk_init) =
            self.solve_predicate_for_states_to_bulk_prechecked(init_name)?
        {
            let init_generated_count = bulk_init.enumeration.generated;
            let bulk_storage = bulk_init.storage;
            let mut scratch = ArrayState::new(registry.len());
            let num_states = u32::try_from(bulk_storage.len()).map_err(|_| {
                CheckResult::from_error(
                    ConfigCheckError::Setup(format!(
                        "too many initial states ({}) for u32 BulkStateStorage index",
                        bulk_storage.len()
                    ))
                    .into(),
                    self.stats.clone(),
                )
            })?;

            for idx in 0..num_states {
                scratch.overwrite_from_slice(bulk_storage.get_state(idx));
                let fp = self.prepare_prechecked_initial_state(&mut scratch)?;

                #[cfg(debug_assertions)]
                if debug_states() {
                    let state = scratch.to_state(registry);
                    eprintln!("INIT STATE {fp} via Init: {state:?}");
                }

                #[cfg(feature = "memory-stats")]
                {
                    crate::value::memory_stats::inc_array_state();
                    crate::value::memory_stats::inc_array_state_bytes(scratch.len());
                }
                let mut arr = scratch.clone();
                if self.compiled.cached_view_name.is_none() && self.symmetry.perms.is_empty() {
                    let _ = arr.fingerprint(registry);
                }

                let liveness_arr = if self.track_liveness_init_states() {
                    Some(arr.clone())
                } else {
                    None
                };
                if !self.mark_state_seen_owned_checked(fp, arr, None, 0)? {
                    debug_eprintln!(debug_states(), "DUP INIT STATE {}", fp);
                    continue;
                }
                if let Some(liveness_arr) = liveness_arr {
                    self.liveness_cache.init_states.push((fp, liveness_arr));
                }
                queue.push_back((fp, 0));
            }

            init_generated = init_generated_count;
            self.stats.initial_states = queue.len();
            true
        } else {
            let streaming_result = self.generate_initial_states_to_bulk(init_name);
            // Part of #1433: Propagate actual eval errors instead of silently falling back.
            // Ok(None) = streaming not available (fall back to Vec<State> path).
            // Err(e)   = real eval error (propagate immediately).
            match streaming_result {
                Err(e) => {
                    return Err(check_error_to_result(e, &self.stats));
                }
                Ok(None) => false,
                Ok(Some(bulk_init)) => {
                    let init_generated_count = bulk_init.enumeration.generated;
                    let bulk_storage = bulk_init.storage;
                    // Streaming successful! Process states from BulkStateStorage directly.
                    // Filter by constraints and add to seen.
                    let mut scratch = ArrayState::new(registry.len());
                    let num_states = u32::try_from(bulk_storage.len()).map_err(|_| {
                        CheckResult::from_error(
                            ConfigCheckError::Setup(format!(
                                "too many initial states ({}) for u32 BulkStateStorage index",
                                bulk_storage.len()
                            ))
                            .into(),
                            self.stats.clone(),
                        )
                    })?;

                    // Part of #254: Set TLC level for TLCGet("level") - TLC uses 1-based indexing
                    // Initial states are at level 1 in TLC
                    self.ctx.set_tlc_level(1);

                    // Filter by constraints, check invariants, and store states
                    for idx in 0..num_states {
                        scratch.overwrite_from_slice(bulk_storage.get_state(idx));

                        // Part of #2473: Use shared check_init_state helper
                        let (fp, violation) = match self.check_init_state(&mut scratch, true)? {
                            Some(result) => result,
                            None => continue,
                        };

                        #[cfg(debug_assertions)]
                        if debug_states() {
                            let state = scratch.to_state(registry);
                            eprintln!("INIT STATE {fp} via Init: {state:?}");
                        }

                        // Create ArrayState for storage (clone from scratch)
                        #[cfg(feature = "memory-stats")]
                        {
                            crate::value::memory_stats::inc_array_state();
                            crate::value::memory_stats::inc_array_state_bytes(scratch.len());
                        }
                        let mut arr = scratch.clone();
                        if self.compiled.cached_view_name.is_none()
                            && self.symmetry.perms.is_empty()
                        {
                            let _ = arr.fingerprint(registry);
                        }

                        // Part of #2708: clone for liveness cache BEFORE the
                        // move into mark_state_seen, push only after dedup succeeds.
                        let liveness_arr = if self.track_liveness_init_states() {
                            Some(arr.clone())
                        } else {
                            None
                        };
                        // Part of #2708: atomic test-and-set replaces the old two-step
                        // is_state_seen_checked + mark_state_seen pattern. The return
                        // value is the dedup authority — skip if already present.
                        if !self.mark_state_seen_owned_checked(fp, arr, None, 0)? {
                            debug_eprintln!(debug_states(), "DUP INIT STATE {}", fp);
                            continue;
                        }
                        // Part of #3175: cache init states for post-BFS liveness
                        if let Some(liveness_arr) = liveness_arr {
                            self.liveness_cache.init_states.push((fp, liveness_arr));
                        }
                        if let Some(violation) = violation {
                            self.handle_init_violation(violation, fp, || {
                                scratch.to_state(registry)
                            })?;
                        }
                        // Initial states are at depth 0.
                        queue.push_back((fp, 0));
                    }

                    init_generated = init_generated_count;
                    self.stats.initial_states = queue.len();
                    true
                }
            }
        };

        // Fall back to Vec<State> path if streaming not available
        if !used_streaming {
            let initial_states = self.constrained_initial_states(init_name)?;

            // Part of #2163: capture pre-dedup count for states_generated reporting
            init_generated = initial_states.len();

            // Part of #254: Set TLC level for TLCGet("level") - TLC uses 1-based indexing
            // Initial states are at level 1 in TLC
            self.ctx.set_tlc_level(1);

            // Check initial states and mark as seen in a single pass.
            // Part of #595: Handle continue_on_error for initial states.
            for state in &initial_states {
                // Part of #158: Use from_state (NOT from_state_with_fp) so fingerprint
                // is computed fresh using registry order. from_state_with_fp copies
                // State's alphabetical-order fingerprint, causing mismatch.
                let mut arr = ArrayState::from_state(state, registry);

                // Part of #2473: Use shared check_init_state helper
                // check_constraints=false: already filtered by constrained_initial_states
                let (fp, violation) = match self.check_init_state(&mut arr, false)? {
                    Some(result) => result,
                    None => continue,
                };

                // Part of #2708: clone for liveness BEFORE the move, push
                // only after dedup succeeds (prevents duplicate cache entries).
                let liveness_arr = if self.track_liveness_init_states() {
                    Some(arr.clone())
                } else {
                    None
                };
                // Part of #2708: atomic test-and-set — skip if already present.
                if !self.mark_state_seen_owned_checked(fp, arr, None, 0)? {
                    debug_eprintln!(debug_states(), "DUP INIT STATE {}", fp);
                    continue;
                }
                // Part of #3175: cache init states for post-BFS liveness
                if let Some(liveness_arr) = liveness_arr {
                    self.liveness_cache.init_states.push((fp, liveness_arr));
                }
                if let Some(violation) = violation {
                    self.handle_init_violation(violation, fp, || state.clone())?;
                } else {
                    debug_eprintln!(debug_states(), "INIT STATE {} via Init: {:?}", fp, state);
                }
                // Initial states are at depth 0.
                queue.push_back((fp, 0));
            }

            // Part of #2163: set initial_states to post-dedup count, consistent
            // with the streaming path (was initial_states.len() — pre-dedup).
            self.stats.initial_states = queue.len();

            // Explicitly drop Vec<State> to release OrdMap memory
            drop(initial_states);
        }

        // Initialize states_found with initial states count
        self.stats.states_found = self.states_count();
        // Part of #2163: report both pre-dedup generated count and post-dedup distinct count
        self.report_init_progress(init_generated, self.stats.states_found);
        Ok(queue)
    }

    /// Run the full-state BFS loop using the unified `run_bfs_loop` implementation.
    ///
    /// Part of #2133: Delegates to `run_bfs_loop<FullStateStorage>` instead of
    /// maintaining a separate copy of the BFS loop body.
    pub(in crate::check) fn check_impl_full_state_mode(&mut self, init_name: &str) -> CheckResult {
        let registry = self.ctx.var_registry().clone();
        self.initialize_checkpoint_timing();
        self.prepare_inline_liveness_cache();

        // Part of #1801: route init-state violations through finalize_terminal_result
        // so storage-error precedence applies even to early invariant violations.
        let mut queue = match self.init_states_full_state(init_name, &registry) {
            Ok(q) => q,
            Err(result) => return self.finalize_terminal_result_with_storage(result),
        };

        // Part of #3986: Infer flat i64 state layout from first initial state.
        // This must run before the JIT layout upgrade since the JIT may use the
        // flat layout for FlatState conversions in the dispatch path.
        if let Some(first_init) = self.liveness_cache.init_states.first().map(|(_, a)| a.clone())
            .or_else(|| self.state_storage.seen.values().next().cloned())
        {
            self.infer_flat_state_layout(&first_init);
        }

        // Part of #3910: Upgrade JIT invariant cache with compound layout info
        // inferred from the first initial state. This enables native record/function
        // access in JIT-compiled invariants instead of falling back to the interpreter.
        #[cfg(feature = "jit")]
        if let Some(first_init) = self.get_first_init_state_for_layout() {
            self.upgrade_jit_cache_with_layout(&first_init);
            // Part of #3986: Verify that the flat BFS layout and JIT layout agree
            // on buffer format. Log warning if incompatible.
            self.verify_layout_compatibility();
        }

        let mut storage = FullStateStorage;
        self.run_bfs_loop(&mut storage, &mut queue)
    }
}
