// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State generation: initial state enumeration, successor generation,
//! and pilot sampling for the adaptive parallel checker.

use super::{
    bind_constants_from_config, build_ident_hints, check_error_to_result, enumerate_successors,
    precompute_constant_operators, promote_env_constants_to_precomputed, Arc, ArrayState,
    BulkInitStates, CheckError, CheckResult, ModelChecker, OperatorDef, State, SuccessorResult,
};
use crate::{ConfigCheckError, EvalCheckError};

impl<'a> ModelChecker<'a> {
    /// Generate initial states by finding all states satisfying Init
    pub(super) fn generate_initial_states(
        &mut self,
        init_name: &str,
    ) -> Result<Vec<State>, CheckError> {
        let states = self.solve_predicate_for_states(init_name)?;
        if self.tir_parity.is_some() {
            let registry = self.ctx.var_registry().clone();
            for state in &states {
                let array_state = ArrayState::from_state(state, &registry);
                self.maybe_check_tir_parity_state(init_name, &array_state)?;
            }
        }
        Ok(states)
    }

    /// Pilot helper for the adaptive checker: sample initial state count and branching factor
    /// using the same enumeration path as the sequential checker.
    ///
    /// This intentionally uses the same ArrayState diff path as the main checker so
    /// the pilot samples the current single-path successor engine.
    pub(crate) fn pilot_sample_init_and_branching_factor(
        &mut self,
        init_name: &str,
        next_name: &str,
        sample_size: usize,
    ) -> Result<(usize, f64, usize), CheckError> {
        if let Some(err) = self.module.setup_error.take() {
            return Err(err);
        }
        if self.module.vars.is_empty() {
            return Err(ConfigCheckError::NoVariables.into());
        }

        // Match the normal checker behavior (TLCGet("config") support, op replacements, etc.).
        self.sync_tlc_config("bfs");
        bind_constants_from_config(&mut self.ctx, self.config).map_err(EvalCheckError::Eval)?;
        // Part of #2955: Must match prepare_bfs_common setup — without these,
        // eval_ident's fast path skips env.get() for interned names when state_env
        // is set, causing "Undefined variable" errors for constants like N.
        precompute_constant_operators(&mut self.ctx);
        promote_env_constants_to_precomputed(&mut self.ctx);
        build_ident_hints(&mut self.ctx);

        let next_name = self.ctx.resolve_op_name(next_name).to_string();
        let next_def = self
            .module
            .op_defs
            .get(&next_name)
            .ok_or(ConfigCheckError::MissingNext)?
            .clone();

        let registry = self.ctx.var_registry().clone();

        // Prefer streaming init enumeration (BulkStateStorage) to match the default no-trace path
        // and avoid Vec<State> allocations. This keeps the pilot's Init satisfiability decision
        // consistent with the main checker.
        // Part of #1734: Propagate init generation errors instead of silently falling through
        // to the Vec<State> fallback. Ok(None) = not supported (use fallback); Err = real error.
        let bulk_result = self.generate_initial_states_to_bulk(init_name)?;
        if let Some(bulk_init) = bulk_result {
            let bulk_storage = bulk_init.storage;
            let mut scratch = ArrayState::new(registry.len());
            let num_states = u32::try_from(bulk_storage.len()).map_err(|_| {
                ConfigCheckError::Setup(format!(
                    "too many initial states ({}) for u32 BulkStateStorage index",
                    bulk_storage.len()
                ))
            })?;

            let mut num_initial = 0usize;
            let mut total_successors = 0usize;
            let mut states_sampled = 0usize;

            for idx in 0..num_states {
                scratch.overwrite_from_slice(bulk_storage.get_state(idx));
                if !self.check_state_constraints_array(&scratch)? {
                    continue;
                }
                num_initial += 1;

                if states_sampled >= sample_size {
                    continue;
                }

                let diffs = {
                    let _state_guard = self.ctx.bind_state_env_guard(scratch.env_ref());
                    let stack_mark = self.ctx.mark_stack();
                    let diffs = crate::enumerate::enumerate_successors_array_as_diffs(
                        &mut self.ctx,
                        &next_def,
                        &scratch,
                        &self.module.vars,
                        None,
                    );
                    self.ctx.pop_to_mark(&stack_mark);
                    diffs
                };

                match diffs {
                    Ok(Some(diffs)) => {
                        total_successors += diffs.len();
                        states_sampled += 1;
                    }
                    Ok(None) => {
                        // Pilot sampling is a heuristic; if the fast path requests fallback,
                        // skip this state rather than risking a hang in slower fallback paths.
                    }
                    Err(e) => {
                        // Part of #1734: Propagate enumeration errors instead of silently
                        // skipping. The main checker path propagates these fatally.
                        return Err(EvalCheckError::Eval(e).into());
                    }
                }
            }

            if num_initial == 0 {
                return Ok((0, 0.0, 0));
            }

            let avg_branching_factor = if states_sampled > 0 {
                total_successors as f64 / states_sampled as f64
            } else {
                1.0
            };

            return Ok((num_initial, avg_branching_factor, states_sampled));
        }

        // Fallback: Vec<State> enumeration (used when streaming init enumeration is not possible).
        let initial_states = self.generate_initial_states(init_name)?;
        let mut constrained_initial_states = Vec::with_capacity(initial_states.len());
        for state in initial_states {
            let arr = ArrayState::from_state(&state, &registry);
            if self.check_state_constraints_array(&arr)? {
                constrained_initial_states.push(state);
            }
        }
        let initial_states = constrained_initial_states;
        let num_initial = initial_states.len();
        if num_initial == 0 {
            return Ok((0, 0.0, 0));
        }

        let mut total_successors = 0usize;
        let mut states_sampled = 0usize;

        for state in initial_states.iter().take(sample_size) {
            let current_array = ArrayState::from_state(state, &registry);
            let diffs = {
                let _state_guard = self.ctx.bind_state_env_guard(current_array.env_ref());
                let stack_mark = self.ctx.mark_stack();
                let diffs = crate::enumerate::enumerate_successors_array_as_diffs(
                    &mut self.ctx,
                    &next_def,
                    &current_array,
                    &self.module.vars,
                    None,
                );
                self.ctx.pop_to_mark(&stack_mark);
                diffs
            };

            match diffs {
                Ok(Some(diffs)) => {
                    total_successors += diffs.len();
                    states_sampled += 1;
                }
                Ok(None) => {
                    // Pilot sampling is a heuristic; if the fast path requests fallback,
                    // skip this state rather than risking a hang in slower fallback paths.
                }
                Err(e) => {
                    // Part of #1734: Propagate enumeration errors instead of silently
                    // skipping. The main checker path propagates these fatally.
                    return Err(EvalCheckError::Eval(e).into());
                }
            }

            if states_sampled >= sample_size {
                break;
            }
        }

        let avg_branching_factor = if states_sampled > 0 {
            total_successors as f64 / states_sampled as f64
        } else {
            1.0
        };

        Ok((num_initial, avg_branching_factor, states_sampled))
    }

    /// Generate initial states directly to BulkStateStorage (memory-efficient for no-trace mode).
    ///
    /// This bypasses Vec<State> creation entirely, avoiding OrdMap allocations.
    /// Returns None if streaming enumeration is not possible (caller should fall back to Vec<State>).
    ///
    /// Used by no-trace mode to stream initial states directly to contiguous storage,
    /// with constraint and invariant checking done inline on the BulkStateStorage entries.
    pub(in crate::check) fn generate_initial_states_to_bulk(
        &mut self,
        init_name: &str,
    ) -> Result<Option<BulkInitStates>, CheckError> {
        let bulk = self.solve_predicate_for_states_to_bulk(init_name)?;
        if let Some(bulk_init) = bulk.as_ref() {
            if self.tir_parity.is_some() {
                let mut scratch = ArrayState::new(self.ctx.var_registry().len());
                let count = u32::try_from(bulk_init.storage.len()).map_err(|_| {
                    ConfigCheckError::Setup(format!(
                        "too many initial states ({}) for tir parity replay",
                        bulk_init.storage.len()
                    ))
                })?;
                for idx in 0..count {
                    scratch.overwrite_from_slice(bulk_init.storage.get_state(idx));
                    self.maybe_check_tir_parity_state(init_name, &scratch)?;
                }
            }
        }
        Ok(bulk)
    }

    /// Materialize and fingerprint an initial state that already passed init checks.
    ///
    /// Used by the prechecked streaming-init path: constraints, invariants, and
    /// property-init predicates were already evaluated during enumeration, so the
    /// admission loop only needs materialization plus fingerprint computation.
    #[allow(clippy::result_large_err)]
    pub(in crate::check) fn prepare_prechecked_initial_state(
        &mut self,
        arr: &mut ArrayState,
    ) -> Result<crate::state::Fingerprint, CheckResult> {
        if let Err(error) = crate::materialize::materialize_array_state(&self.ctx, arr, self.compiled.spec_may_produce_lazy) {
            return Err(check_error_to_result(
                EvalCheckError::Eval(error).into(),
                &self.stats,
            ));
        }

        self.array_state_fingerprint(arr)
            .map_err(|error| CheckResult::from_error(error, self.stats.clone()))
    }

    /// Generate successor states from a given state via Next relation.
    ///
    /// Binds current state variables to unprimed names, enumerates successors
    /// via the Next relation, then unconditionally restores the evaluation scope.
    pub(super) fn generate_successors(
        &mut self,
        next_name: &str,
        state: &State,
    ) -> Result<Vec<State>, CheckError> {
        // RAII guard restores env on drop (Part of #2738)
        let _scope_guard = self.ctx.scope_guard();
        for (name, value) in state.vars() {
            self.ctx.bind_mut(Arc::clone(name), value.clone());
        }
        self.solve_next_relation(next_name, state)
    }

    /// Generate successor states from a given state via Next relation, filtered by state constraints.
    ///
    /// When coverage collection is enabled, this enumerates each detected action separately so we
    /// can attribute transitions to actions.
    pub(super) fn generate_successors_filtered(
        &mut self,
        next_name: &str,
        state: &State,
    ) -> Result<SuccessorResult<Vec<State>>, CheckError> {
        // Use per-action enumeration if coverage, POR, or hybrid JIT is enabled.
        // Part of #3968: When some (but not all) actions have JIT-compiled functions,
        // route through per-action dispatch so compiled actions use JIT while
        // uncompiled actions fall back to the interpreter.
        let registry = self.ctx.var_registry().clone();
        let use_per_action = self.coverage.collect
            || self.por.independence.is_some()
            || self.jit_hybrid_ready();
        if !use_per_action || self.coverage.actions.is_empty() {
            let successors = self.generate_successors(next_name, state)?;
            let had_raw_successors = !successors.is_empty();
            let current_arr = ArrayState::from_state(state, &registry);
            let mut valid = Vec::new();
            for succ in successors {
                let succ_arr = ArrayState::from_state(&succ, &registry);
                if self.check_state_constraints_array(&succ_arr)?
                    && self.check_action_constraints_array(&current_arr, &succ_arr)?
                {
                    valid.push(succ);
                }
            }
            return Ok(SuccessorResult {
                successors: valid,
                had_raw_successors,
            });
        }

        let actions = self.coverage.actions.clone();
        let (
            template_name,
            template_params,
            template_local,
            template_contains_prime,
            template_has_primed_param,
        ) = {
            let next_def = self
                .module
                .op_defs
                .get(next_name)
                .ok_or(ConfigCheckError::MissingNext)?;
            (
                next_def.name.clone(),
                next_def.params.clone(),
                next_def.local,
                next_def.contains_prime,
                next_def.has_primed_param,
            )
        };

        // RAII guard restores env on drop, including early-return paths (Part of #2738)
        let _scope_guard = self.ctx.scope_guard();
        let mut had_any_raw_successors = false;

        // Reuse the same OperatorDef, swapping the body for each action.
        let mut action_def = OperatorDef {
            name: template_name,
            params: template_params,
            body: actions[0].expr.clone(),
            local: template_local,
            contains_prime: template_contains_prime,
            guards_depend_on_prime: false,
            has_primed_param: template_has_primed_param,
            is_recursive: false,
            self_call_count: 0,
        };

        // For POR: track successors per action so we can filter by ample set
        let por_enabled = self.por.independence.is_some();
        let mut per_action_successors: Vec<(usize, Vec<State>)> = Vec::with_capacity(actions.len());

        // Hoist ArrayState conversion outside loop: `state` is invariant across actions.
        // Part of #2484: fixes O(actions × vars) redundant work flagged in R1-1694/R1-1695.
        let current_arr = ArrayState::from_state(state, &registry);

        // Part of #3910: Flatten state once for JIT next-state dispatch.
        // Returns true if a JIT cache exists and the state was successfully
        // flattened to i64 scratch buffer. Zero cost when no JIT cache.
        // Part of #4035: Only call when JIT feature is compiled in.
        let jit_state_ready = self.prepare_jit_next_state(&current_arr);

        // Part of #4162: Track JIT eval time in the split-action coverage path
        // for the warmup gate (#4031). Without this, jit_eval_ns stays at 0
        // while interpreter time accumulates, causing premature JIT disable.
        let warmup_sampling = self.jit_perf_monitor.2 < super::run_helpers::JIT_WARMUP_THRESHOLD;
        let mut jit_eval_ns_split: u64 = 0;
        let mut any_jit_dispatched = false;

        for (action_idx, action) in actions.iter().enumerate() {
            // Part of #4118: LLVM2 native dispatch — takes priority over Cranelift
            // JIT when available. Falls through to JIT or interpreter when LLVM2
            // does not handle the action.
            #[cfg(feature = "llvm2")]
            let llvm2_handled: Option<Result<super::llvm2_dispatch::Llvm2ActionResult, ()>> =
                if self.llvm2_ready() && jit_state_ready {
                    // Part of #4270: thread `action_idx` so the dispatcher can
                    // look up specialized keys (ActionName__v0_v1) for
                    // EXISTS-bound actions when TLA2_LLVM2_EXISTS=1.
                    self.try_llvm2_action(action_idx, &action.name)
                } else {
                    None
                };

            #[cfg(feature = "llvm2")]
            if let Some(llvm2_result) = llvm2_handled {
                match llvm2_result {
                    Ok(super::llvm2_dispatch::Llvm2ActionResult::Enabled { successor, jit_input }) => {
                        had_any_raw_successors = true;
                        let succ_arr = super::invariants::unflatten_i64_to_array_state_with_input(
                            &current_arr,
                            &successor,
                            self.module.vars.len(),
                            Some(&jit_input),
                        );
                        let mut valid = Vec::new();
                        let state_ok = self.check_state_constraints_array(&succ_arr)?;
                        let action_ok =
                            self.check_action_constraints_array(&current_arr, &succ_arr)?;
                        if state_ok && action_ok {
                            valid.push(succ_arr.to_state(&registry));
                        }
                        if let Some(ref mut coverage) = self.stats.coverage {
                            coverage.record_action(action.id, valid.len());
                        }
                        self.record_cooperative_action_successors(action_idx, valid.len());
                        self.record_action_eval_for_tier(action_idx, valid.len() as u64);
                        if por_enabled && !valid.is_empty() {
                            per_action_successors.push((action_idx, valid));
                        } else if !por_enabled {
                            per_action_successors.push((action_idx, valid));
                        }
                        continue; // Skip JIT and interpreter
                    }
                    Ok(super::llvm2_dispatch::Llvm2ActionResult::Disabled) => {
                        if let Some(ref mut coverage) = self.stats.coverage {
                            coverage.record_action(action.id, 0);
                        }
                        self.record_cooperative_action_successors(action_idx, 0);
                        self.record_action_eval_for_tier(action_idx, 0);
                        if !por_enabled {
                            per_action_successors.push((action_idx, Vec::new()));
                        }
                        continue; // Skip JIT and interpreter
                    }
                    Err(()) => {
                        // LLVM2 runtime error — fall through to JIT/interpreter.
                    }
                }
            }

            // Part of #3910: JIT next-state dispatch for split actions.
            // When the action has been promoted to Tier 1+ and JIT state is
            // prepared, try the compiled native code path first. On JIT hit
            // we skip the interpreter entirely; on fallback/error we fall
            // through to the interpreter below.
            let jit_handled = if jit_state_ready {
                // Part of #4012: Skip JIT for actions individually disabled due to
                // prior runtime errors. Other actions can still use JIT.
                let action_disabled = action_idx < self.jit_disabled_actions.len()
                    && self.jit_disabled_actions[action_idx];
                if action_disabled {
                    None
                } else if let Some(ref manager) = self.tier_manager {
                    let tier = manager.current_tier(action_idx);
                    if tier >= tla_jit_abi::CompilationTier::Tier1 {
                        // Part of #4162: Time the JIT eval for warmup gate accounting.
                        let eval_t0 = if warmup_sampling {
                            Some(std::time::Instant::now())
                        } else {
                            None
                        };
                        // try_jit_action updates dispatch counters internally.
                        let result = self.try_jit_action(&action.name, &current_arr);
                        if let Some(t0) = eval_t0 {
                            jit_eval_ns_split += t0.elapsed().as_nanos() as u64;
                        }
                        if result.is_some() {
                            any_jit_dispatched = true;
                        }
                        result
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            };

            // When JIT produced a definitive result, use it directly and
            // skip the interpreter. Constraint checking still applies.
            if let Some(jit_result) = jit_handled {
                match jit_result {
                    Ok(Some(flat_succ)) => {
                        // JIT says action is enabled — materialize ArrayState
                        // for constraint checking. Deferred-unflatten optimization
                        // is only in the BFS hot path (full_state_successors.rs).
                        let succ_arr = flat_succ.to_array_state(&current_arr);
                        had_any_raw_successors = true;
                        let mut valid = Vec::new();
                        let state_ok = self.check_state_constraints_array(&succ_arr)?;
                        let action_ok =
                            self.check_action_constraints_array(&current_arr, &succ_arr)?;
                        if state_ok && action_ok {
                            valid.push(succ_arr.to_state(&registry));
                        }

                        if let Some(ref mut coverage) = self.stats.coverage {
                            coverage.record_action(action.id, valid.len());
                        }
                        self.record_cooperative_action_successors(action_idx, valid.len());
                        self.record_action_eval_for_tier(action_idx, valid.len() as u64);
                        if por_enabled && !valid.is_empty() {
                            per_action_successors.push((action_idx, valid));
                        } else if !por_enabled {
                            per_action_successors.push((action_idx, valid));
                        }
                        continue; // Skip interpreter path
                    }
                    Ok(None) => {
                        // JIT says action is disabled (guard=false). No successors.
                        if let Some(ref mut coverage) = self.stats.coverage {
                            coverage.record_action(action.id, 0);
                        }
                        self.record_cooperative_action_successors(action_idx, 0);
                        self.record_action_eval_for_tier(action_idx, 0);
                        if !por_enabled {
                            per_action_successors.push((action_idx, Vec::new()));
                        }
                        continue; // Skip interpreter path
                    }
                    Err(()) => {
                        // JIT error — fall through to interpreter below.
                    }
                }
            }

            // Interpreter path: either JIT is not available, action is below
            // Tier 1, or JIT returned a fallback/error.
            action_def.body = action.expr.clone();
            let successors =
                enumerate_successors(&mut self.ctx, &action_def, state, &self.module.vars)
                    .map_err(EvalCheckError::Eval)?;

            if !successors.is_empty() {
                had_any_raw_successors = true;
            }

            let mut valid = Vec::new();
            for succ in successors {
                let succ_arr = ArrayState::from_state(&succ, &registry);
                let state_ok = self.check_state_constraints_array(&succ_arr)?;
                let action_ok = self.check_action_constraints_array(&current_arr, &succ_arr)?;
                if state_ok && action_ok {
                    valid.push(succ);
                }
            }

            if let Some(ref mut coverage) = self.stats.coverage {
                coverage.record_action(action.id, valid.len());
            }

            // Part of #3784: per-action cooperative metrics (when fused mode is active).
            self.record_cooperative_action_successors(action_idx, valid.len());

            // Part of #3850: per-action evaluation tracking for tiered JIT promotion.
            self.record_action_eval_for_tier(action_idx, valid.len() as u64);

            // For POR, track per-action successors if action is enabled
            if por_enabled && !valid.is_empty() {
                per_action_successors.push((action_idx, valid));
            } else if !por_enabled {
                // Non-POR path: collect directly
                per_action_successors.push((action_idx, valid));
            }
        }

        // Part of #4162: Accumulate JIT eval time from this state into jit_perf_monitor.
        // Only count this state if at least one action was dispatched via JIT.
        if any_jit_dispatched && warmup_sampling {
            self.jit_perf_monitor.0 += jit_eval_ns_split;
            self.jit_perf_monitor.2 += 1;
        }

        drop(_scope_guard);

        // Compute ample set and filter successors
        let all_valid_successors = if por_enabled && per_action_successors.len() > 1 {
            // Compute ample set from enabled actions
            let enabled_indices: Vec<usize> =
                per_action_successors.iter().map(|(idx, _)| *idx).collect();

            let independence = self.por.independence.as_ref().ok_or_else(|| {
                ConfigCheckError::Setup(
                    "POR enabled but independence relation is not initialized".to_string(),
                )
            })?;
            let ample_result =
                crate::por::compute_ample_set(&enabled_indices, independence, &self.por.visibility);

            // Record POR stats
            self.por
                .stats
                .record(enabled_indices.len(), ample_result.actions.len());

            if ample_result.reduced {
                // Filter to only ample set actions
                let ample_set: rustc_hash::FxHashSet<usize> =
                    ample_result.actions.into_iter().collect();
                per_action_successors
                    .into_iter()
                    .filter(|(idx, _)| ample_set.contains(idx))
                    .flat_map(|(_, succs)| succs)
                    .collect()
            } else {
                // No reduction - collect all successors
                per_action_successors
                    .into_iter()
                    .flat_map(|(_, succs)| succs)
                    .collect()
            }
        } else {
            // Single action or POR disabled - collect all successors
            per_action_successors
                .into_iter()
                .flat_map(|(_, succs)| succs)
                .collect()
        };
        Ok(SuccessorResult {
            successors: all_valid_successors,
            had_raw_successors: had_any_raw_successors,
        })
    }

    /// Generate successor states from a `FlatState` via per-action dispatch.
    ///
    /// This is the zero-flatten/unflatten fast path for `flat_state_primary=true`
    /// specs where all state variables are scalar (Int/Bool). The flat buffer is
    /// passed directly to JIT-compiled action functions without
    /// `flatten_state_to_i64_selective`, and successors are returned as `FlatState`
    /// without `unflatten_i64_to_array_state_with_input`.
    ///
    /// For actions not in the JIT cache, falls back to:
    ///   unflatten → interpreter → flatten (the "interpreter sandwich").
    ///
    /// Part of #3986, #4183: Direct flat buffer JIT dispatch.
    pub(super) fn generate_successors_filtered_flat(
        &mut self,
        flat_state: &crate::state::FlatState,
    ) -> Result<SuccessorResult<Vec<crate::state::FlatState>>, CheckError> {
        let registry = self.ctx.var_registry().clone();
        let layout = flat_state.layout_arc().clone();

        // Part of #4214: Extract the resolved next name once at the top.
        // Previously, the no-action fallback used .unwrap_or_default() (empty string)
        // and the template builder used .unwrap_or("Next") — both incorrect.
        // cached_resolved_next_name is always set by prepare_bfs_common before
        // successor generation; if it's None, that's a setup error.
        let resolved_next_name = self
            .trace
            .cached_resolved_next_name
            .clone()
            .ok_or(ConfigCheckError::MissingNext)?;

        // We need per-action dispatch (actions must be discovered).
        if self.coverage.actions.is_empty() {
            // No actions discovered — cannot do per-action dispatch.
            // Fall back to interpreter path via ArrayState.
            let arr = flat_state.to_array_state(&registry);
            let state = arr.to_state(&registry);
            let result = self.generate_successors_filtered(
                &resolved_next_name,
                &state,
            )?;
            // Convert State successors back to FlatState.
            let flat_succs: Vec<crate::state::FlatState> = result
                .successors
                .iter()
                .map(|s| {
                    let arr = ArrayState::from_state(s, &registry);
                    crate::state::FlatState::from_array_state(&arr, Arc::clone(&layout))
                })
                .collect();
            return Ok(SuccessorResult {
                successors: flat_succs,
                had_raw_successors: result.had_raw_successors,
            });
        }

        let actions = self.coverage.actions.clone();

        // Prepare JIT scratch buffer from flat state (memcpy, not per-variable dispatch).
        let jit_state_ready = self.prepare_jit_next_state_flat(flat_state);

        // Part of #4202: POR support in flat path — mirrors interpreter path logic.
        let por_enabled = self.por.independence.is_some();

        // Part of #4196: Fast path — when the caller's flat_state_primary gate
        // guarantees no constraints, skip the per-successor ArrayState
        // conversion used solely to feed check_*_constraints_array (which would
        // early-return Ok(true) on an empty config anyway). The gate in
        // `process_full_state_successors` (bfs/full_state_successors.rs:111-117)
        // excludes has_constraints, but this function is also callable from
        // non-flat-primary dispatch, so we recompute and branch here.
        let has_any_constraints =
            !self.config.constraints.is_empty() || !self.config.action_constraints.is_empty();

        let mut had_any_raw_successors = false;
        let mut per_action_successors: Vec<(usize, Vec<crate::state::FlatState>)> =
            Vec::with_capacity(actions.len());

        // Part of #4196 Slice B: Defer `current_arr` materialization.
        //
        // `current_arr` was previously materialized unconditionally here because
        // it feeds two consumers:
        //   1. `check_action_constraints_array(&current_arr, &succ_arr)` —
        //      only reached when `has_any_constraints`.
        //   2. `current_arr.to_state(&registry)` on the interpreter-fallback
        //      branch — only reached when JIT doesn't handle an action.
        //
        // On the flat_state_primary hot path (all-scalar specs, every action
        // JIT-compiled, no constraints), neither consumer fires and the
        // per-parent `to_array_state` allocation is pure overhead. Materialize
        // lazily so fully-JIT + no-constraints parents pay zero cost.
        let mut current_arr_cache: Option<ArrayState> = None;

        // Build the action template for interpreter fallback.
        let (
            template_name,
            template_params,
            template_local,
            template_contains_prime,
            template_has_primed_param,
        ) = {
            let next_def = self
                .module
                .op_defs
                .get(&resolved_next_name)
                .ok_or(ConfigCheckError::MissingNext)?;
            (
                next_def.name.clone(),
                next_def.params.clone(),
                next_def.local,
                next_def.contains_prime,
                next_def.has_primed_param,
            )
        };

        let _scope_guard = self.ctx.scope_guard();
        let mut action_def = OperatorDef {
            name: template_name,
            params: template_params,
            body: actions[0].expr.clone(),
            local: template_local,
            contains_prime: template_contains_prime,
            guards_depend_on_prime: false,
            has_primed_param: template_has_primed_param,
            is_recursive: false,
            self_call_count: 0,
        };

        for (action_idx, action) in actions.iter().enumerate() {
            // Try JIT first when state is ready and action is promoted.
            // Part of #4176: Use try_jit_action_expanded which handles EXISTS
            // binding expansion — returns Vec<FlatState> for all enabled bindings.
            let jit_handled: Option<Result<Vec<crate::state::FlatState>, ()>> = if jit_state_ready {
                let action_disabled = action_idx < self.jit_disabled_actions.len()
                    && self.jit_disabled_actions[action_idx];
                if action_disabled {
                    None
                } else if let Some(ref manager) = self.tier_manager {
                    let tier = manager.current_tier(action_idx);
                    if tier >= tla_jit_abi::CompilationTier::Tier1 {
                        self.try_jit_action_expanded(&action.name, &layout)
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            };

            if let Some(jit_result) = jit_handled {
                match jit_result {
                    Ok(flat_succs) if !flat_succs.is_empty() => {
                        had_any_raw_successors = true;
                        // Part of #4196: Skip per-successor ArrayState
                        // conversion when no constraints are configured.
                        // check_*_constraints_array with an empty config
                        // early-returns Ok(true), so the conversion is pure
                        // allocator overhead on the flat_state_primary hot
                        // path.
                        let valid: Vec<crate::state::FlatState> = if has_any_constraints {
                            // Part of #4196 Slice B: Materialize `current_arr`
                            // lazily — only reached when constraints are
                            // configured AND the JIT expansion produced at
                            // least one successor.
                            let current_arr = current_arr_cache.get_or_insert_with(|| {
                                flat_state.to_array_state(&registry)
                            });
                            let mut v = Vec::with_capacity(flat_succs.len());
                            for flat_succ in flat_succs {
                                let succ_arr = flat_succ.to_array_state(&registry);
                                let state_ok = self.check_state_constraints_array(&succ_arr)?;
                                let action_ok = self
                                    .check_action_constraints_array(current_arr, &succ_arr)?;
                                if state_ok && action_ok {
                                    v.push(flat_succ);
                                }
                            }
                            v
                        } else {
                            flat_succs
                        };
                        if let Some(ref mut coverage) = self.stats.coverage {
                            coverage.record_action(action.id, valid.len());
                        }
                        self.record_cooperative_action_successors(action_idx, valid.len());
                        self.record_action_eval_for_tier(action_idx, valid.len() as u64);
                        // Part of #4202: POR-aware — only track enabled actions.
                        if por_enabled && !valid.is_empty() {
                            per_action_successors.push((action_idx, valid));
                        } else if !por_enabled {
                            per_action_successors.push((action_idx, valid));
                        }
                        continue;
                    }
                    Ok(_empty) => {
                        // All bindings disabled — no successors for this action.
                        if let Some(ref mut coverage) = self.stats.coverage {
                            coverage.record_action(action.id, 0);
                        }
                        self.record_cooperative_action_successors(action_idx, 0);
                        self.record_action_eval_for_tier(action_idx, 0);
                        // Part of #4202: POR-aware — disabled actions are not "enabled".
                        if !por_enabled {
                            per_action_successors.push((action_idx, Vec::new()));
                        }
                        continue;
                    }
                    Err(()) => {
                        // JIT error — fall through to interpreter.
                    }
                }
            }

            // Interpreter fallback: unflatten → eval → flatten.
            // Part of #4196 Slice B: Materialize `current_arr` lazily — this
            // branch is the fallback path, so we pay the allocation only when
            // at least one action escapes JIT dispatch. On a fully-JIT
            // all-scalar spec this branch never executes.
            let current_arr = current_arr_cache
                .get_or_insert_with(|| flat_state.to_array_state(&registry));
            action_def.body = action.expr.clone();
            let state = current_arr.to_state(&registry);
            let successors =
                enumerate_successors(&mut self.ctx, &action_def, &state, &self.module.vars)
                    .map_err(EvalCheckError::Eval)?;

            if !successors.is_empty() {
                had_any_raw_successors = true;
            }

            // Part of #4196: Skip constraint checks when none are configured.
            // FlatState::from_array_state is still required to normalize
            // interpreter-produced successors into the flat domain.
            let mut valid = Vec::with_capacity(successors.len());
            for succ in successors {
                let succ_arr = ArrayState::from_state(&succ, &registry);
                let ok = if has_any_constraints {
                    let state_ok = self.check_state_constraints_array(&succ_arr)?;
                    let action_ok =
                        self.check_action_constraints_array(current_arr, &succ_arr)?;
                    state_ok && action_ok
                } else {
                    true
                };
                if ok {
                    valid.push(crate::state::FlatState::from_array_state(
                        &succ_arr,
                        Arc::clone(&layout),
                    ));
                }
            }

            if let Some(ref mut coverage) = self.stats.coverage {
                coverage.record_action(action.id, valid.len());
            }
            self.record_cooperative_action_successors(action_idx, valid.len());
            self.record_action_eval_for_tier(action_idx, valid.len() as u64);
            // Part of #4202: POR-aware — only track enabled actions.
            if por_enabled && !valid.is_empty() {
                per_action_successors.push((action_idx, valid));
            } else if !por_enabled {
                per_action_successors.push((action_idx, valid));
            }
        }

        drop(_scope_guard);

        // Part of #4202: Apply POR (ample set) filtering to the flat path.
        // Mirrors the interpreter path's POR logic in generate_successors_filtered.
        let all_valid_flat: Vec<crate::state::FlatState> =
            if por_enabled && per_action_successors.len() > 1 {
                let enabled_indices: Vec<usize> =
                    per_action_successors.iter().map(|(idx, _)| *idx).collect();

                let independence = self.por.independence.as_ref().ok_or_else(|| {
                    ConfigCheckError::Setup(
                        "POR enabled but independence relation is not initialized".to_string(),
                    )
                })?;
                let ample_result = crate::por::compute_ample_set(
                    &enabled_indices,
                    independence,
                    &self.por.visibility,
                );

                // Record POR stats
                self.por
                    .stats
                    .record(enabled_indices.len(), ample_result.actions.len());

                if ample_result.reduced {
                    let ample_set: rustc_hash::FxHashSet<usize> =
                        ample_result.actions.into_iter().collect();
                    per_action_successors
                        .into_iter()
                        .filter(|(idx, _)| ample_set.contains(idx))
                        .flat_map(|(_, succs)| succs)
                        .collect()
                } else {
                    per_action_successors
                        .into_iter()
                        .flat_map(|(_, succs)| succs)
                        .collect()
                }
            } else {
                per_action_successors
                    .into_iter()
                    .flat_map(|(_, succs)| succs)
                    .collect()
            };

        Ok(SuccessorResult {
            successors: all_valid_flat,
            had_raw_successors: had_any_raw_successors,
        })
    }
}
