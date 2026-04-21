// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
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
        // Use per-action enumeration if coverage OR POR is enabled
        let registry = self.ctx.var_registry().clone();
        let use_per_action = self.coverage.collect || self.por.independence.is_some();
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
        #[cfg(feature = "jit")]
        let jit_state_ready = self.prepare_jit_next_state(&current_arr);

        for (action_idx, action) in actions.iter().enumerate() {
            // Part of #3910: JIT next-state dispatch for split actions.
            // When the action has been promoted to Tier 1+ and JIT state is
            // prepared, try the compiled native code path first. On JIT hit
            // we skip the interpreter entirely; on fallback/error we fall
            // through to the interpreter below.
            #[cfg(feature = "jit")]
            let jit_handled = if jit_state_ready {
                if let Some(ref manager) = self.tier_manager {
                    let tier = manager.current_tier(action_idx);
                    if tier >= tla_jit::CompilationTier::Tier1 {
                        // try_jit_action updates dispatch counters internally.
                        self.try_jit_action(&action.name, &current_arr)
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
            #[cfg(feature = "jit")]
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
}
