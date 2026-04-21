// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Successor generation dispatch.
//!
//! TLC alignment: `ModelChecker.doNext()` per-action dispatch.

use super::super::{
    enumerate_successors, ArrayState, CheckError, DiffSuccessor, ModelChecker, State,
    SuccessorResult,
};
use crate::{ConfigCheckError, EvalCheckError};

impl<'a> ModelChecker<'a> {
    /// Solve next-state relation to find successor states
    pub(in crate::check::model_checker) fn solve_next_relation(
        &mut self,
        next_name: &str,
        state: &State,
    ) -> Result<Vec<State>, CheckError> {
        // Part of #3296: resolve CONSTANT operator replacement for the actual
        // definition lookup. The caller passes the raw config name (for trace labels),
        // but op_defs stores the expanded definition under the resolved name.
        let resolved_name = self.ctx.resolve_op_name(next_name).to_string();
        // Part of #3255: OperatorDef clone removed — NLL releases the borrow
        // after the enumerate call, before the &mut self TIR methods below.
        let def = self
            .module
            .op_defs
            .get(&resolved_name)
            .ok_or(ConfigCheckError::MissingNext)?;

        let successors = enumerate_successors(&mut self.ctx, def, state, &self.module.vars)
            .map_err(EvalCheckError::Eval)?;
        if self.tir_parity.is_some() {
            let registry = self.ctx.var_registry().clone();
            let current_array = ArrayState::from_state(state, &registry);
            let mut validated = Vec::with_capacity(successors.len());
            for successor in successors {
                let succ_array = ArrayState::from_state(&successor, &registry);
                if self.transition_holds_via_tir(next_name, &current_array, &succ_array)? {
                    self.maybe_check_tir_parity_transition(next_name, &current_array, &succ_array)?;
                    validated.push(successor);
                }
            }
            return Ok(validated);
        }

        Ok(successors)
    }

    /// Solve Next relation returning ArrayState instead of State.
    ///
    /// NOTE: Assumes caller has already bound state variables via `bind_state_array`.
    ///
    /// Part of #131 (P1 optimization): Uses `enumerate_successors_array` which avoids
    /// State/OrdMap construction in the fast path. Falls back to State-based enumeration
    /// for complex expression types.
    fn solve_next_relation_as_array(
        &mut self,
        current_array: &ArrayState,
    ) -> Result<Vec<ArrayState>, CheckError> {
        // Part of #3255: as_deref() avoids String allocation on the common (non-TIR) path.
        // The TIR parity path (env-gated, off by default) creates a local owned copy.
        let raw_next_name = self
            .trace
            .cached_next_name
            .as_deref()
            .ok_or(ConfigCheckError::MissingNext)?;
        let resolved_next_name = self.ctx.resolve_op_name(raw_next_name).to_string();

        // Part of #3255: OperatorDef clone removed — NLL releases the borrow
        // after the enumerate call, before the &mut self TIR methods below.
        let def = self
            .module
            .op_defs
            .get(&resolved_next_name)
            .ok_or(ConfigCheckError::MissingNext)?;

        // Part of #3194: leaf-level TIR evaluation during successor generation
        // is keyed on the resolved `next_name`, not the literal string `Next`.
        // The TirProgram borrows from self.tir_parity (immutable), while
        // enumerate borrows self.ctx (mutable) — disjoint fields, so split
        // borrow is safe.
        let tir_program = self.tir_parity.as_ref().and_then(|p| {
            p.make_tir_program_for_selected_eval_name(raw_next_name, &resolved_next_name)
        });
        let leaf_tir_used = tir_program.is_some();

        // PlusCal pc-dispatch optimization for the ArrayState path.
        // Same logic as in generate_successors_as_diffs_raw — skip actions
        // whose pc guard doesn't match the current state.
        if !leaf_tir_used {
            if let Some(ref table) = self.compiled.pc_dispatch {
                let pc_val = current_array.get(table.pc_var_idx);
                if let Some(action_indices) = table.actions_for_pc(&pc_val) {
                    let mut all_successors: Vec<ArrayState> = Vec::new();
                    let mut action_def = tla_core::ast::OperatorDef {
                        name: def.name.clone(),
                        params: def.params.clone(),
                        body: table.actions[0].expr.clone(),
                        local: def.local,
                        contains_prime: def.contains_prime,
                        guards_depend_on_prime: false,
                        has_primed_param: def.has_primed_param,
                        is_recursive: false,
                        self_call_count: 0,
                    };
                    for &action_idx in action_indices {
                        action_def.body = table.actions[action_idx].expr.clone();
                        let succs = crate::enumerate::enumerate_successors_array_with_tir(
                            &mut self.ctx,
                            &action_def,
                            current_array,
                            &self.module.vars,
                            None,
                        )
                        .map_err(EvalCheckError::Eval)?;
                        all_successors.extend(succs);
                    }
                    return Ok(all_successors);
                }
                // pc value not in dispatch table — fall through to full enumeration.
            }
        }

        // Part of #131 (P1): Use ArrayState-native enumeration to avoid State construction.
        // This avoids O(n) OrdMap construction for each successor in the fast path.
        let successors = crate::enumerate::enumerate_successors_array_with_tir(
            &mut self.ctx,
            def,
            current_array,
            &self.module.vars,
            tir_program.as_ref(),
        )
        .map_err(EvalCheckError::Eval)?;
        if self.tir_parity.is_some() && !leaf_tir_used {
            // Allocate owned copy only for the TIR parity path (env-gated, rare).
            // Part of #3296/#3294: when successor enumeration already used a
            // leaf-level TirProgram, replaying eval_named_op() here double-counts
            // named-op probes without changing filtering/parity behavior.
            let next_owned = raw_next_name.to_string();
            let mut validated = Vec::with_capacity(successors.len());
            for successor in successors {
                if self.transition_holds_via_tir(&next_owned, current_array, &successor)? {
                    self.maybe_check_tir_parity_transition(&next_owned, current_array, &successor)?;
                    validated.push(successor);
                }
            }
            return Ok(validated);
        }

        Ok(successors)
    }

    /// Generate successor ArrayStates from a given ArrayState via Next relation.
    pub(in crate::check::model_checker) fn generate_successors_as_array(
        &mut self,
        current_array: &ArrayState,
    ) -> Result<Vec<ArrayState>, CheckError> {
        let _state_guard = self.ctx.bind_state_env_guard(current_array.env_ref());

        let successors = self.solve_next_relation_as_array(current_array)?;

        Ok(successors)
    }

    /// Check whether a successor passes all configured state and action constraints.
    ///
    /// Part of #3322: extracted from three constraint filter sites to eliminate
    /// the repeated `has_action_constraints` / nested-if pattern.
    pub(in crate::check::model_checker) fn successor_passes_constraints(
        &mut self,
        current_array: &ArrayState,
        succ: &ArrayState,
    ) -> Result<bool, CheckError> {
        if !self.check_state_constraints_array(succ)? {
            return Ok(false);
        }
        if !self.config.action_constraints.is_empty()
            && !self.check_action_constraints_array(current_array, succ)?
        {
            return Ok(false);
        }
        Ok(true)
    }

    /// Generate successor DiffSuccessors from a given ArrayState via Next relation.
    ///
    /// Part of #131: Early deduplication optimization. DiffSuccessors contain pre-computed
    /// fingerprints, allowing the BFS loop to check `is_state_seen()` BEFORE materializing
    /// full ArrayStates. For duplicate states (~95%), this avoids allocation entirely.
    ///
    /// Returns:
    /// - `Ok(Some(result))` for simple action structures that the diff path can handle
    /// - `Ok(None)` for complex actions that require full ArrayState enumeration
    pub(in crate::check::model_checker) fn generate_successors_as_diffs_raw(
        &mut self,
        current_array: &ArrayState,
    ) -> Result<Option<SuccessorResult<Vec<DiffSuccessor>>>, CheckError> {
        // POR needs per-action enabled-set computation, which the diff fast path
        // cannot provide today. Fall back to full-state enumeration.
        if self.por.independence.is_some() {
            return Ok(None);
        }

        // Coverage collection not supported in diff path - use ArrayState path
        if self.coverage.collect && !self.coverage.actions.is_empty() {
            return Ok(None);
        }

        let _state_guard = self.ctx.bind_state_env_guard(current_array.env_ref());

        // Part of #3255: as_deref() avoids String allocation on the common (non-TIR) path.
        // Part of #3296: split raw/resolved for CONSTANT operator replacement correctness.
        let raw_next_name = self
            .trace
            .cached_next_name
            .as_deref()
            .ok_or(ConfigCheckError::MissingNext)?;
        let resolved_next_name = self.ctx.resolve_op_name(raw_next_name).to_string();

        // Part of #3255: OperatorDef clone removed — NLL releases the borrow
        // after the last enumerate call, before the &mut self TIR methods below.
        let def = self
            .module
            .op_defs
            .get(&resolved_next_name)
            .ok_or(ConfigCheckError::MissingNext)?;

        // Part of #3294: select the TIR successor evaluator once at the shared
        // batch diff boundary so constrained/implied-action runs use the same
        // generation policy as the streaming path.
        let tir_program = self.tir_parity.as_ref().and_then(|p| {
            p.make_tir_program_for_selected_eval_name(raw_next_name, &resolved_next_name)
        });

        // PlusCal pc-dispatch optimization: when all Next disjuncts are guarded
        // by `pc = "label"`, read the current pc value and enumerate only matching
        // actions. This avoids evaluating guards that are guaranteed to be FALSE.
        // TIR is not used with pc-dispatch (the per-action defs are synthetic).
        if tir_program.is_none() {
            if let Some(ref table) = self.compiled.pc_dispatch {
                let pc_val = current_array.get(table.pc_var_idx);
                if let Some(action_indices) = table.actions_for_pc(&pc_val) {
                    let mut all_diffs: Vec<DiffSuccessor> = Vec::new();
                    // Build a temporary OperatorDef for each matching action.
                    let mut action_def = tla_core::ast::OperatorDef {
                        name: def.name.clone(),
                        params: def.params.clone(),
                        body: table.actions[0].expr.clone(),
                        local: def.local,
                        contains_prime: def.contains_prime,
                        guards_depend_on_prime: false,
                        has_primed_param: def.has_primed_param,
                        is_recursive: false,
                        self_call_count: 0,
                    };
                    for &action_idx in action_indices {
                        action_def.body = table.actions[action_idx].expr.clone();
                        let diffs = crate::enumerate::enumerate_successors_array_as_diffs(
                            &mut self.ctx,
                            &action_def,
                            current_array,
                            &self.module.vars,
                            None,
                        )
                        .map_err(EvalCheckError::Eval)?;
                        if let Some(d) = diffs {
                            all_diffs.extend(d);
                        }
                    }
                    let had_raw_successors = !all_diffs.is_empty();
                    return Ok(Some(SuccessorResult {
                        successors: all_diffs,
                        had_raw_successors,
                    }));
                }
                // pc value not in dispatch table — fall through to full enumeration.
            }
        }

        // Part of #3354 Slice 1: unified-only successor generation.
        // The compiled split-action dispatch is removed. All successor
        // enumeration routes through the canonical AST/TIR unified path.
        // Action splitting as an algorithmic structure is preserved inside
        // the unified enumerator; only the second evaluator (CompiledAction
        // stack machine) is bypassed.
        let leaf_tir_used = tir_program.is_some();
        let diffs_opt = crate::enumerate::enumerate_successors_array_as_diffs(
            &mut self.ctx,
            def,
            current_array,
            &self.module.vars,
            tir_program.as_ref(),
        )
        .map_err(EvalCheckError::Eval)?;

        match diffs_opt {
            Some(mut diffs) => {
                let registry = self.ctx.var_registry().clone();
                if self.tir_parity.is_some() && !leaf_tir_used {
                    // Part of #3296: use raw name for TIR parity (matches convention).
                    // Part of #3294: constrained diff generation already threads
                    // tir_leaf through enumerate_successors_array_as_diffs(), so
                    // avoid replaying eval_named_op() per successor here.
                    let next_owned = raw_next_name.to_string();
                    let mut tir_valid_diffs: Vec<DiffSuccessor> = Vec::with_capacity(diffs.len());
                    for diff in diffs {
                        let succ = diff.materialize(current_array, &registry);
                        if self.transition_holds_via_tir(&next_owned, current_array, &succ)? {
                            self.maybe_check_tir_parity_transition(
                                &next_owned,
                                current_array,
                                &succ,
                            )?;
                            tir_valid_diffs.push(diff);
                        }
                    }
                    diffs = tir_valid_diffs;
                }
                let had_raw_successors = !diffs.is_empty();

                Ok(Some(SuccessorResult {
                    successors: diffs,
                    had_raw_successors,
                }))
            }
            None => Ok(None), // Fall back to ArrayState path
        }
    }

    /// Generate successor DiffSuccessors and apply configured constraints.
    ///
    /// Retained for callers that still want filtering at generation time. The
    /// sequential BFS batch paths now call [`generate_successors_as_diffs_raw`]
    /// and route constraints through the observer layer instead.
    #[allow(dead_code)]
    pub(in crate::check::model_checker) fn generate_successors_as_diffs(
        &mut self,
        current_array: &ArrayState,
    ) -> Result<Option<SuccessorResult<Vec<DiffSuccessor>>>, CheckError> {
        match self.generate_successors_as_diffs_raw(current_array)? {
            Some(result)
                if !self.config.constraints.is_empty()
                    || !self.config.action_constraints.is_empty() =>
            {
                let registry = self.ctx.var_registry().clone();
                let mut valid_diffs: Vec<DiffSuccessor> =
                    Vec::with_capacity(result.successors.len());
                for diff in result.successors {
                    let succ = diff.materialize(current_array, &registry);
                    if self.successor_passes_constraints(current_array, &succ)? {
                        valid_diffs.push(diff);
                    }
                }
                Ok(Some(SuccessorResult {
                    successors: valid_diffs,
                    had_raw_successors: result.had_raw_successors,
                }))
            }
            other => Ok(other),
        }
    }

    /// Generate successor ArrayStates filtered by state and action constraints.
    ///
    /// This is the array-based equivalent of `generate_successors_filtered`.
    /// Returns a SuccessorResult that includes whether there were any raw successors
    /// before constraint filtering (used for correct deadlock detection per TLC semantics).
    ///
    /// Note: This method is retained for the coverage collection fallback path
    /// and for constrained specs that need explicit filtering.
    pub(in crate::check::model_checker) fn generate_successors_array_raw(
        &mut self,
        current_array: &ArrayState,
    ) -> Result<SuccessorResult<Vec<ArrayState>>, CheckError> {
        // Coverage and POR both rely on per-action successor dispatch, which already
        // exists in the state-based path. Route through that shared implementation.
        if (self.coverage.collect && !self.coverage.actions.is_empty())
            || self.por.independence.is_some()
        {
            let registry = self.ctx.var_registry().clone();
            let state = current_array.to_state(&registry);
            // Action-dispatch fallback: clone needed because generate_successors_filtered
            // takes &mut self, conflicting with a borrow of self.trace.
            let next_name = self
                .trace
                .cached_next_name
                .clone()
                .ok_or(ConfigCheckError::MissingNext)?;
            let result = self.generate_successors_filtered(&next_name, &state)?;
            // Part of #131: Use from_successor_state for incremental fingerprinting.
            // Also satisfies #158: computes fingerprint using registry order, not alphabetical.
            return Ok(SuccessorResult {
                successors: result
                    .successors
                    .into_iter()
                    .map(|s| ArrayState::from_successor_state(&s, current_array, &registry))
                    .collect(),
                had_raw_successors: result.had_raw_successors,
            });
        }

        let successors = self.generate_successors_as_array(current_array)?;
        let had_raw_successors = !successors.is_empty();

        Ok(SuccessorResult {
            successors,
            had_raw_successors,
        })
    }

    /// Generate successor ArrayStates filtered by state and action constraints.
    ///
    /// This is the array-based equivalent of `generate_successors_filtered`.
    /// Returns a SuccessorResult that includes whether there were any raw successors
    /// before constraint filtering (used for correct deadlock detection per TLC semantics).
    ///
    /// Note: This method is retained for the coverage collection fallback path
    /// and for constrained specs that need explicit filtering.
    pub(in crate::check::model_checker) fn generate_successors_filtered_array(
        &mut self,
        current_array: &ArrayState,
    ) -> Result<SuccessorResult<Vec<ArrayState>>, CheckError> {
        let raw = self.generate_successors_array_raw(current_array)?;

        // Fast path: no constraints to check, return successors directly
        if self.config.constraints.is_empty() && self.config.action_constraints.is_empty() {
            return Ok(raw);
        }

        // Filter by state constraints and action constraints
        let mut valid = Vec::new();
        for succ in raw.successors {
            if self.successor_passes_constraints(current_array, &succ)? {
                valid.push(succ);
            }
        }

        Ok(SuccessorResult {
            successors: valid,
            had_raw_successors: raw.had_raw_successors,
        })
    }

    /// Part of #3100: Generate successor ArrayStates with action provenance tags.
    ///
    /// Part of #3354 Slice 1: successor generation is now unified-only, so this
    /// helper currently returns `None` tags for every successor while preserving
    /// the tagged result shape for liveness callers.
    ///
    /// Returns `(SuccessorResult, action_tags)` where `action_tags[i]` is the
    /// split_action index that produced `successors[i]`, or `None` for monolithic.
    #[allow(clippy::type_complexity)]
    pub(in crate::check::model_checker) fn generate_successors_filtered_array_tagged(
        &mut self,
        current_array: &ArrayState,
    ) -> Result<(SuccessorResult<Vec<ArrayState>>, Vec<Option<usize>>), CheckError> {
        // Coverage collection: fall back to untagged path
        if self.coverage.collect && !self.coverage.actions.is_empty() {
            let result = self.generate_successors_filtered_array(current_array)?;
            let tags = vec![None; result.successors.len()];
            return Ok((result, tags));
        }

        let _state_guard = self.ctx.bind_state_env_guard(current_array.env_ref());

        // Part of #3255: as_deref() avoids String allocation on the common (non-TIR) path.
        // Compute owned copy up front if TIR is active, to release self.trace borrow
        // before the &mut self enumeration calls below.
        let next_name = self
            .trace
            .cached_next_name
            .as_deref()
            .ok_or(ConfigCheckError::MissingNext)?;
        let next_owned_opt = if self.tir_parity.is_some() {
            Some(next_name.to_string())
        } else {
            None
        };

        // Part of #3354 Slice 1: unified-only successor generation.
        // Per-action tagging requires split-action enumeration which is being
        // removed. All successors come from the monolithic unified path with
        // no per-action provenance (tags are None).
        let succs = self.solve_next_relation_as_array(current_array)?;
        let tags: Vec<Option<usize>> = vec![None; succs.len()];
        let (successors, tags, needs_tir_filter) = (succs, tags, false);

        let (successors, tags) =
            if let (true, Some(next_owned)) = (needs_tir_filter, next_owned_opt) {
                let mut validated = Vec::with_capacity(successors.len());
                let mut validated_tags = Vec::with_capacity(tags.len());
                for (succ, tag) in successors.into_iter().zip(tags) {
                    if self.transition_holds_via_tir(&next_owned, current_array, &succ)? {
                        self.maybe_check_tir_parity_transition(&next_owned, current_array, &succ)?;
                        validated.push(succ);
                        validated_tags.push(tag);
                    }
                }
                (validated, validated_tags)
            } else {
                (successors, tags)
            };

        let had_raw_successors = !successors.is_empty();

        // Apply constraints (preserving tag association)
        if self.config.constraints.is_empty() && self.config.action_constraints.is_empty() {
            return Ok((
                SuccessorResult {
                    successors,
                    had_raw_successors,
                },
                tags,
            ));
        }

        let mut valid = Vec::new();
        let mut valid_tags = Vec::new();
        for (succ, tag) in successors.into_iter().zip(tags) {
            if self.successor_passes_constraints(current_array, &succ)? {
                valid.push(succ);
                valid_tags.push(tag);
            }
        }

        Ok((
            SuccessorResult {
                successors: valid,
                had_raw_successors,
            },
            valid_tags,
        ))
    }
}
