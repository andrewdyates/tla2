// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Parallel checker prepare phase.

use super::*;
use crate::check::validate_all_config_ops;
use crate::{ConfigCheckError, EvalCheckError};
// Part of #4267 Gate 1 Batch C: collapse Cranelift-backed JIT type paths.
use tla_jit::bytecode_lower::JitInvariantCache as JitInvariantCacheImpl;

impl Drop for CheckPreparation {
    fn drop(&mut self) {
        crate::intern::end_model_check_run();
    }
}

impl ParallelChecker {
    fn detected_actions_info_for_resolved_next(
        &self,
        resolved_next_name: &str,
    ) -> Vec<crate::coverage::DetectedAction> {
        self.op_defs
            .get(resolved_next_name)
            .map(detect_actions)
            .unwrap_or_default()
    }

    fn detect_actions_for_resolved_next(
        &self,
        resolved_next_name: &str,
    ) -> (Vec<String>, Vec<String>) {
        let detected_actions_info =
            self.detected_actions_info_for_resolved_next(resolved_next_name);
        let detected_actions = detected_actions_info
            .iter()
            .map(|action| action.name.clone())
            .collect();
        let detected_action_ids = detected_actions_info
            .into_iter()
            .map(|action| action.id.to_string())
            .collect();
        (detected_actions, detected_action_ids)
    }

    fn prepare_por_state(
        &self,
        ctx: &EvalCtx,
        resolved_next_name: &str,
        detected_actions_info: Vec<crate::coverage::DetectedAction>,
        eval_state_invariants: &[(String, tla_core::Spanned<tla_core::ast::Expr>)],
    ) -> (
        Arc<Vec<crate::coverage::DetectedAction>>,
        Option<Arc<crate::por::IndependenceMatrix>>,
        Arc<crate::por::VisibilitySet>,
    ) {
        let por_actions = Arc::new(detected_actions_info);
        // POR is disabled when liveness properties are present because the C3
        // BFS proviso is insufficient for liveness — it only guarantees no
        // exploration cycles in safety BFS, but liveness checking requires
        // the "ignoring proviso" (Peled 1996) or "strong proviso" which we
        // do not yet implement.
        let has_liveness = self.config.has_liveness_properties();

        // Part of #3993: Auto-POR for the parallel checker. Same logic as
        // sequential: when auto-POR is enabled (default), run independence
        // analysis even when --por isn't explicitly passed. Part of #4164.
        let auto_por = crate::por::resolve_auto_por(self.config.auto_por);
        let por_candidate = (self.config.por_enabled || auto_por)
            && !por_actions.is_empty()
            && !has_liveness
            && por_actions.len() >= 2;

        if !por_candidate {
            if has_liveness && self.config.por_enabled {
                eprintln!(
                    "POR: disabled — liveness properties present (C3 BFS proviso is insufficient for liveness)"
                );
            }
            return (
                por_actions,
                None,
                Arc::new(crate::por::VisibilitySet::new()),
            );
        }

        let independence = self
            .op_defs
            .get(resolved_next_name)
            .map(|next_def| {
                let por_expanded =
                    crate::checker_ops::expand_operator_body_with_primes(ctx, next_def);
                let por_actions = detect_actions(&por_expanded);
                let action_dependencies =
                    crate::por::extract_detected_action_dependencies(&por_actions);
                let matrix = crate::por::IndependenceMatrix::compute(&action_dependencies);

                // Auto-POR gate: skip POR when no independent pairs found.
                if !self.config.por_enabled && matrix.count_independent_pairs() == 0 {
                    return None;
                }
                Some(Arc::new(matrix))
            })
            .flatten();

        let mut visibility = crate::por::VisibilitySet::new();
        for (_name, expr) in eval_state_invariants {
            visibility.extend_from_expanded_expr(ctx, expr);
        }

        for inv_name in &self.config.invariants {
            if let Some(def) = ctx.get_op(inv_name) {
                visibility.extend_from_expanded_expr(ctx, &def.body);
            } else {
                eprintln!(
                    "POR: config invariant '{}' not found in op_defs, disabling reduction",
                    inv_name
                );
                visibility.mark_all_visible();
                break;
            }
        }

        (por_actions, independence, Arc::new(visibility))
    }

    #[allow(clippy::result_large_err)]
    pub(super) fn prepare_base_ctx(&self) -> Result<EvalCtx, CheckResult> {
        if let Some(err) = self.setup_error.clone() {
            return Err(check_error_to_result(err, &CheckStats::default()));
        }

        // Create evaluation context for setup-time validation/classification.
        let mut ctx = EvalCtx::new();
        // Part of #1102: Propagate input_base_dir so IO builtins (ndJsonDeserialize, etc.)
        // can resolve relative file paths against the spec directory.
        ctx.set_input_base_dir(self.input_base_dir.clone());

        // Shared module loading sequence: set extended_module_names, load unqualified
        // modules, load main module, then load instance modules (Part of #810).
        let ext_refs: Vec<&Module> = self.extended_modules.iter().collect();
        crate::checker_ops::load_modules_into_ctx(
            &mut ctx,
            &self.module,
            &ext_refs,
            &self.unqualified_modules,
            true, // load instances for I!Op references
        );

        // Register state variables in VarRegistry for efficient array-based state handling
        ctx.register_vars(self.vars.iter().cloned());
        ctx.resolve_state_vars_in_loaded_ops();

        // Bind constants from config before generating initial states
        if let Err(e) = bind_constants_from_config(&mut ctx, &self.config) {
            return Err(check_error_to_result(
                EvalCheckError::Eval(e).into(),
                &CheckStats::default(),
            ));
        }

        // Sync TLC config for TLCGet("config") support (must happen before ASSUME checking).
        // Fix #563: Sequential checker did this but parallel checker was missing it.
        let tlc_config = TlcConfig::new(
            Arc::from("bfs"),
            self.max_depth_limit.map_or(-1, |d| d as i64),
            self.check_deadlock,
        );
        ctx.set_tlc_config(tlc_config);

        // Part of #1102: Set initial BFS level for TLCGet("level") during init state generation.
        // TLC uses 1-based levels: initial states are at level 1.
        ctx.set_tlc_level(1);

        // Part of #2753: Pre-evaluate zero-arity constant operators for O(1) lookup during BFS.
        // Sequential checker already does this (run_prepare.rs:249); this was missing here.
        crate::check::precompute_constant_operators(&mut ctx);
        // Part of #2895: Promote env constants to precomputed_constants.
        crate::check::promote_env_constants_to_precomputed(&mut ctx);
        // Part of #3961: Build ident resolution hints for eval_ident fast-path dispatch.
        crate::check::build_ident_hints(&mut ctx);

        Ok(ctx)
    }

    #[allow(clippy::result_large_err)]
    fn validate_prepare_ctx(&self, ctx: &EvalCtx) -> Result<(), CheckResult> {
        // Check ASSUME statements before model checking (Fix #563).
        // Delegates to checker_ops::check_assumes — the single shared
        // implementation used by both sequential and parallel checkers (Part of #810).
        if let Some(error) = crate::checker_ops::check_assumes(ctx, &self.assumes) {
            return Err(check_error_to_result(error, &CheckStats::default()));
        }

        // Part of #2675: Full config operator validation (existence, arity, level).
        // Previously only checked invariant existence. Now matches sequential checker's
        // validate_config_ops() by sharing the same standalone validation functions.
        validate_all_config_ops(ctx, &self.config, self.vars.len())
            .map_err(|error| check_error_to_result(error, &CheckStats::default()))?;

        Ok(())
    }

    #[allow(clippy::result_large_err)]
    pub(crate) fn state_property_violation_names_for_resume(
        &self,
    ) -> Result<Vec<String>, CheckResult> {
        if self.config.properties.is_empty() {
            return Ok(Vec::new());
        }

        let ctx = self.prepare_base_ctx()?;
        self.validate_prepare_ctx(&ctx)?;
        Ok(crate::checker_ops::classify_property_safety_parts(
            &ctx,
            &self.config.properties,
            &self.op_defs,
        )
        .state_violation_properties)
    }

    #[allow(clippy::result_large_err)]
    pub(crate) fn detected_actions_for_resume(
        &self,
    ) -> Result<(Vec<String>, Vec<String>), CheckResult> {
        let next_name = match &self.config.next {
            Some(name) => name.clone(),
            None => {
                return Err(check_error_to_result(
                    ConfigCheckError::MissingNext.into(),
                    &CheckStats::default(),
                ));
            }
        };

        let ctx = self.prepare_base_ctx()?;
        self.validate_prepare_ctx(&ctx)?;
        let resolved_next_name = ctx.resolve_op_name(&next_name).to_string();
        Ok(self.detect_actions_for_resolved_next(&resolved_next_name))
    }

    #[allow(clippy::result_large_err)]
    pub(super) fn prepare_check(&self) -> Result<CheckPreparation, CheckResult> {
        let init_name = match &self.config.init {
            Some(name) => name.clone(),
            None => {
                return Err(check_error_to_result(
                    ConfigCheckError::MissingInit.into(),
                    &CheckStats::default(),
                ));
            }
        };

        let next_name = match &self.config.next {
            Some(name) => name.clone(),
            None => {
                return Err(check_error_to_result(
                    ConfigCheckError::MissingNext.into(),
                    &CheckStats::default(),
                ));
            }
        };

        // Part of #2699: NoVariables check moved to validate_all_config_ops().

        // Part of #2740: Liveness properties are now supported via post-BFS checking.
        // The previous rejection (Part of #2250) is removed. Fingerprint-only mode
        // still skips liveness with a warning (handled in finalize_check).

        // Create evaluation context for initial state generation and setup-time classification.
        let mut ctx = self.prepare_base_ctx()?;

        // Resolve init_name through op_replacements (e.g., `CONSTANT Init <- MCInit`).
        // The sequential checker does this in resolve_init_predicate(); the parallel
        // checker must do it here after prepare_base_ctx() binds constants.
        let init_name = ctx.resolve_op_name(&init_name).to_string();

        // Part of #3011: Compute symmetry permutations for canonical fingerprinting.
        // Mirrors sequential checker's compute_symmetry_perms (run_prepare.rs:214-226).
        // Part of #3011 Unit 3: Propagate errors instead of silently swallowing via .ok().
        let mvperms: Arc<Vec<crate::value::MVPerm>> = if self.config.symmetry.is_some() {
            let perms = crate::check::compute_symmetry_perms(&ctx, &self.config)
                .map_err(|e| check_error_to_result(e, &CheckStats::default()))?;
            let mvperms: Vec<_> = perms
                .iter()
                .map(crate::value::MVPerm::from_func_value)
                .collect::<Result<Vec<_>, _>>()
                .map_err(|e| {
                    check_error_to_result(EvalCheckError::Eval(e).into(), &CheckStats::default())
                })?;
            Arc::new(mvperms)
        } else {
            Arc::new(Vec::new())
        };

        self.validate_prepare_ctx(&ctx)?;

        let resolved_next_name = ctx.resolve_op_name(&next_name).to_string();
        let parallel_tir_next_selection = crate::tir_mode::parallel_direct_next_tir_eval_selection(
            &next_name,
            &resolved_next_name,
        )
        .map_err(|message| {
            check_error_to_result(
                ConfigCheckError::Config(message).into(),
                &CheckStats::default(),
            )
        })?;
        let detected_actions_info =
            self.detected_actions_info_for_resolved_next(&resolved_next_name);
        let detected_actions: Vec<String> = detected_actions_info
            .iter()
            .map(|action| action.name.clone())
            .collect();
        let detected_action_ids: Vec<String> = detected_actions_info
            .iter()
            .map(|action| action.id.to_string())
            .collect();

        // Validate and cache VIEW operator name.
        // Delegates to checker_ops::validate_view_operator — the single shared
        // implementation used by both sequential and parallel checkers (Part of #810).
        let cached_view_name: Option<String> =
            crate::checker_ops::validate_view_operator(&ctx, &self.config);

        // Part of #2740/#3710: In on-the-fly liveness mode, keep PROPERTY safety
        // terms out of the BFS invariant lanes so the dedicated on-the-fly
        // property checker remains the single execution path for PROPERTY traces.
        // Otherwise mixed `[]P /\ <>Q` properties can fail during BFS with
        // no-trace invariant-style results, bypassing the direct property traces
        // produced by `check_single_property_on_the_fly`.
        let property_classification =
            (!self.config.liveness_execution.uses_on_the_fly()).then(|| {
                crate::checker_ops::classify_property_safety_parts(
                    &ctx,
                    &self.config.properties,
                    &self.op_defs,
                )
            });
        let eval_implied_actions: Arc<Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>> =
            Arc::new(
                property_classification
                    .as_ref()
                    .map_or_else(Vec::new, |classification| {
                        classification.eval_implied_actions.clone()
                    }),
            );
        let eval_state_invariants: Arc<Vec<(String, tla_core::Spanned<tla_core::ast::Expr>)>> =
            Arc::new(
                property_classification
                    .as_ref()
                    .map_or_else(Vec::new, |classification| {
                        classification.eval_state_invariants.clone()
                    }),
            );

        // Part of #3053: Store init predicates for initial-state checking.
        let property_init_predicates = property_classification
            .as_ref()
            .map_or_else(Vec::new, |classification| {
                classification.init_predicates.clone()
            });

        let state_property_violation_names: Vec<String> = property_classification
            .as_ref()
            .map_or_else(Vec::new, |classification| {
                classification.state_violation_properties.clone()
            });

        // Preserve the fully promoted state-only property names for post-BFS liveness skip.
        let promoted_property_invariants: Vec<String> = property_classification
            .as_ref()
            .map_or_else(Vec::new, |classification| {
                classification.promoted_invariant_properties.clone()
            });

        let (por_actions, por_independence, por_visibility) = self.prepare_por_state(
            &ctx,
            &resolved_next_name,
            detected_actions_info,
            &eval_state_invariants,
        );

        // Collect fully-promoted property names for post-BFS liveness skip.
        let mut promoted_properties: Vec<String> = property_classification
            .as_ref()
            .map_or_else(Vec::new, |classification| {
                classification.promoted_invariant_properties.clone()
            });
        if let Some(classification) = property_classification {
            for name in classification.promoted_action_properties {
                if !promoted_properties.contains(&name) {
                    promoted_properties.push(name);
                }
            }
        }

        let var_registry = Arc::new(ctx.var_registry().clone());

        // Fix #344: Pre-expand operator references in the Next action body.
        // Delegates to checker_ops::expand_operator_body (Part of #810).
        let mut expanded_op_defs = self.op_defs.clone();
        if let Some(next_def) = expanded_op_defs.get(&resolved_next_name).cloned() {
            let expanded_def = crate::checker_ops::expand_operator_body(&ctx, &next_def);
            expanded_op_defs.insert(resolved_next_name.clone(), expanded_def);
        }

        // Part of #2740: TLC_LIVE_FORMULA_TAUTOLOGY pre-check (EC 2253).
        // TLC rejects tautological liveness properties before state exploration.
        // Previously this check only happened post-BFS in the parallel path, wasting
        // the entire BFS run. Matches sequential checker's pre-BFS behavior.
        if let Some(error) = crate::checker_ops::check_property_tautologies(
            &ctx,
            &self.config.properties,
            &self.op_defs,
            self.module.name.node.as_str(),
        ) {
            return Err(check_error_to_result(error, &CheckStats::default()));
        }

        // Generate initial states (streaming bulk or Vec<State> fallback)
        // Part of #2789: Route through check_error_to_result so
        // ExitRequested maps to LimitReached(Exit).
        let initial_states: InitialStates =
            match self.generate_initial_states_to_bulk(&mut ctx, &init_name) {
                Ok(Some(storage)) => InitialStates::Bulk(storage),
                Ok(None) => match self.generate_initial_states(&ctx, &init_name) {
                    Ok(states) => InitialStates::Vec(states),
                    Err(e) => return Err(check_error_to_result(e, &CheckStats::default())),
                },
                Err(e) => return Err(check_error_to_result(e, &CheckStats::default())),
            };

        // Part of #3621: Compile invariant bytecode for parallel workers.
        // Mirrors sequential checker's compile_invariant_bytecode (run_prepare.rs:259).
        let bytecode = if !self.config.invariants.is_empty() && tla_eval::tir::bytecode_vm_enabled()
        {
            self.compile_invariant_bytecode_for_workers(&ctx, &var_registry, &initial_states)
        } else {
            None
        };
        let jit_cache = self.compile_jit_invariant_cache_for_workers(&bytecode, &initial_states);

        // Part of #3960: Compile action bytecode for JIT next-state dispatch.
        // Mirrors sequential checker's compile_action_bytecode (run_prepare.rs:535).
        // The action bytecode contains StoreVar opcodes for primed variables,
        // which the JitNextStateCache needs to produce successor states.
        let action_bytecode = if crate::check::debug::jit_enabled() {
            self.compile_action_bytecode_for_workers(
                &ctx,
                &var_registry,
                &resolved_next_name,
                &detected_actions,
            )
        } else {
            None
        };

        // Pre-analyze ACTION_CONSTRAINTs for variable dependencies (parallel path).
        let action_constraint_analysis = if !self.config.action_constraints.is_empty() {
            Some(Arc::new(
                crate::checker_ops::ActionConstraintAnalysis::build(
                    &ctx,
                    &self.config.action_constraints,
                ),
            ))
        } else {
            None
        };

        crate::intern::begin_model_check_run();

        Ok(CheckPreparation {
            resolved_next_name,
            parallel_tir_next_selection,
            detected_actions,
            detected_action_ids,
            por_actions,
            por_independence,
            por_visibility,
            ctx,
            cached_view_name,
            eval_implied_actions,
            eval_state_invariants,
            property_init_predicates,
            state_property_violation_names,
            var_registry,
            expanded_op_defs,
            initial_states: Some(initial_states),
            promoted_properties,
            promoted_property_invariants,
            mvperms,
            bytecode,
            action_bytecode,
            jit_cache,
            action_constraint_analysis,
        })
    }

    /// Compile invariant operators to bytecode for parallel worker threads.
    ///
    /// Part of #3621: Mirrors sequential checker's `compile_invariant_bytecode`
    /// (run_prepare.rs:259). Clones module ASTs, resolves state vars in operator
    /// bodies (required for correct LoadVar opcodes), and compiles via
    /// `compile_operators_to_bytecode_with_constants`. Returns `Arc`-wrapped
    /// result for sharing across workers.
    fn compile_invariant_bytecode_for_workers(
        &self,
        ctx: &EvalCtx,
        var_registry: &Arc<VarRegistry>,
        initial_states: &InitialStates,
    ) -> Option<Arc<tla_eval::bytecode_vm::CompiledBytecode>> {
        use tla_core::ast::Unit;

        let mut root = (*self.module).clone();
        let mut deps: Vec<tla_core::ast::Module> = self.extended_modules.iter().cloned().collect();

        // Resolve state vars in operator bodies — without this, bytecode compiler
        // emits LoadConst with string names instead of LoadVar with VarRegistry indices.
        let registry = (**var_registry).clone();
        for unit in &mut root.units {
            if let Unit::Operator(def) = &mut unit.node {
                tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
            }
        }
        for dep in &mut deps {
            for unit in &mut dep.units {
                if let Unit::Operator(def) = &mut unit.node {
                    tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
                }
            }
        }

        let dep_refs: Vec<&tla_core::ast::Module> = deps.iter().collect();
        let tir_callees =
            tla_eval::bytecode_vm::collect_bytecode_namespace_callees(&root, &dep_refs);
        let mut compiled = tla_eval::bytecode_vm::compile_operators_to_bytecode_full(
            &root,
            &dep_refs,
            &self.config.invariants,
            ctx.precomputed_constants(),
            Some(ctx.op_replacements()),
            Some(&tir_callees),
        );

        match initial_states {
            InitialStates::Bulk(storage) if !storage.is_empty() => {
                let mut scratch = ArrayState::new(var_registry.len());
                scratch.overwrite_from_slice(storage.get_state(0));
                let runtime_failed =
                        crate::check::model_checker::invariants::collect_runtime_failing_invariant_bytecode_ops(
                            &compiled,
                            &self.config.invariants,
                            scratch.env_ref(),
                            ctx,
                        );
                crate::check::model_checker::invariants::prune_runtime_failing_invariant_bytecode_ops(
                    &mut compiled,
                    runtime_failed,
                    "bytecode-parallel",
                );
            }
            InitialStates::Vec(states) => {
                if let Some(first_state) = states.first() {
                    let first_arr = ArrayState::from_state(first_state, var_registry);
                    let runtime_failed =
                        crate::check::model_checker::invariants::collect_runtime_failing_invariant_bytecode_ops(
                            &compiled,
                            &self.config.invariants,
                            first_arr.env_ref(),
                            ctx,
                        );
                    crate::check::model_checker::invariants::prune_runtime_failing_invariant_bytecode_ops(
                        &mut compiled,
                        runtime_failed,
                        "bytecode-parallel",
                    );
                }
            }
            _ => {}
        }

        let stats_enabled = crate::check::debug::bytecode_vm_stats_enabled();
        let reason_logs_enabled = stats_enabled || crate::check::debug::debug_bytecode_vm();
        if stats_enabled {
            eprintln!(
                "[bytecode-parallel] compiled {}/{} invariants ({} failed)",
                compiled.op_indices.len(),
                self.config.invariants.len(),
                compiled.failed.len(),
            );
        }
        if reason_logs_enabled {
            for (name, err) in &compiled.failed {
                eprintln!("[bytecode-parallel]   skip {name}: {err}");
            }
        }

        if compiled.op_indices.is_empty() {
            None
        } else {
            Some(Arc::new(compiled))
        }
    }

    /// Compile action operators to bytecode for JIT next-state dispatch.
    ///
    /// Part of #3960: Mirrors sequential checker's `compile_action_bytecode`
    /// (run_prepare.rs:535). Compiles the Next operator (and detected sub-actions)
    /// with state var resolution, then applies `transform_action_to_next_state`
    /// to rewrite `LoadPrime(x) + Eq` into `StoreVar(x, expr)` so the
    /// JitNextStateCache can produce successor states from native code.
    ///
    /// Returns `None` when compilation or transformation yields no usable actions.
    fn compile_action_bytecode_for_workers(
        &self,
        ctx: &EvalCtx,
        var_registry: &Arc<VarRegistry>,
        resolved_next_name: &str,
        detected_actions: &[String],
    ) -> Option<Arc<tla_eval::bytecode_vm::CompiledBytecode>> {
        use tla_core::ast::Unit;

        // Build the list of action operator names to compile.
        // Include the monolithic Next operator (used by parallel dispatch)
        // and the detected sub-actions (for future split-action dispatch).
        let mut action_names: Vec<String> = vec![resolved_next_name.to_string()];
        for name in detected_actions {
            if name != resolved_next_name && !action_names.contains(name) {
                action_names.push(name.clone());
            }
        }

        // Clone module ASTs and resolve state vars (same pattern as invariant bytecode).
        let mut root = (*self.module).clone();
        let mut deps: Vec<tla_core::ast::Module> = self.extended_modules.iter().cloned().collect();

        let registry = (**var_registry).clone();
        for unit in &mut root.units {
            if let Unit::Operator(def) = &mut unit.node {
                tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
            }
        }
        for dep in &mut deps {
            for unit in &mut dep.units {
                if let Unit::Operator(def) = &mut unit.node {
                    tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
                }
            }
        }

        let dep_refs: Vec<&tla_core::ast::Module> = deps.iter().collect();
        let tir_callees =
            tla_eval::bytecode_vm::collect_bytecode_namespace_callees(&root, &dep_refs);
        let compiled = tla_eval::bytecode_vm::compile_operators_to_bytecode_full(
            &root,
            &dep_refs,
            &action_names,
            ctx.precomputed_constants(),
            Some(ctx.op_replacements()),
            Some(&tir_callees),
        );

        let stats_enabled = crate::check::debug::bytecode_vm_stats_enabled();
        let reason_logs = stats_enabled || crate::check::debug::debug_bytecode_vm();
        if reason_logs {
            eprintln!(
                "[bytecode-parallel] action compilation: {}/{} actions compiled ({} failed)",
                compiled.op_indices.len(),
                action_names.len(),
                compiled.failed.len(),
            );
            for (name, err) in &compiled.failed {
                eprintln!("[bytecode-parallel]   action skip {name}: {err}");
            }
        }

        if compiled.op_indices.is_empty() {
            return None;
        }

        // Transform action predicate bytecode into next-state function bytecode.
        // Rewrites `LoadPrime(x) + Eq` -> `StoreVar(x, expr)` so the JIT can
        // produce successor states. Mirrors sequential run_prepare.rs:606-638.
        let mut transformed_count = 0usize;
        let mut transformed = compiled;
        let action_entries: Vec<(String, u16)> = transformed
            .op_indices
            .iter()
            .map(|(name, &func_idx)| (name.clone(), func_idx))
            .collect();
        let action_entry_count = action_entries.len();
        transformed.op_indices.clear();
        for (name, func_idx) in action_entries {
            let Some(original_instructions) = transformed
                .chunk
                .functions
                .get(func_idx as usize)
                .map(|func| func.instructions.clone())
            else {
                continue;
            };

            match tla_tir::bytecode::action_transform::transform_action_to_next_state(
                &original_instructions,
            ) {
                tla_tir::bytecode::action_transform::ActionTransformOutcome::Transformed(
                    new_instructions,
                ) => match crate::check::model_checker::validate_next_state_action_chunk(
                    func_idx,
                    &new_instructions,
                    &transformed.chunk,
                    self.vars.len(),
                ) {
                    Ok(()) => {
                        if let Some(func) = transformed.chunk.functions.get_mut(func_idx as usize) {
                            func.instructions = new_instructions;
                        }
                        transformed.op_indices.insert(name.clone(), func_idx);
                        transformed_count += 1;
                        if reason_logs {
                            eprintln!(
                                "[bytecode-parallel]   action '{name}': transformed to next-state"
                            );
                        }
                    }
                    Err(reason) => {
                        transformed.failed.push((
                            name.clone(),
                            tla_tir::bytecode::CompileError::Unsupported(format!(
                                "unsafe next-state transform: {reason}"
                            )),
                        ));
                        if reason_logs {
                            eprintln!("[bytecode-parallel]   action '{name}': skipped ({reason})");
                        }
                    }
                },
                tla_tir::bytecode::action_transform::ActionTransformOutcome::NoRewrite => {
                    transformed.failed.push((
                        name.clone(),
                        tla_tir::bytecode::CompileError::Unsupported(
                            "no safe next-state rewrite found".to_string(),
                        ),
                    ));
                    if reason_logs {
                        eprintln!(
                                "[bytecode-parallel]   action '{name}': skipped (no prime assignment pattern found)"
                            );
                    }
                }
                tla_tir::bytecode::action_transform::ActionTransformOutcome::Unsafe(reason) => {
                    transformed.failed.push((
                        name.clone(),
                        tla_tir::bytecode::CompileError::Unsupported(format!(
                            "unsafe next-state transform: {reason}"
                        )),
                    ));
                    if reason_logs {
                        eprintln!("[bytecode-parallel]   action '{name}': skipped ({reason})");
                    }
                }
            }
        }
        if reason_logs {
            eprintln!(
                "[bytecode-parallel] action transform: {transformed_count}/{} actions -> next-state",
                action_entry_count,
            );
        }
        if !transformed.op_indices.is_empty() {
            Some(Arc::new(transformed))
        } else {
            None
        }
    }

    fn compile_jit_invariant_cache_for_workers(
        &self,
        bytecode: &Option<Arc<tla_eval::bytecode_vm::CompiledBytecode>>,
        initial_states: &InitialStates,
    ) -> Option<crate::parallel::SharedJitInvariantCache> {
        if !crate::check::debug::jit_enabled() {
            return None;
        }

        let bytecode = bytecode.as_ref()?;
        let stats_enabled = crate::check::debug::bytecode_vm_stats_enabled();
        let reason_logs_enabled = stats_enabled || crate::check::debug::debug_bytecode_vm();

        // Part of #3910: Try build_with_layout for native compound access when
        // we can infer layout from the first initial state.
        let state_layout = self.infer_state_layout_from_initial_states(initial_states);

        let build_result = if let Some(ref layout) = state_layout {
            JitInvariantCacheImpl::build_with_layout(&bytecode.chunk, &bytecode.op_indices, layout)
        } else {
            JitInvariantCacheImpl::build(&bytecode.chunk, &bytecode.op_indices)
        };

        match build_result {
            Ok(cache) => {
                let jit_count = cache.len();
                if jit_count == 0 {
                    return None;
                }
                if stats_enabled {
                    let layout_note = if state_layout.is_some() {
                        " (with compound layout)"
                    } else {
                        ""
                    };
                    eprintln!(
                        "[jit-parallel] compiled {}/{} bytecode invariants to native code{layout_note}",
                        jit_count,
                        bytecode.op_indices.len(),
                    );
                }
                Some(Arc::new(cache))
            }
            Err(error) => {
                if reason_logs_enabled {
                    eprintln!("[jit-parallel] JIT compilation failed: {error}");
                }
                None
            }
        }
    }

    /// Infer a `StateLayout` from the first initial state for JIT compound access.
    ///
    /// Returns `Some(layout)` only when at least one variable is compound (record,
    /// function, set, tuple, sequence). For all-scalar specs, `build()` and
    /// `build_with_layout()` produce identical results, so we skip the overhead.
    ///
    /// Part of #3910.
    fn infer_state_layout_from_initial_states(
        &self,
        initial_states: &InitialStates,
    ) -> Option<tla_jit_abi::StateLayout> {
        let values: Vec<&tla_value::Value> = match initial_states {
            InitialStates::Bulk(storage) if storage.len() > 0 => {
                storage.get_state(0).iter().collect()
            }
            InitialStates::Vec(states) if !states.is_empty() => {
                states[0].vars().map(|(_, v)| v).collect()
            }
            _ => return None,
        };

        let has_compound = values.iter().any(|v| {
            !matches!(
                v,
                tla_value::Value::SmallInt(_)
                    | tla_value::Value::Int(_)
                    | tla_value::Value::Bool(_)
            )
        });
        if !has_compound {
            return None;
        }

        let var_layouts: Vec<tla_jit_abi::VarLayout> = values
            .iter()
            .map(|v| tla_jit_runtime::infer_var_layout(v))
            .collect();
        Some(tla_jit_abi::StateLayout::new(var_layouts))
    }

    // Wave 11a (Part of #4267): `compile_jit_next_state_cache` removed
    // alongside `SharedJitNextStateCache`. The Cranelift JIT is being
    // deleted (Epic #4251); the parallel next-state dispatch fell
    // through to the tree-walk interpreter even when this cache was
    // populated, so the compilation path was dead weight.
}

#[cfg(test)]
#[path = "prepare_tests.rs"]
mod prepare_tests;
