// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pre-BFS preparation: constant binding, symmetry computation, VIEW validation,
//! invariant compilation, operator expansion, and action compilation.
//!
//! Extracted from `run.rs` to separate setup concerns from runtime dispatch
//! (Part of #2385). TLC keeps construction/init concerns in `ModelChecker` init
//! path; this module mirrors that boundary.

use super::super::api::{check_error_to_result, CheckResult, ResolvedSpec, INLINE_NEXT_NAME};
use super::super::check_error::CheckError;
use super::debug::debug_bytecode_vm;
#[cfg(debug_assertions)]
use super::debug::tla2_debug;
use super::mc_struct::ModelChecker;
use super::trace_detect::compute_uses_trace;
use crate::constants::bind_constants_from_config;
use crate::{ConfigCheckError, EvalCheckError};
use tla_core::ast::Module;
// Part of #4267 Gate 1 Batch C: collapse Cranelift-backed JIT type paths.
use tla_jit::bytecode_lower::JitInvariantCache as JitInvariantCacheImpl;

impl ModelChecker<'_> {
    /// Register an inline NEXT expression from a ResolvedSpec.
    ///
    /// Delegates CST lowering and OperatorDef construction to the shared
    /// `checker_ops::lower_inline_next`, then registers the result in both
    /// the module's op_defs and the evaluation context.
    pub fn register_inline_next(&mut self, resolved: &ResolvedSpec) -> Result<(), CheckError> {
        let op_def = match crate::checker_ops::lower_inline_next(
            resolved.next_node.as_ref(),
            self.ctx.var_registry(),
        ) {
            None => return Ok(()),
            Some(result) => result?,
        };

        // Register the operator in our definitions and evaluation context.
        self.module
            .op_defs
            .insert(INLINE_NEXT_NAME.to_string(), op_def.clone());
        self.ctx.define_op(INLINE_NEXT_NAME.to_string(), op_def);

        Ok(())
    }

    /// Validate and cache the VIEW operator name from the configuration.
    ///
    /// Delegates to `checker_ops::validate_view_operator` — the single shared
    /// implementation used by both sequential and parallel checkers (Part of #810).
    pub(super) fn validate_view(&mut self) {
        self.compiled.cached_view_name =
            crate::checker_ops::validate_view_operator(&self.ctx, self.config);
        self.refresh_liveness_mode();
    }

    /// Shared setup for BFS model checking: constant binding, symmetry, VIEW validation,
    /// config validation, invariant compilation, operator expansion, and action compilation.
    /// Returns the resolved `Next` operator name on success.
    ///
    /// Both `check_impl` and `check_with_resume` call this to avoid duplicating setup logic.
    /// Part of #1230: extracted from check_impl/check_with_resume to eliminate copy-paste.
    #[allow(clippy::result_large_err)]
    pub(super) fn prepare_bfs_common(&mut self) -> Result<String, CheckResult> {
        // Install ENABLED hook (adaptive/parallel checkers install in their entry points).
        crate::eval::set_enabled_hook(crate::enabled::eval_enabled_cp);

        // Bind constants from config before checking
        // Part of #2356/#2777: Route through check_error_to_result so
        // ExitRequested maps to LimitReached(Exit).
        if let Err(e) = bind_constants_from_config(&mut self.ctx, self.config) {
            return Err(check_error_to_result(
                EvalCheckError::Eval(e).into(),
                &self.stats,
            ));
        }

        // Pre-evaluate zero-arity constant-level operators (Part of #2364).
        // Mirrors TLC's SpecProcessor.processConstantDefns(): evaluate all zero-arg
        // operators that don't reference state variables ONCE, store the result in
        // SharedCtx for O(1) lookup during model checking. This eliminates per-reference
        // overhead (dep tracking, cache key hashing, context stripping) for constant ops
        // like RingOfNodes, Initiator, N in EWD998ChanID.
        super::precompute::precompute_constant_operators(&mut self.ctx);

        // Part of #2895: Promote env constants (CONSTANT declarations from model config)
        // to precomputed_constants for NameId-keyed O(1) lookup in eval_ident.
        // Constants in env are looked up via string-key HashMap::get; moving them to
        // precomputed_constants (NameId key) eliminates string hashing on the fast path.
        // Only promotes non-state-variable entries (state vars stay in state_env).
        super::precompute::promote_env_constants_to_precomputed(&mut self.ctx);
        // Part of #3961: Build ident resolution hints for eval_ident fast-path dispatch.
        super::precompute::build_ident_hints(&mut self.ctx);

        // Part of #4251 Stream 5: populate the TIR partial-evaluation
        // ConstantEnv from the authoritative precomputed_constants map now
        // that all CONSTANT bindings (from .cfg and --constant overrides)
        // have been resolved. The env is attached to every TirProgram built
        // during this run; partial-eval substitution runs at TIR preprocess
        // time only when `TLA2_PARTIAL_EVAL=1` / `--partial-eval` is set.
        if let Some(tir_parity) = self.tir_parity.as_mut() {
            let mut env = tla_tir::analysis::ConstantEnv::new();
            for (name_id, value) in self.ctx.precomputed_constants().iter() {
                env.bind(*name_id, value.clone());
            }
            tir_parity.set_partial_eval_env(env);
        }

        // Compute symmetry permutations now that constants are bound.
        // Two paths: explicit SYMMETRY config, or auto-detection from model value sets.
        if self.symmetry.perms.is_empty() && self.config.symmetry.is_some() {
            self.symmetry.perms =
                super::symmetry_perms::compute_symmetry_perms(&self.ctx, self.config)
                    .map_err(|e| check_error_to_result(e, &self.stats))?;
            // Extract group names from config for statistics.
            self.symmetry.group_names =
                super::symmetry_detect::detect_symmetric_model_value_sets(self.config)
                    .into_iter()
                    .map(|(name, _)| name)
                    .collect();
            self.symmetry.auto_detected = false;
            self.symmetry.mvperms = self // #358: MVPerm for O(1) model value lookup
                .symmetry
                .perms
                .iter()
                .map(crate::value::MVPerm::from_func_value)
                .collect::<Result<Vec<_>, _>>()
                // Part of #2356/#2777: Route through check_error_to_result so
                // ExitRequested maps to LimitReached(Exit).
                .map_err(|e| check_error_to_result(EvalCheckError::Eval(e).into(), &self.stats))?;
            self.refresh_liveness_mode();
        } else if self.symmetry.perms.is_empty() && self.config.symmetry.is_none() {
            // Auto-detect symmetry from model value sets (TLA2_AUTO_SYMMETRY=1).
            let (auto_perms, group_names) =
                super::symmetry_detect::auto_detect_symmetry_perms(&self.ctx, self.config);
            if !auto_perms.is_empty() {
                #[cfg(debug_assertions)]
                if tla2_debug() {
                    eprintln!(
                        "Auto-detected symmetry: {} permutations from {} group(s): {:?}",
                        auto_perms.len(),
                        group_names.len(),
                        group_names,
                    );
                }
                self.symmetry.perms = auto_perms;
                self.symmetry.group_names = group_names;
                self.symmetry.auto_detected = true;
                self.symmetry.mvperms = self
                    .symmetry
                    .perms
                    .iter()
                    .map(crate::value::MVPerm::from_func_value)
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|e| {
                        check_error_to_result(EvalCheckError::Eval(e).into(), &self.stats)
                    })?;
                self.refresh_liveness_mode();
            }
        }

        // Part of #2227: Only warn/reject for genuine temporal properties.
        // Pure safety properties (`[]P`) are handled by the safety-temporal fast
        // path and work correctly in notrace mode even with symmetry.
        // Check both explicit and auto-detected symmetry.
        let has_symmetry = !self.symmetry.perms.is_empty();
        let has_genuine_temporal = has_symmetry
            && !self.config.properties.is_empty()
            && crate::checker_ops::any_property_requires_liveness_checker(
                &self.ctx,
                &self.module.op_defs,
                &self.config.properties,
            );

        // Part of #1963: Warn when SYMMETRY and genuine liveness properties are both present.
        if has_genuine_temporal {
            eprintln!(
                "Warning: Declaring symmetry during liveness checking is dangerous. \
                 Please check liveness without symmetry defined."
            );
        }

        // Part of #2200/#3222: SYMMETRY + genuine temporal properties require
        // full-state storage for witness reconstruction because inline liveness
        // recording is disabled under symmetry. TLC warns but continues because
        // it always stores full states, so match TLC by auto-upgrading here.
        if has_genuine_temporal && !self.state_storage.store_full_states {
            self.set_store_states(true);
        }

        // Validate and cache VIEW operator name now that constants are bound
        if self.compiled.cached_view_name.is_none() && self.config.view.is_some() {
            self.validate_view();
        }

        // Validate next_name
        let raw_next_name = match &self.config.next {
            Some(name) => name.clone(),
            None => {
                return Err(CheckResult::from_error(
                    ConfigCheckError::MissingNext.into(),
                    self.stats.clone(),
                ))
            }
        };

        // Cache the raw config alias for trace reconstruction and user-facing labels,
        // but resolve replacements for the actual operator body we execute/compile.
        self.trace.cached_next_name = Some(raw_next_name.clone());
        let resolved = self.ctx.resolve_op_name(&raw_next_name).to_string();
        self.trace.cached_resolved_next_name = Some(resolved);

        // Part of #254: Set initial TLC level for TLCGet("level") - TLC uses 1-based indexing.
        // Set level=1 before any expression evaluation (including constraint extraction)
        // to avoid side effects (like PrintT) seeing level=0. Later phases update this
        // to the correct depth during BFS exploration.
        self.ctx.set_tlc_level(1);

        // Validate config operators: existence, arity, level, and variables.
        // Part of #2573: TLC validates all config elements at setup time
        // (SpecProcessor.java:processConfigInvariants/Properties/Constraints).
        self.validate_config_ops()?;

        let next_name = self.ctx.resolve_op_name(&raw_next_name).to_string();

        // Classify PROPERTY entries into BFS-phase checking buckets (#2332, #2670, #2740).
        let classification = crate::checker_ops::classify_property_safety_parts(
            &self.ctx,
            &self.config.properties,
            &self.module.op_defs,
        );
        self.compiled.promoted_property_invariants = classification.promoted_invariant_properties;
        self.compiled.state_property_violation_names = classification.state_violation_properties;
        self.compiled.eval_implied_actions = classification.eval_implied_actions;
        self.compiled.eval_state_invariants = classification.eval_state_invariants;
        self.compiled.promoted_implied_action_properties =
            classification.promoted_action_properties;
        self.compiled.property_init_predicates = classification.init_predicates;

        // Part of #1121: Shared alias-aware trace detection (invariants + constraints + action_constraints).
        self.compiled.uses_trace = compute_uses_trace(self.config, &self.module.op_defs)
            .map_err(|e| CheckResult::from_error(e, self.stats.clone()))?;

        // Pre-expand operator references in the Next action body (Part of #207).
        // Delegates to checker_ops::expand_operator_body (Part of #810).
        if let Some(next_def) = self.module.op_defs.get(&next_name).cloned() {
            let expanded_def = crate::checker_ops::expand_operator_body(&self.ctx, &next_def);
            self.module.op_defs.insert(next_name.clone(), expanded_def);
        }

        // Part of #3100: Discover split-action metadata for liveness provenance.
        // Successor generation no longer uses compiled split actions, but inline
        // liveness still needs the split action names/bindings to match action
        // predicates against BFS actions.
        if {
            static ACTION_SPLIT_ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            *ACTION_SPLIT_ENABLED.get_or_init(|| std::env::var("TLA2_NO_ACTION_SPLIT").is_err())
        } {
            if let Some(next_def) = self.module.op_defs.get(&next_name) {
                match crate::action_instance::split_action_instances(&self.ctx, &next_def.body) {
                    Ok(instances) if instances.len() > 1 => {
                        #[cfg(debug_assertions)]
                        if tla2_debug() {
                            eprintln!(
                                "[#3100] Action split: {} instances recorded for liveness provenance",
                                instances.len()
                            );
                        }
                        let meta: Vec<_> = instances
                            .iter()
                            .map(|inst| super::mc_struct::ActionInstanceMeta {
                                name: inst.name.clone(),
                                bindings: inst.bindings.clone(),
                                expr: Some(inst.expr.clone()),
                            })
                            .collect();
                        self.compiled.split_action_meta = Some(meta);
                    }
                    Ok(_instances) =>
                    {
                        #[cfg(debug_assertions)]
                        if tla2_debug() {
                            eprintln!(
                                "[#1150] Action split: only {} instance(s), using monolithic",
                                _instances.len()
                            );
                        }
                    }
                    Err(_e) =>
                    {
                        #[cfg(debug_assertions)]
                        if tla2_debug() {
                            eprintln!("[#1150] Action split failed, using monolithic: {_e:?}");
                        }
                    }
                }
            }
        }

        // TLC_LIVE_FORMULA_TAUTOLOGY pre-check (EC 2253, #2215).
        if let Some(result) = self.check_properties_for_tautologies() {
            return Err(result);
        }

        // Pre-analyze ACTION_CONSTRAINTs for variable dependencies.
        // This enables skipping constraint evaluation when referenced variables
        // are unchanged between current and successor states.
        if !self.config.action_constraints.is_empty() {
            self.compiled.action_constraint_analysis =
                Some(crate::checker_ops::ActionConstraintAnalysis::build(
                    &self.ctx,
                    &self.config.action_constraints,
                ));
        }

        // Detect PlusCal pc-dispatch pattern for action guard hoisting.
        // When all disjuncts of Next are guarded by `pc = "label"`, the BFS
        // loop can skip evaluating actions whose pc guard doesn't match the
        // current state, avoiding wasted work in PlusCal-generated specs.
        if let Some(next_def) = self.module.op_defs.get(&next_name) {
            let registry = self.ctx.var_registry().clone();
            if let Some(table) = crate::checker_ops::pc_dispatch::detect_pc_dispatch(
                next_def,
                &self.module.vars,
                &registry,
                &self.ctx,
            ) {
                #[cfg(debug_assertions)]
                if tla2_debug() {
                    eprintln!(
                        "[pc-dispatch] Detected PlusCal pattern: {} actions, {} distinct pc values",
                        table.total_actions,
                        table.dispatch.len(),
                    );
                }
                self.compiled.pc_var_idx = Some(table.pc_var_idx);
                self.compiled.pc_dispatch = Some(table);
            } else {
                // Part of #3805: Multi-process PlusCal guard hoisting.
                // When the full dispatch table can't be built (multi-process specs
                // use `pc[self] = "label"` instead of `pc = "label"`), we can still
                // enable guard hoisting by detecting the pc variable and verifying
                // the spec has pc guards. The enumerator handles multi-process pc
                // values (Value::Func) by looking up `self` in the binding chain.
                if let Some(pc_var_idx) = registry.get("pc") {
                    if crate::checker_ops::pc_dispatch::spec_has_pc_guards(
                        next_def, &self.ctx,
                    ) {
                        #[cfg(debug_assertions)]
                        if tla2_debug() {
                            eprintln!(
                                "[pc-dispatch] Detected multi-process PlusCal pc guards (pc_var_idx={:?})",
                                pc_var_idx,
                            );
                        }
                        self.compiled.pc_var_idx = Some(pc_var_idx);
                    }
                }
            }
        }

        // Part of #3578: Compile invariant operators to bytecode for VM fast path.
        // NOTE: Profiling shows the bytecode VM is currently ~2.6x slower than
        // tree-walking with TIR cache for invariant evaluation (EWD998Small:
        // 27.1s bytecode vs 10.3s tree-walk). The per-state VM setup overhead
        // (BytecodeVm::from_state_env) exceeds the benefit of avoiding AST
        // traversal. Skip bytecode compilation when TIR eval owns invariants.
        //
        // Previously JIT forced bytecode compilation here, but the compiled
        // bytecode activates the slow bytecode VM path for ALL invariant evals.
        // Since JIT invariant native code currently has 0% hit rate (all
        // FallbackNeeded), this caused a 33% regression. JIT bytecode
        // compilation is now deferred to the JIT compilation phase.
        let tir_blocks_bytecode_vm = self
            .tir_parity
            .as_ref()
            .is_some_and(super::tir_parity::TirParityState::is_eval_mode);
        if tla_eval::tir::bytecode_vm_enabled() && !tir_blocks_bytecode_vm {
            self.compile_invariant_bytecode();
        }

        // Part of #3910: Compile action operators to bytecode for JIT next-state dispatch.
        // This is separate from invariant bytecode because actions use StoreVar opcodes
        // for primed variables, and the JitNextStateCache requires action-specific bytecode.
        // Also needed when LLVM2 is enabled (#4190), since the LLVM2 pipeline takes
        // BytecodeFunction as input.
        {
            let need_action_bytecode = crate::check::debug::jit_enabled();
            #[cfg(feature = "llvm2")]
            let need_action_bytecode = need_action_bytecode
                || super::llvm2_dispatch::should_use_llvm2();
            if need_action_bytecode {
                self.compile_action_bytecode();
            }
        }

        // Part of #3850: Initialize tiered JIT manager after action splitting
        // so we know the action count. The tier manager tracks per-action
        // compilation tiers and makes promotion decisions based on evaluation
        // frequency.
        if crate::check::debug::jit_enabled() {
            self.initialize_tier_manager();
        }

        // Part of #4118: Initialize LLVM2 native compilation cache.
        // Must be called after compile_action_bytecode() so bytecode is available.
        // Only activates when TLA2_LLVM2=1 and llc is on PATH.
        self.initialize_llvm2_cache();

        Ok(next_name)
    }

    /// Compile invariant operators to bytecode for VM-accelerated evaluation.
    ///
    /// Part of #3578: Attempts bytecode compilation for all configured invariant
    /// names. The result is stored in `self.bytecode` and consulted during
    /// `check_invariants_array` to bypass tree-walking evaluation.
    fn compile_invariant_bytecode(&mut self) {
        if self.config.invariants.is_empty() {
            return;
        }

        // Get module references from tir_parity if available, otherwise use
        // the root module from the context.
        let (mut root, mut deps) = if let Some(tir) = &self.tir_parity {
            let (root, deps) = tir.clone_modules();
            (root, deps)
        } else {
            return;
        };

        // The cloned module's operator bodies contain Expr::Ident for state
        // variables (state var resolution in checker_setup.rs only applies to
        // the op_defs HashMap, not the module AST). The TIR lowerer needs
        // Expr::StateVar nodes to emit LoadVar opcodes; without this, variable
        // references lower to TirNameKind::Ident and the bytecode compiler
        // emits LoadConst with a string name instead of LoadVar with a
        // VarRegistry index — causing the VM to evaluate against wrong values.
        use tla_core::ast::Unit;
        let registry = self.ctx.var_registry().clone();
        for unit in &mut root.units {
            if let Unit::Operator(def) = &mut unit.node {
                tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
            }
        }
        // Also resolve state vars in dependency modules — invariants defined
        // in EXTENDS'd base specs reference the same state variables.
        for dep in &mut deps {
            for unit in &mut dep.units {
                if let Unit::Operator(def) = &mut unit.node {
                    tla_eval::state_var::resolve_state_vars_in_op_def(def, &registry);
                }
            }
        }

        // Diagnostic: show what modules and operators are available for compilation.
        if super::debug::bytecode_vm_stats_enabled() {
            let root_ops: Vec<_> = root
                .units
                .iter()
                .filter_map(|u| {
                    if let Unit::Operator(def) = &u.node {
                        Some(def.name.node.as_str())
                    } else {
                        None
                    }
                })
                .collect();
            eprintln!(
                "[bytecode] root module '{}': {} operators: {:?}",
                root.name.node,
                root_ops.len(),
                &root_ops[..root_ops.len().min(10)]
            );
            for (i, dep) in deps.iter().enumerate() {
                let dep_ops: Vec<_> = dep
                    .units
                    .iter()
                    .filter_map(|u| {
                        if let Unit::Operator(def) = &u.node {
                            Some(def.name.node.as_str())
                        } else {
                            None
                        }
                    })
                    .collect();
                eprintln!(
                    "[bytecode] dep[{i}] module '{}': {} operators: {:?}",
                    dep.name.node,
                    dep_ops.len(),
                    &dep_ops[..dep_ops.len().min(10)]
                );
            }
        }

        let dep_refs: Vec<&Module> = deps.iter().collect();
        let tir_callees =
            tla_eval::bytecode_vm::collect_bytecode_namespace_callees(&root, &dep_refs);
        let compiled = tla_eval::bytecode_vm::compile_operators_to_bytecode_full(
            &root,
            &dep_refs,
            &self.config.invariants,
            self.ctx.precomputed_constants(),
            Some(self.ctx.op_replacements()),
            Some(&tir_callees),
        );

        // Keep the rollout measurements behind the stats flag, but allow
        // release-mode reason logging via TLA2_DEBUG_BYTECODE_VM=1.
        let stats_enabled = super::debug::bytecode_vm_stats_enabled();
        let reason_logs_enabled = stats_enabled || debug_bytecode_vm();
        if stats_enabled {
            eprintln!(
                "[bytecode] compiled {}/{} invariants ({} failed)",
                compiled.op_indices.len(),
                self.config.invariants.len(),
                compiled.failed.len(),
            );
        }
        if reason_logs_enabled {
            for (name, err) in &compiled.failed {
                eprintln!("[bytecode]   skip {name}: {err}");
            }
        }
        #[cfg(debug_assertions)]
        if super::debug::tla2_debug() {
            eprintln!(
                "[#3578] Bytecode VM: compiled {}/{} invariants ({} failed)",
                compiled.op_indices.len(),
                self.config.invariants.len(),
                compiled.failed.len(),
            );
            for (name, err) in &compiled.failed {
                eprintln!("[#3578]   skip {name}: {err}");
            }
        }
        if !compiled.op_indices.is_empty() {
            // Part of #3582: JIT-compile eligible bytecode invariants to native code.
            if crate::check::debug::jit_enabled() {
                match JitInvariantCacheImpl::build(
                    &compiled.chunk,
                    &compiled.op_indices,
                ) {
                    Ok(cache) => {
                        let jit_count = cache.len();
                        if jit_count > 0 {
                            if stats_enabled {
                                eprintln!(
                                    "[jit] compiled {}/{} bytecode invariants to native code",
                                    jit_count,
                                    compiled.op_indices.len(),
                                );
                            }
                            let all = cache.covers_all(&self.config.invariants);
                            self.jit_all_compiled = all;
                            self.jit_resolved_fns = if all {
                                cache.resolve_ordered(&self.config.invariants)
                            } else {
                                None
                            };
                            self.jit_cache = Some(cache);
                        }
                    }
                    Err(e) => {
                        if reason_logs_enabled {
                            eprintln!("[jit] JIT compilation failed: {e}");
                        }
                    }
                }
            }

            self.bytecode = Some(compiled);
        }
    }

    /// Compile action operators to bytecode for JIT next-state dispatch.
    ///
    /// Part of #3910: The JitNextStateCache needs bytecode for split-action operators
    /// (like "Send", "Receive"), not invariant operators. This method compiles the
    /// action operators discovered by split_action_instances into bytecode that the
    /// Cranelift JIT can lower to native code.
    ///
    /// No-op when:
    /// - No split_action_meta (monolithic single-action specs)
    /// - tir_parity modules unavailable (no AST to compile from)
    fn compile_action_bytecode(&mut self) {
        if self.compiled.split_action_meta.as_ref().map_or(true, |m| m.is_empty()) {
            return;
        }

        // Collect unique action operator names from BOTH sources:
        // 1. split_action_meta (leaf actions: "RecvMsg", "PassToken", etc.)
        // 2. coverage.actions (detected actions: "System", "Environment", etc.)
        //
        // We need both because the JIT dispatch uses detected action names
        // (from run_gen.rs per-action loop) while deeper split actions may
        // also be referenced. Having both ensures cache hits regardless of
        // which naming level the dispatch uses.
        //
        // Part of: JIT name mismatch fix — detected vs split action names.
        let mut name_set = std::collections::HashSet::new();
        if let Some(meta) = self.compiled.split_action_meta.as_ref() {
            for m in meta {
                if let Some(name) = &m.name {
                    name_set.insert(name.clone());
                }
            }
        }
        for action in &self.coverage.actions {
            name_set.insert(action.name.clone());
        }
        let action_names: Vec<String> = name_set.into_iter().collect();
        if action_names.is_empty() {
            return;
        }

        // Get module references (same source as invariant bytecode compilation).
        let (mut root, mut deps) = if let Some(tir) = &self.tir_parity {
            let (root, deps) = tir.clone_modules();
            (root, deps)
        } else {
            return;
        };

        // Resolve state vars in the AST (required for LoadVar/StoreVar opcodes).
        use tla_core::ast::Unit;
        let registry = self.ctx.var_registry().clone();
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
            self.ctx.precomputed_constants(),
            Some(self.ctx.op_replacements()),
            Some(&tir_callees),
        );

        let stats_enabled = super::debug::bytecode_vm_stats_enabled();
        let reason_logs = stats_enabled || super::debug::debug_bytecode_vm();
        if reason_logs {
            eprintln!(
                "[bytecode] action compilation: {}/{} actions compiled ({} failed)",
                compiled.op_indices.len(),
                action_names.len(),
                compiled.failed.len(),
            );
            for (name, err) in &compiled.failed {
                eprintln!("[bytecode]   action skip {name}: {err}");
            }
        }

        if compiled.op_indices.is_empty() {
            return;
        }

        // Part of #3910: Transform action predicate bytecode into next-state
        // function bytecode. Rewrites `LoadPrime(x) + Eq` → `StoreVar(x, expr)`
        // so the JIT next-state cache can produce successor states.
        let mut transformed_count = 0usize;
        let mut transformed = compiled;
        for (name, &func_idx) in &transformed.op_indices {
            if let Some(func) = transformed.chunk.functions.get_mut(func_idx as usize) {
                if let Some(new_instructions) =
                    tla_tir::bytecode::action_transform::transform_action_to_next_state(
                        &func.instructions,
                    )
                {
                    func.instructions = new_instructions;
                    transformed_count += 1;
                    if reason_logs {
                        eprintln!("[bytecode]   action '{name}': transformed to next-state");
                    }
                } else if reason_logs {
                    eprintln!(
                        "[bytecode]   action '{name}': no prime assignment pattern found"
                    );
                }
            }
        }
        if reason_logs {
            eprintln!(
                "[bytecode] action transform: {transformed_count}/{} actions → next-state",
                transformed.op_indices.len(),
            );
        }
        if transformed_count > 0 {
            self.action_bytecode = Some(transformed);
        }
    }

    /// Infer and store a `StateLayout` for flat i64 state representation.
    ///
    /// Called after init state solving when we have a concrete initial state
    /// to infer variable types from. The inferred layout maps each state
    /// variable to a contiguous region of i64 slots, enabling `FlatState`
    /// conversions for JIT-compiled transition functions and invariant checks.
    ///
    /// No-op when no initial states are available.
    ///
    /// Part of #3986: Wire FlatState into BFS path.
    pub(in crate::check) fn infer_flat_state_layout(
        &mut self,
        first_init_state: &crate::state::ArrayState,
    ) {
        let registry = self.ctx.var_registry().clone();
        let layout = crate::state::infer_layout(first_init_state, &registry);

        let flat_bytes = crate::state::flat_state_bytes(&layout);
        let stats_enabled = super::debug::bytecode_vm_stats_enabled();
        if stats_enabled {
            eprintln!(
                "[flat_state] inferred layout: {} vars, {} total slots, {} bytes/state, \
                 all_scalar={}, trivial={}, fully_flat={}, has_dynamic={}",
                layout.var_count(),
                layout.total_slots(),
                flat_bytes,
                layout.is_all_scalar(),
                layout.is_trivial(),
                layout.is_fully_flat(),
                layout.has_dynamic_vars(),
            );
        }

        let layout_arc = std::sync::Arc::new(layout);
        // Part of #3986: Create the FlatBfsBridge alongside the layout.
        let bridge = crate::state::FlatBfsBridge::new(std::sync::Arc::clone(&layout_arc));

        if stats_enabled {
            eprintln!(
                "[flat_state] bridge: fully_flat={}, num_slots={}, bytes_per_state={}",
                bridge.is_fully_flat(),
                bridge.num_slots(),
                bridge.bytes_per_state(),
            );
        }

        self.flat_state_layout = Some(layout_arc);
        // Part of #4126: Create adapter for Tier 0 interpreter sandwich.
        // Verify the first initial state roundtrips correctly through the flat
        // representation. This catches specs with string/model-value variables
        // that layout inference classifies as Scalar but the i64 roundtrip
        // would corrupt (e.g., "black" → 0 → SmallInt(0)).
        let mut adapter = crate::state::FlatBfsAdapter::new(bridge.clone());
        let mut verify_state = first_init_state.clone();
        let roundtrip_ok = adapter.verify_roundtrip(&mut verify_state, &registry);
        // Log roundtrip result: always log on failure (auto-detect may have
        // wanted to activate), or when stats are enabled. Include a diagnostic
        // summary on failure so the FAIL message is actionable (issue #4275).
        if stats_enabled || !roundtrip_ok {
            if roundtrip_ok {
                eprintln!("[flat_state] adapter roundtrip verification: PASS");
            } else {
                let detail = adapter
                    .diagnose_roundtrip(first_init_state, &registry)
                    .unwrap_or_else(|| "no detail available".to_string());
                eprintln!(
                    "[flat_state] adapter roundtrip verification: FAIL ({detail}) — flat BFS will fall back to Owned entries",
                );
            }
        }
        self.flat_bfs_adapter = Some(adapter);
        self.flat_bfs_bridge = Some(bridge);

        // Part of #3986: Detect if flat i64 state can be the primary BFS representation.
        // Conditions: all vars scalar, roundtrip verified, no VIEW, no SYMMETRY.
        //
        // Part of #4298: Gate activation on `store_full_states == false`. Same
        // rationale as the #4281 fix for `jit_compiled_fp_active`: in full-state
        // mode the `seen` HashMap and `seen_fps` set are already populated with
        // FP64 fingerprints by `init_states_full_state()` before layout inference
        // runs here. If we now flip to flat-primary, successors would be
        // fingerprinted via `FlatState::fingerprint_compiled()` (xxh3 on raw i64
        // buffer) while init states remain under FP64 — the same state value
        // (e.g., stuttering `x=0`) gets two different fingerprints, inflating
        // the distinct-state count and breaking parity with TLC (e.g.,
        // `system_loop_no_fair_2w`).
        {
            let all_scalar = self
                .flat_state_layout
                .as_ref()
                .is_some_and(|l| l.is_all_scalar());
            self.flat_state_primary = roundtrip_ok
                && all_scalar
                && self.compiled.cached_view_name.is_none()
                && self.symmetry.perms.is_empty()
                && !self.state_storage.store_full_states;
            if stats_enabled && self.flat_state_primary {
                eprintln!(
                    "[flat_state] flat_state_primary=true: all vars scalar, \
                     no VIEW, no SYMMETRY — flat i64 is primary BFS representation",
                );
            }
        }
    }

    /// Infer and store a `StateLayout` from a wavefront of initial states.
    ///
    /// Like `infer_flat_state_layout` but examines multiple states for
    /// robustness. If variable shapes disagree across states, the
    /// conflicting variable falls back to `Dynamic`.
    ///
    /// Part of #3986: Layout inference from first wavefront (~1000 states).
    pub(in crate::check) fn infer_flat_state_layout_from_wavefront(
        &mut self,
        states: &[crate::state::ArrayState],
    ) {
        if states.is_empty() {
            return;
        }

        let registry = self.ctx.var_registry().clone();
        let layout = crate::state::infer_layout_from_wavefront(states, &registry);

        let flat_bytes = crate::state::flat_state_bytes(&layout);
        let stats_enabled = super::debug::bytecode_vm_stats_enabled();
        if stats_enabled {
            eprintln!(
                "[flat_state] wavefront layout ({} states): {} vars, {} total slots, {} bytes/state, \
                 all_scalar={}, trivial={}, fully_flat={}, has_dynamic={}",
                states.len(),
                layout.var_count(),
                layout.total_slots(),
                flat_bytes,
                layout.is_all_scalar(),
                layout.is_trivial(),
                layout.is_fully_flat(),
                layout.has_dynamic_vars(),
            );
        }

        let layout_arc = std::sync::Arc::new(layout);
        let bridge = crate::state::FlatBfsBridge::new(std::sync::Arc::clone(&layout_arc));

        if stats_enabled {
            eprintln!(
                "[flat_state] wavefront bridge: fully_flat={}, num_slots={}, bytes_per_state={}",
                bridge.is_fully_flat(),
                bridge.num_slots(),
                bridge.bytes_per_state(),
            );
        }

        self.flat_state_layout = Some(layout_arc.clone());
        // Part of #4126: Create adapter for Tier 0 interpreter sandwich.
        let mut adapter = crate::state::FlatBfsAdapter::new(bridge.clone());
        let mut verify_state = states[0].clone();
        let roundtrip_ok = adapter.verify_roundtrip(&mut verify_state, &registry);
        if stats_enabled || !roundtrip_ok {
            if roundtrip_ok {
                eprintln!("[flat_state] wavefront adapter roundtrip verification: PASS");
            } else {
                let detail = adapter
                    .diagnose_roundtrip(&states[0], &registry)
                    .unwrap_or_else(|| "no detail available".to_string());
                eprintln!(
                    "[flat_state] wavefront adapter roundtrip verification: FAIL ({detail}) — flat BFS will fall back to Owned entries",
                );
            }
        }
        self.flat_bfs_adapter = Some(adapter);
        self.flat_bfs_bridge = Some(bridge);

        // Part of #3986: Detect if flat i64 state can be the primary BFS representation.
        // Part of #4298: Gate on `!store_full_states` — see the single-state
        // `infer_flat_state_layout` setter above for the full rationale. Flipping
        // the fingerprint algorithm after init states are already stored in the
        // `seen`/`seen_fps` domain inflates distinct-state counts (same state
        // value ends up with both an FP64 init fingerprint and an xxh3 successor
        // fingerprint).
        {
            self.flat_state_primary = roundtrip_ok
                && layout_arc.is_all_scalar()
                && self.compiled.cached_view_name.is_none()
                && self.symmetry.perms.is_empty()
                && !self.state_storage.store_full_states;
            if stats_enabled && self.flat_state_primary {
                eprintln!(
                    "[flat_state] flat_state_primary=true (wavefront): all vars scalar, \
                     no VIEW, no SYMMETRY — flat i64 is primary BFS representation",
                );
            }
        }
    }

    /// Get the flat state layout, if inferred.
    ///
    /// Returns `None` before `infer_flat_state_layout` has been called.
    ///
    /// Part of #3986: Wire FlatState into BFS path.
    #[must_use]
    #[allow(dead_code)]
    pub(in crate::check) fn flat_state_layout(
        &self,
    ) -> Option<&std::sync::Arc<crate::state::StateLayout>> {
        self.flat_state_layout.as_ref()
    }

    /// Get the FlatBfsBridge, if created.
    ///
    /// Returns `None` before `infer_flat_state_layout` has been called.
    /// The bridge provides cheap `ArrayState <-> FlatState` conversions
    /// and fingerprint bridging at the BFS boundary.
    ///
    /// Part of #3986: Wire FlatState into BFS engine.
    #[must_use]
    #[allow(dead_code)]
    pub(in crate::check) fn flat_bfs_bridge(&self) -> Option<&crate::state::FlatBfsBridge> {
        self.flat_bfs_bridge.as_ref()
    }

    /// Get a clone of the FlatBfsAdapter, if created.
    ///
    /// Returns `None` before `infer_flat_state_layout` has been called.
    /// The adapter wraps the bridge with BFS-specific convenience methods
    /// for the interpreter sandwich (FlatState -> ArrayState -> eval ->
    /// ArrayState -> FlatState).
    ///
    /// Returns a clone because adapters are per-worker (mutable stats).
    ///
    /// Part of #4126: FlatState as native BFS representation (Phase E).
    #[must_use]
    #[allow(dead_code)]
    pub(in crate::check) fn flat_bfs_adapter(&self) -> Option<crate::state::FlatBfsAdapter> {
        self.flat_bfs_adapter.clone()
    }

    /// Determine whether flat BFS should be used for this run.
    ///
    /// The decision hierarchy is:
    /// 1. `Config::use_flat_state = Some(false)` → disabled (programmatic override)
    /// 2. `TLA2_NO_FLAT_BFS=1` → disabled (env var override)
    /// 3. `Config::use_flat_state = Some(true)` → enabled if adapter ready
    /// 4. `TLA2_FLAT_BFS=1` → enabled if adapter ready (force-enable env var)
    /// 5. Auto-detect: enabled when adapter is present, roundtrip verified,
    ///    AND the layout is fully flat (all vars are scalar/IntArray/Record —
    ///    no Dynamic vars requiring ArrayState fallback).
    ///
    /// The auto-detect path (5) is the default for specs where all state
    /// variables are i64-representable (Int, Bool, ModelValue). This removes
    /// the need for `TLA2_FLAT_BFS=1` on typical scalar specs.
    ///
    /// Part of #4126: Auto-detect flat BFS for scalar specs.
    #[must_use]
    pub(in crate::check) fn should_use_flat_bfs(&self) -> bool {
        // 1. Programmatic force-disable
        if self.config.use_flat_state == Some(false) {
            return false;
        }
        // 2. Env var force-disable
        if crate::check::debug::flat_bfs_disabled() {
            return false;
        }

        let adapter_ready = self
            .flat_bfs_adapter
            .as_ref()
            .is_some_and(|a| a.roundtrip_verified());

        // 3. Programmatic force-enable
        if self.config.use_flat_state == Some(true) {
            return adapter_ready;
        }
        // 4. Env var force-enable
        if crate::check::debug::flat_bfs_enabled() {
            return adapter_ready;
        }

        // 5. Auto-detect: enable when fully flat and roundtrip verified
        if !adapter_ready {
            return false;
        }
        self.flat_bfs_adapter
            .as_ref()
            .is_some_and(|a| a.is_fully_flat())
    }

    /// Whether flat i64 state is the primary BFS representation for this run.
    ///
    /// True when ALL of:
    /// - All spec variables are scalar (Int/Bool) — `layout.is_all_scalar()`
    /// - Roundtrip verification passed
    /// - No VIEW expression configured
    /// - No SYMMETRY reduction active
    ///
    /// When true, the BFS hot path can store states as contiguous `[i64]`
    /// buffers and pass them directly to JIT-compiled transition functions
    /// without flatten/unflatten overhead.
    ///
    /// Part of #3986: Flat i64 state as primary BFS representation.
    #[must_use]
    #[allow(dead_code)]
    pub(in crate::check) fn is_flat_state_primary(&self) -> bool {
        self.flat_state_primary
    }

    /// Upgrade the JIT invariant cache with compound layout information.
    ///
    /// Called after init state solving when we have a concrete initial state
    /// to infer variable types from. The initial `JitInvariantCache::build()`
    /// has no layout info, so compound-type variable accesses (records,
    /// functions, tuples) fall back to the interpreter. Rebuilding with
    /// `build_with_layout()` enables native compound access in JIT-compiled
    /// invariants.
    ///
    /// No-op when:
    /// - JIT feature is disabled
    /// - No JIT cache exists (no invariants were JIT-compiled)
    /// - No bytecode exists (no invariants were bytecode-compiled)
    /// - The initial state has no compound variables (layout upgrade is unnecessary)
    ///
    /// Part of #3910: JIT invariant layout upgrade for native compound access.
    pub(in crate::check) fn upgrade_jit_cache_with_layout(
        &mut self,
        first_init_state: &crate::state::ArrayState,
    ) {
        // Infer layout from the initial state's values.
        // This is needed for BOTH invariant JIT and next-state JIT,
        // so compute it even when jit_cache (invariant) is None.
        let compact_values = first_init_state.values();
        let has_compound = compact_values
            .iter()
            .any(|cv| !cv.is_int() && !cv.is_bool());
        if !has_compound {
            // All variables are scalar — layout offers no benefit.
            return;
        }

        let var_layouts: Vec<tla_jit_abi::VarLayout> = compact_values
            .iter()
            .map(|cv| {
                let value = tla_value::Value::from(cv);
                tla_jit_runtime::infer_var_layout(&value)
            })
            .collect();
        let state_layout = tla_jit_abi::StateLayout::new(var_layouts);

        // Store layout for next-state JIT compilation (Part of #3958).
        self.jit_state_layout = Some(state_layout.clone());

        // Upgrade the invariant JIT cache if it exists.
        let Some(ref bytecode) = self.bytecode else {
            return;
        };
        if self.jit_cache.is_none() {
            return;
        }

        let stats_enabled = super::debug::bytecode_vm_stats_enabled();
        match JitInvariantCacheImpl::build_with_layout(
            &bytecode.chunk,
            &bytecode.op_indices,
            &state_layout,
        ) {
            Ok(cache) => {
                let jit_count = cache.len();
                if jit_count > 0 {
                    if stats_enabled {
                        eprintln!(
                            "[jit] upgraded {jit_count} invariants with compound layout info",
                        );
                    }
                    let all = cache.covers_all(&self.config.invariants);
                    self.jit_all_compiled = all;
                    self.jit_resolved_fns = if all {
                        cache.resolve_ordered(&self.config.invariants)
                    } else {
                        None
                    };
                    self.jit_cache = Some(cache);
                }
            }
            Err(e) => {
                if stats_enabled {
                    eprintln!("[jit] layout upgrade failed (keeping basic cache): {e}");
                }
            }
        }
    }

    /// Attempt to activate compiled xxh3 fingerprinting for the BFS run.
    ///
    /// Checks all prerequisites:
    /// 1. All init state variables are scalar (Int/Bool) — compound values
    ///    cannot be represented as a single i64 for xxh3 hashing.
    /// 2. No VIEW expression configured — VIEW fingerprinting uses its own
    ///    custom computation path.
    /// 3. No SYMMETRY reduction — symmetry canonical fingerprinting is
    ///    incompatible with xxh3 raw-buffer hashing.
    /// 4. JIT state layout is available (needed for variable count).
    ///
    /// When all conditions are met, sets `jit_compiled_fp_active = true`.
    /// This flag MUST be set before any init states are fingerprinted.
    ///
    /// Part of #3987: Compiled xxh3 fingerprinting for the BFS hot path.
    pub(in crate::check) fn try_activate_compiled_fingerprinting(&mut self) {
        // Part of #4215: Structural guarantee that fingerprint algorithm cannot change
        // after BFS processing has started. If this fires, it means a code path is
        // attempting to switch fingerprint algorithms mid-run, which would cause
        // domain separation violations in the seen set.
        #[cfg(debug_assertions)]
        debug_assert!(
            !self.fp_algorithm_sealed,
            "BUG: try_activate_compiled_fingerprinting called after BFS loop started \
             (fingerprint algorithm sealed). This would mix xxh3 and FP64 fingerprints \
             in the same seen set, causing silent state loss. Part of #4215."
        );

        self.try_activate_compiled_fingerprinting_inner();

        // Part of #4319 Phase 0: fingerprint mixed-mode guard.
        //
        // Once activation decisions have been made, assert the invariant that
        // every fingerprint seen by the BFS comes from a single hash domain.
        //
        // When any LLVM2-compiled action is present, the BFS can emit two
        // classes of successors in the same run:
        //   (a) compiled successors produced by `try_llvm2_action`
        //       (unflattened from an i64 buffer), and
        //   (b) interpreter successors produced by the fallback path.
        // Both classes ultimately flow through `array_state_fingerprint`,
        // which either (i) routes everything through
        // `fingerprint_flat_compiled` when `jit_compiled_fp_active` is true
        // (xxh3 + FLAT_COMPILED_DOMAIN_SEED — single domain), or
        // (ii) routes everything through FP64/FNV when
        // `jit_compiled_fp_active` is false (single FP64 domain). Either
        // configuration is sound *as long as the flag is consistent for the
        // whole run* — which `fp_algorithm_sealed` enforces at the BFS
        // entry and the runtime assertion in `state_fingerprint` checks for
        // the OrdMap path.
        //
        // This guard runs after both `initialize_llvm2_cache` and
        // `try_activate_compiled_fingerprinting_inner`, so it observes the
        // final configuration.
        self.enforce_llvm2_fingerprint_guard();
    }

    /// Actual activation logic, separated so the post-decision guard in
    /// `try_activate_compiled_fingerprinting` can inspect the final state.
    ///
    /// Part of #4319 Phase 0 refactor — body is unchanged from the previous
    /// implementation.
    fn try_activate_compiled_fingerprinting_inner(&mut self) {
        // Condition 1: No VIEW
        if self.compiled.cached_view_name.is_some() {
            return;
        }

        // Condition 2: No SYMMETRY
        if !self.symmetry.perms.is_empty() {
            return;
        }

        // Condition 3: JIT state layout available OR flat_state_primary confirmed.
        // The jit_state_layout is only set for compound specs (upgrade path).
        // For all-scalar specs, flat_state_primary is the reliable indicator.
        // Part of #3986: Enable compiled fingerprinting for all-scalar specs
        // even without the JIT layout (which is only needed for compound access).
        if self.jit_state_layout.is_none() && !self.flat_state_primary {
            return;
        }

        // Condition 4: Check if all init state variables are scalar.
        // We check the first init state in the queue — all states share the
        // same variable types (TLA+ is unityped per variable).
        let all_scalar = if let Some(first_init) = self.get_first_init_state_for_layout() {
            first_init
                .values()
                .iter()
                .all(|cv| cv.is_int() || cv.is_bool())
        } else {
            // If no init state available for inspection, fall back to
            // flat_state_primary which was already verified via roundtrip.
            self.flat_state_primary
        };

        if !all_scalar {
            return;
        }

        // Part of #4281: Gate activation on absence of batch-path-triggering features.
        //
        // The successor-generation dispatcher in `full_state_successors.rs` routes
        // specs with implied actions, constraints, POR, or coverage collection
        // through the batch path. The batch path calls `array_state_fingerprint`
        // with successors produced by `ArrayState::from_successor_state`, which
        // unconditionally pre-caches an FP64 (`finalize_fingerprint_xor`)
        // fingerprint on the successor `ArrayState`. The `array_state_fingerprint`
        // fast path then short-circuits on that cached FP64 value and never
        // executes the xxh3 branch — even though `jit_compiled_fp_active` is
        // true. This mixes FP64 (successors) with xxh3 (init re-fingerprint) in
        // the same `seen_fps` set, causing successors to never match init
        // fingerprints → spurious duplicate inflation.
        //
        // Refusing activation here when any batch-path trigger is configured
        // keeps `seen_fps` in a single FP64 domain for these specs. The
        // performance cost is negligible (xxh3 provides ~5% speedup on
        // all-scalar specs; specs using these features already take the slower
        // batch path).
        if !self.compiled.eval_implied_actions.is_empty()
            || !self.config.constraints.is_empty()
            || !self.config.action_constraints.is_empty()
            || self.por.independence.is_some()
            || (self.coverage.collect && !self.coverage.actions.is_empty())
        {
            return;
        }

        // Part of #4281: Gate activation on `store_full_states == false`.
        //
        // When full-state storage is enabled (liveness, trace reconstruction,
        // fairness), the `seen` HashMap is already populated with FP64 keys by
        // `init_states_full_state()` before this function runs. Activating xxh3
        // here would cause successors to be looked up in `seen_fps` with xxh3
        // fingerprints while `seen` still holds FP64 keys, breaking downstream
        // consumers (`seen.get(fp)` in liveness/safety reconstruction, trace
        // replay). Re-keying the populated `seen` HashMap mid-run is invasive
        // and introduces its own correctness risks. Keep the full-state path on
        // FP64 for single-domain consistency across `seen` and `seen_fps`.
        if self.state_storage.store_full_states {
            return;
        }

        // All conditions met — activate compiled xxh3 fingerprinting.
        self.jit_compiled_fp_active = true;

        // Pre-allocate the flat fingerprint scratch buffer to avoid resize on first use.
        // Part of #3986: Eliminate per-state Vec<i64> allocation.
        let var_count = self.ctx.var_registry().len();
        self.flat_fp_scratch.resize(var_count, 0);

        // Log activation for diagnostics.
        if super::debug::bytecode_vm_stats_enabled() {
            eprintln!(
                "[jit-fp] Compiled xxh3 fingerprinting ACTIVATED (all-scalar, no VIEW/SYMMETRY)"
            );
        }
    }

    /// Enforce the fingerprint mixed-mode invariant for LLVM2 runs.
    ///
    /// When at least one action was compiled by the LLVM2 pipeline, the BFS
    /// dispatcher (`run_gen.rs`) can emit a per-state mixture of
    /// compiled-generated and interpreter-generated successors within the
    /// same run. Phase 0 of the #4319 design (Option D) formalises the
    /// existing all-or-nothing fingerprint gate as a checked invariant:
    ///
    /// For the BFS seen-set to be sound, every fingerprint entered into
    /// `seen_fps` must come from a single hash domain. This holds when any
    /// of the following is true:
    ///   * `jit_compiled_fp_active == true` — xxh3 over flat i64 buffer,
    ///     applied uniformly by `array_state_fingerprint` regardless of
    ///     whether the successor was produced by compiled or interpreter
    ///     code paths.
    ///   * `store_full_states == true` — full-state mode forces the FP64
    ///     array-state path for every successor (both the full-state
    ///     `seen` HashMap and the notrace `seen_fps` set stay on FP64).
    ///   * `compiled.cached_view_name.is_some()` — VIEW fingerprinting
    ///     uses its own single domain via `compute_view_fingerprint_array`.
    ///   * `!symmetry.perms.is_empty()` — symmetry canonicalisation owns
    ///     the entire fingerprint pipeline (see `state_fingerprint`).
    ///
    /// The remaining scenario — LLVM2 compiled actions live, `jit_compiled_fp_active`
    /// false, no full-state/VIEW/symmetry — is the latent divergence risk the
    /// design protects against. Today it cannot be reached: LLVM2 compiles
    /// all-scalar specs, and every all-scalar path that reaches this guard has
    /// either `flat_state_primary` or an all-scalar layout, which activates
    /// `jit_compiled_fp_active` earlier. If that architectural accident ever
    /// breaks (e.g. future work lets LLVM2 compile actions for a compound-
    /// variable spec), this guard fires instead of silently losing states.
    ///
    /// Debug builds panic (surfacing the bug immediately in tests and
    /// development). Release builds log a loud warning and disable the LLVM2
    /// cache as a belt-and-suspenders fallback, preserving soundness at the
    /// cost of performance. Phase 1 (single canonical `tla2_compiled_fp_u64`
    /// symbol) removes the need for this guard entirely.
    ///
    /// Part of #4319 Phase 0 (Option D).
    fn enforce_llvm2_fingerprint_guard(&mut self) {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: self.llvm2_has_compiled_action(),
            jit_compiled_fp_active: self.jit_compiled_fp_active,
            store_full_states: self.state_storage.store_full_states,
            has_view: self.compiled.cached_view_name.is_some(),
            has_symmetry: !self.symmetry.perms.is_empty(),
        };

        match state.evaluate() {
            Llvm2FingerprintGuardOutcome::NotApplicable => {}
            Llvm2FingerprintGuardOutcome::SingleDomain { domain } => {
                if super::debug::bytecode_vm_stats_enabled() {
                    eprintln!(
                        "[llvm2] fingerprint mixed-mode guard OK: domain={domain} \
                         (compiled actions routed through single fingerprint domain)"
                    );
                }
            }
            Llvm2FingerprintGuardOutcome::MixedModeRisk => {
                let msg = "#4319 fingerprint mixed-mode guard: LLVM2 compiled actions present, \
                           but neither jit_compiled_fp_active nor store_full_states nor VIEW/symmetry \
                           is set. Compiled-emitted and interpreter-emitted successors would hash in \
                           two different fingerprint domains, breaking BFS dedup. \
                           See designs/2026-04-20-llvm2-fingerprint-unification.md Phase 0 / Option D.";

                #[cfg(debug_assertions)]
                panic!("{}", msg);

                #[cfg(not(debug_assertions))]
                {
                    eprintln!("[llvm2] {msg}");
                    eprintln!(
                        "[llvm2] disabling LLVM2 native dispatch for this run; \
                         falling back to interpreter to preserve soundness."
                    );
                    #[cfg(feature = "llvm2")]
                    {
                        self.llvm2_cache = None;
                    }
                }
            }
        }
    }

    /// Verify layout compatibility between the flat BFS bridge and the JIT
    /// state layout.
    ///
    /// When both `flat_bfs_bridge` and `jit_state_layout` have been created
    /// (after init state solving), this checks that their slot counts agree.
    /// This is a safety net: if the two independent inference paths produce
    /// incompatible layouts, we log a warning and disable the JIT BFS path.
    ///
    /// No-op when either layout is missing (JIT disabled or no compound vars).
    ///
    /// Part of #3986: Phase 3 layout bridge verification.
    pub(in crate::check) fn verify_layout_compatibility(&self) {
        let Some(ref bridge) = self.flat_bfs_bridge else {
            return;
        };
        let Some(ref jit_layout) = self.jit_state_layout else {
            return;
        };

        let compatible = bridge.is_compatible_with_jit(jit_layout);
        let stats_enabled = super::debug::bytecode_vm_stats_enabled();

        if compatible {
            if stats_enabled {
                eprintln!(
                    "[flat_state] layout bridge verified: check layout ({} slots) \
                     compatible with JIT layout ({} vars)",
                    bridge.num_slots(),
                    jit_layout.var_count(),
                );
            }
        } else {
            // Log a warning. The JIT BFS path should not use the check layout's
            // buffer format if they disagree. The interpreter path is always safe.
            eprintln!(
                "[flat_state] WARNING: layout mismatch between check ({} vars, {} slots) \
                 and JIT ({} vars). JIT BFS will use its own layout.",
                bridge.layout().var_count(),
                bridge.num_slots(),
                jit_layout.var_count(),
            );
        }
    }
}

/// Pure-data view of the inputs to the fingerprint mixed-mode guard.
///
/// Extracted from `ModelChecker` state so the decision logic in
/// [`Llvm2FingerprintGuardState::evaluate`] can be unit-tested without
/// constructing a full `ModelChecker`. See the design doc
/// `designs/2026-04-20-llvm2-fingerprint-unification.md` Phase 0 / Option D.
///
/// Part of #4319.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::check) struct Llvm2FingerprintGuardState {
    /// True iff `Llvm2NativeCache::has_any_compiled_action()` reports at least
    /// one successfully compiled next-state action.
    pub llvm2_has_compiled_action: bool,
    /// True iff `ModelChecker::jit_compiled_fp_active` is set (xxh3 +
    /// `FLAT_COMPILED_DOMAIN_SEED` is the single domain for all successors).
    pub jit_compiled_fp_active: bool,
    /// True iff `StateStorage::store_full_states` is set (FP64 is the single
    /// domain; xxh3 activation is short-circuited elsewhere).
    pub store_full_states: bool,
    /// True iff a VIEW operator is configured
    /// (`compiled.cached_view_name.is_some()`): all fingerprints flow through
    /// `compute_view_fingerprint{,_array}`, pinning the domain to VIEW's output.
    pub has_view: bool,
    /// True iff `symmetry.perms` is non-empty: fingerprints flow through the
    /// canonical representative path (`state_fingerprint` → symmetry cache).
    pub has_symmetry: bool,
}

/// Outcome of the fingerprint mixed-mode guard.
///
/// Part of #4319 Phase 0 (Option D).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::check) enum Llvm2FingerprintGuardOutcome {
    /// No LLVM2 compiled action is present; the guard has nothing to check.
    /// (The pure BFS interpreter path uses a single FP64 domain throughout.)
    NotApplicable,
    /// At least one LLVM2 compiled action is present AND the configuration
    /// pins all successors to a single fingerprint domain. `domain` is a short
    /// human-readable tag identifying which branch took effect, used for
    /// diagnostic logging.
    SingleDomain { domain: &'static str },
    /// LLVM2 compiled actions are present but NO single-domain configuration
    /// is active. Compiled-emitted successors would hash via xxh3 while
    /// interpreter-emitted successors would hash via FP64, which breaks BFS
    /// dedup. This outcome is unreachable in the current codebase (see
    /// `enforce_llvm2_fingerprint_guard` docs) but Phase 0 enforces it
    /// explicitly so a future regression panics in debug and falls back safely
    /// in release.
    MixedModeRisk,
}

impl Llvm2FingerprintGuardState {
    /// Classify the current fingerprint configuration.
    ///
    /// Precedence when multiple single-domain conditions are active:
    /// `jit_compiled_fp_active` > `store_full_states` > VIEW > symmetry.
    /// The ordering only affects the diagnostic `domain` tag; any single-
    /// domain condition is sufficient to rule out the mixed-mode risk.
    ///
    /// Part of #4319 Phase 0 (Option D).
    #[must_use]
    pub(in crate::check) fn evaluate(&self) -> Llvm2FingerprintGuardOutcome {
        if !self.llvm2_has_compiled_action {
            return Llvm2FingerprintGuardOutcome::NotApplicable;
        }
        if self.jit_compiled_fp_active {
            return Llvm2FingerprintGuardOutcome::SingleDomain {
                domain: "xxh3_flat_compiled",
            };
        }
        if self.store_full_states {
            return Llvm2FingerprintGuardOutcome::SingleDomain {
                domain: "fp64_full_states",
            };
        }
        if self.has_view {
            return Llvm2FingerprintGuardOutcome::SingleDomain { domain: "view" };
        }
        if self.has_symmetry {
            return Llvm2FingerprintGuardOutcome::SingleDomain {
                domain: "symmetry_canonical",
            };
        }
        Llvm2FingerprintGuardOutcome::MixedModeRisk
    }
}

#[cfg(test)]
mod llvm2_fingerprint_guard_tests {
    //! Unit tests for the Phase 0 fingerprint mixed-mode guard.
    //!
    //! Part of #4319. See
    //! `designs/2026-04-20-llvm2-fingerprint-unification.md` Phase 0 / Option D.

    use super::{Llvm2FingerprintGuardOutcome, Llvm2FingerprintGuardState};

    /// Baseline: no compiled action, no single-domain flags — guard is inert.
    #[test]
    fn no_compiled_action_is_not_applicable() {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: false,
            jit_compiled_fp_active: false,
            store_full_states: false,
            has_view: false,
            has_symmetry: false,
        };
        assert_eq!(state.evaluate(), Llvm2FingerprintGuardOutcome::NotApplicable);
    }

    /// Even if single-domain flags are set, a run without compiled actions
    /// never enters the guarded code path and must classify as NotApplicable.
    #[test]
    fn no_compiled_action_ignores_other_flags() {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: false,
            jit_compiled_fp_active: true,
            store_full_states: true,
            has_view: true,
            has_symmetry: true,
        };
        assert_eq!(state.evaluate(), Llvm2FingerprintGuardOutcome::NotApplicable);
    }

    /// Compiled action + jit_compiled_fp_active = xxh3 single domain.
    #[test]
    fn compiled_with_jit_fp_active_is_xxh3_single_domain() {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: true,
            jit_compiled_fp_active: true,
            store_full_states: false,
            has_view: false,
            has_symmetry: false,
        };
        assert_eq!(
            state.evaluate(),
            Llvm2FingerprintGuardOutcome::SingleDomain {
                domain: "xxh3_flat_compiled",
            }
        );
    }

    /// Compiled action + store_full_states = FP64 single domain.
    #[test]
    fn compiled_with_store_full_states_is_fp64_single_domain() {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: true,
            jit_compiled_fp_active: false,
            store_full_states: true,
            has_view: false,
            has_symmetry: false,
        };
        assert_eq!(
            state.evaluate(),
            Llvm2FingerprintGuardOutcome::SingleDomain {
                domain: "fp64_full_states",
            }
        );
    }

    /// Compiled action + VIEW = VIEW single domain (all fps via VIEW output).
    #[test]
    fn compiled_with_view_is_view_single_domain() {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: true,
            jit_compiled_fp_active: false,
            store_full_states: false,
            has_view: true,
            has_symmetry: false,
        };
        assert_eq!(
            state.evaluate(),
            Llvm2FingerprintGuardOutcome::SingleDomain { domain: "view" }
        );
    }

    /// Compiled action + symmetry = symmetry-canonical single domain.
    #[test]
    fn compiled_with_symmetry_is_symmetry_single_domain() {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: true,
            jit_compiled_fp_active: false,
            store_full_states: false,
            has_view: false,
            has_symmetry: true,
        };
        assert_eq!(
            state.evaluate(),
            Llvm2FingerprintGuardOutcome::SingleDomain {
                domain: "symmetry_canonical",
            }
        );
    }

    /// THE KEY CASE: compiled action with no single-domain condition active.
    /// This is the mixed-mode risk the Phase 0 guard protects against.
    #[test]
    fn compiled_without_single_domain_is_mixed_mode_risk() {
        let state = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: true,
            jit_compiled_fp_active: false,
            store_full_states: false,
            has_view: false,
            has_symmetry: false,
        };
        assert_eq!(state.evaluate(), Llvm2FingerprintGuardOutcome::MixedModeRisk);
    }

    /// Precedence: when multiple single-domain flags are set, the diagnostic
    /// tag follows the documented order
    /// (jit_compiled_fp_active > store_full_states > VIEW > symmetry).
    /// The ordering is purely diagnostic — any SingleDomain outcome is sound.
    #[test]
    fn single_domain_precedence_order() {
        let all_on = Llvm2FingerprintGuardState {
            llvm2_has_compiled_action: true,
            jit_compiled_fp_active: true,
            store_full_states: true,
            has_view: true,
            has_symmetry: true,
        };
        assert_eq!(
            all_on.evaluate(),
            Llvm2FingerprintGuardOutcome::SingleDomain {
                domain: "xxh3_flat_compiled",
            }
        );

        let no_jit = Llvm2FingerprintGuardState {
            jit_compiled_fp_active: false,
            ..all_on
        };
        assert_eq!(
            no_jit.evaluate(),
            Llvm2FingerprintGuardOutcome::SingleDomain {
                domain: "fp64_full_states",
            }
        );

        let no_jit_no_full = Llvm2FingerprintGuardState {
            store_full_states: false,
            ..no_jit
        };
        assert_eq!(
            no_jit_no_full.evaluate(),
            Llvm2FingerprintGuardOutcome::SingleDomain { domain: "view" }
        );

        let only_symmetry = Llvm2FingerprintGuardState {
            has_view: false,
            ..no_jit_no_full
        };
        assert_eq!(
            only_symmetry.evaluate(),
            Llvm2FingerprintGuardOutcome::SingleDomain {
                domain: "symmetry_canonical",
            }
        );
    }
}

#[cfg(test)]
#[path = "run_prepare_tests.rs"]
mod run_prepare_tests;
