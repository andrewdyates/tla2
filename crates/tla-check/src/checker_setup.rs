// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared checker setup pipeline for ModelChecker, ParallelChecker, and AdaptiveChecker.
//!
//! This module extracts the common module-resolution, validation, cfg-override, and
//! operator/variable collection sequence that all three checkers perform during
//! construction. Extracting it eliminates glue-code duplication that previously
//! caused parity drift between sequential and parallel paths (#810, #2787).
//!
//! The leaf operations (`compute_import_sets`, `load_modules_into_ctx`,
//! `collect_ops_vars_and_assumes`) were already shared — this module unifies
//! the *orchestration* of those operations.

use crate::check::model_checker::setup::setup_imports;
use crate::check::module_set_validation;
use crate::config::Config;
use crate::eval::EvalCtx;
use crate::CheckError;
use crate::ConfigCheckError;
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::Arc;
use tla_core::ast::{Expr, Module, OperatorDef};
use tla_core::Spanned;

/// Result of the shared module setup pipeline.
///
/// Contains everything needed for any checker variant to complete its construction:
/// - The EvalCtx with modules loaded
/// - Rewritten modules (after cfg overrides)
/// - Import sets for operator/variable scoping
/// - Collected operators, variables, and ASSUME formulas
/// - Pre-resolved state variable references in operator bodies
pub(crate) struct CheckerSetup {
    /// EvalCtx with modules loaded. The sequential checker keeps this for its own use;
    /// the parallel checker discards it (it creates fresh per-worker contexts in prepare_check).
    pub(crate) ctx: EvalCtx,
    /// Main module after cfg-scoped rewrites.
    pub(crate) main_module: Module,
    /// Extended modules after cfg-scoped rewrites.
    pub(crate) rewritten_exts: Vec<Module>,
    /// Set of module names contributing to the unqualified operator namespace.
    pub(crate) unqualified_modules: FxHashSet<String>,
    /// Sorted state variable names.
    pub(crate) vars: Vec<Arc<str>>,
    /// Operator definitions from all unqualified modules + main module.
    pub(crate) op_defs: rustc_hash::FxHashMap<String, OperatorDef>,
    /// ASSUME formulas from all unqualified modules + main module.
    pub(crate) assumes: Vec<(String, Spanned<Expr>)>,
    /// First setup error encountered (missing modules, cfg override failure, etc.).
    pub(crate) setup_error: Option<CheckError>,
}

/// Options controlling the setup pipeline behavior.
pub(crate) struct SetupOptions {
    /// Whether to load instance modules into the EvalCtx for `I!Op` references.
    /// The sequential checker sets this to `true`; the parallel checker sets it to
    /// `false` because it creates fresh EvalCtx instances per worker in `prepare_check`.
    pub(crate) load_instances: bool,
}

/// Run the shared checker setup pipeline.
///
/// Performs the following steps in order:
/// 1. Build module-by-name lookup map
/// 2. Validate that the loaded-module superset covers all references
/// 3. Compute unqualified import closure (EXTENDS + standalone INSTANCE)
/// 4. Compute variable-contributing closure (EXTENDS-only)
/// 5. Apply cfg module-scoped rewrites
/// 6. Load modules into a fresh EvalCtx
/// 7. Collect operators, variables, and ASSUME formulas
/// 8. Pre-resolve state variable references in operator bodies
///
/// Both `ModelChecker` and `ParallelChecker` call this function. The sequential
/// checker additionally calls `ctx.register_vars()` and
/// `ctx.resolve_state_vars_in_loaded_ops()` on the returned ctx.
pub(crate) fn setup_checker_modules(
    module: &Module,
    extended_modules: &[&Module],
    config: &Config,
    options: &SetupOptions,
) -> CheckerSetup {
    let mut ctx = EvalCtx::new();

    // Step 1: Build module-by-name lookup map.
    let mut module_by_name_orig: FxHashMap<&str, &Module> = FxHashMap::default();
    for ext_mod in extended_modules {
        module_by_name_orig.insert(ext_mod.name.node.as_str(), *ext_mod);
    }

    // Step 2: Validate loaded-module superset.
    let mut setup_error =
        module_set_validation::validate_loaded_module_superset(module, extended_modules);

    // Step 3-4: Compute import sets (unqualified + variable-contributing).
    let (unqualified_modules, variable_contributing_modules) =
        setup_imports::compute_import_sets(module, &module_by_name_orig, &mut setup_error);

    // Step 5: Apply cfg module-scoped rewrites.
    let (rewritten_main, rewritten_exts) =
        match crate::cfg_overrides::rewrite_modules_for_cfg_scoped_overrides(
            module,
            extended_modules,
            &unqualified_modules,
            config,
        ) {
            Ok((m, exts)) => (m, exts),
            Err(e) => {
                if setup_error.is_none() {
                    setup_error = Some(ConfigCheckError::Config(e.to_string()).into());
                }
                (
                    module.clone(),
                    extended_modules.iter().map(|m| (*m).clone()).collect(),
                )
            }
        };

    // Convert import sets to owned FxHashSet<String> for the shared loading helper.
    let unqualified_modules_owned: FxHashSet<String> = unqualified_modules
        .iter()
        .map(|s| (*s).to_string())
        .collect();

    // Step 6: Load modules into EvalCtx.
    let rewritten_ext_refs: Vec<&Module> = rewritten_exts.iter().collect();
    crate::checker_ops::load_modules_into_ctx(
        &mut ctx,
        &rewritten_main,
        &rewritten_ext_refs,
        &unqualified_modules_owned,
        options.load_instances,
    );

    // Step 7: Collect operators, variables, and ASSUME formulas.
    let (vars, mut op_defs, assumes) = setup_imports::collect_ops_vars_and_assumes(
        &rewritten_main,
        &rewritten_ext_refs,
        &unqualified_modules,
        &variable_contributing_modules,
    );

    // Step 8a: Register variables in the EvalCtx's VarRegistry so that
    // resolve_state_vars_in_op_def can resolve variable references.
    // The MC keeps this ctx and relies on the registered vars; the PC discards
    // the ctx but still benefits from correct resolution of the op_defs.
    ctx.register_vars(vars.iter().cloned());

    // Step 8b: Pre-resolve state variable references in operator bodies for O(1) lookup.
    for def in op_defs.values_mut() {
        tla_eval::state_var::resolve_state_vars_in_op_def(def, ctx.var_registry());
    }

    CheckerSetup {
        ctx,
        main_module: rewritten_main,
        rewritten_exts,
        unqualified_modules: unqualified_modules_owned,
        vars,
        op_defs,
        assumes,
        setup_error,
    }
}

/// Lightweight setup for AdaptiveChecker: only validates modules and computes
/// import sets without loading modules, collecting operators, or building an EvalCtx.
///
/// This is sufficient for AdaptiveChecker's constructor which defers heavy setup
/// to `check()` where it creates inner ModelChecker/ParallelChecker instances.
pub(crate) struct LightweightSetup {
    /// First setup error (missing modules).
    pub(crate) setup_error: Option<CheckError>,
    /// Whether any module in scope declares state variables.
    pub(crate) has_variables: bool,
}

/// Run the lightweight setup for AdaptiveChecker.
pub(crate) fn setup_lightweight(module: &Module, extended_modules: &[&Module]) -> LightweightSetup {
    let mut setup_error =
        module_set_validation::validate_loaded_module_superset(module, extended_modules);

    let module_by_name: FxHashMap<&str, &Module> = extended_modules
        .iter()
        .map(|m| (m.name.node.as_str(), *m))
        .collect();

    let (_unqualified_modules, variable_contributing_modules) =
        setup_imports::compute_import_sets(module, &module_by_name, &mut setup_error);

    let has_variables =
        setup_imports::has_any_variables(module, extended_modules, &variable_contributing_modules);

    LightweightSetup {
        setup_error,
        has_variables,
    }
}
