// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Canonical `EvalCtx` module loading order.
//!
//! This is the shared module loading sequence used by both sequential and parallel
//! model checkers. Extracting it prevents parity drift in module loading order —
//! the same class of bug that caused #2787.

use crate::eval::EvalCtx;
use std::sync::Arc;
use tla_core::ast::Module;

use super::module_graph::materialized_standalone_imports_recursive;

/// Load modules into an `EvalCtx` using the canonical loading order.
///
/// This is the shared module loading sequence used by both sequential and parallel
/// model checkers. The loading order is semantically significant:
///
/// 1. Set `extended_module_names` so builtin overrides (e.g., DyadicRationals.Add)
///    are correctly scoped.
/// 2. Load unqualified-imported modules first (EXTENDS + standalone INSTANCE).
/// 3. Load main module last (its operators can override imported ones).
/// 4. (If `load_instances`) Load instance modules with their EXTENDS chains so
///    module references (`I!Op`) can be evaluated.
///
/// Four call sites previously duplicated this sequence:
/// - Sequential constructor (`setup_build.rs:89-115`)
/// - Parallel constructor (`module_setup.rs:84-98`, without instances)
/// - Parallel `prepare_check` (`prepare.rs:63-96`)
/// - Parallel worker init (`helpers.rs:45-74`)
///
/// Extracting it prevents parity drift in module loading order — the same class
/// of bug that caused #2787.
pub(crate) fn load_modules_into_ctx(
    ctx: &mut EvalCtx,
    main_module: &Module,
    extended_modules: &[&Module],
    unqualified_module_names: &rustc_hash::FxHashSet<String>,
    load_instances: bool,
) {
    // Set extended_module_names for builtin override scoping
    Arc::make_mut(ctx.shared_arc_mut())
        .extended_module_names_mut()
        .clone_from(unqualified_module_names);

    // Build module lookup map (needed for LOCAL INSTANCE resolution and instance loading)
    let module_by_name: rustc_hash::FxHashMap<&str, &Module> = extended_modules
        .iter()
        .map(|m| (m.name.node.as_str(), *m))
        .collect();

    // Load unqualified imported modules first (in order).
    // LOCAL INSTANCE'd modules are loaded BEFORE their parent so the parent's
    // operators (which may include cfg-scoped overrides) take precedence via
    // insert-overwrite.  Without this ordering, the instanced module's original
    // operator definitions overwrite cfg-rewritten definitions (#2954).
    for ext_mod in extended_modules {
        if unqualified_module_names.contains(ext_mod.name.node.as_str()) {
            // Part of #2834: Load operators from LOCAL INSTANCE declarations first
            // (lower precedence). LOCAL INSTANCE brings the instanced module's
            // operators into the declaring module's scope (e.g., Functions.tla
            // LOCAL INSTANCE Folds → MapThenFoldSet).
            for unit in &ext_mod.units {
                if let tla_core::ast::Unit::Instance(inst) = &unit.node {
                    if inst.local {
                        if let Some(inst_mod) = module_by_name.get(inst.module.node.as_str()) {
                            ctx.load_module(inst_mod);
                        }
                    }
                }
            }
            for imported in materialized_standalone_imports_recursive(ext_mod, &module_by_name) {
                ctx.load_module(&imported);
            }
            // Parent module loaded second — its operators (including cfg-scoped
            // overrides) overwrite any same-named operators from LOCAL INSTANCE.
            ctx.load_module(ext_mod);
        }
    }
    // Load LOCAL INSTANCE'd modules from main module first (lower precedence)
    for unit in &main_module.units {
        if let tla_core::ast::Unit::Instance(inst) = &unit.node {
            if inst.local {
                if let Some(inst_mod) = module_by_name.get(inst.module.node.as_str()) {
                    ctx.load_module(inst_mod);
                }
            }
        }
    }
    for imported in materialized_standalone_imports_recursive(main_module, &module_by_name) {
        ctx.load_module(&imported);
    }
    // Load main module last (can override everything)
    ctx.load_module(main_module);

    // Load instance modules for I!Op references
    if load_instances {
        for ext_mod in extended_modules {
            ctx.load_instance_module_with_extends(
                ext_mod.name.node.clone(),
                ext_mod,
                &module_by_name,
            );
        }
    }
}
