// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Module-graph traversal and canonical ops/vars/ASSUME collection.
//!
//! This module owns the import traversal policy for:
//! - explicit `WITH` materialization
//! - `LOCAL INSTANCE` operator visibility
//! - EXTENDS-only variable contribution
//! - named `ASSUME` promotion to zero-arg operators

use rustc_hash::FxHashMap;
use std::collections::HashSet;
use std::sync::Arc;
use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::Spanned;

fn materialized_standalone_imports(
    module: &Module,
    module_by_name: &FxHashMap<&str, &Module>,
) -> Vec<Module> {
    module
        .units
        .iter()
        .filter_map(|unit| {
            let Unit::Instance(inst) = &unit.node else {
                return None;
            };
            if inst.local || inst.substitutions.is_empty() {
                return None;
            }
            module_by_name
                .get(inst.module.node.as_str())
                .map(|imported| {
                    crate::eval::materialize_module_with_substitutions(
                        imported,
                        &inst.substitutions,
                    )
                })
        })
        .collect()
}

pub(super) fn materialized_standalone_imports_recursive(
    module: &Module,
    module_by_name: &FxHashMap<&str, &Module>,
) -> Vec<Module> {
    fn collect(
        module: &Module,
        module_by_name: &FxHashMap<&str, &Module>,
        out: &mut Vec<Module>,
        visited: &mut HashSet<String>,
    ) {
        for imported in materialized_standalone_imports(module, module_by_name) {
            if !visited.insert(imported.name.node.clone()) {
                continue;
            }
            collect(&imported, module_by_name, out, visited);
            out.push(imported);
        }
    }

    let mut out = Vec::new();
    let mut visited = HashSet::new();
    visited.insert(module.name.node.clone());
    collect(module, module_by_name, &mut out, &mut visited);
    out
}

fn collect_module_assumes(
    module: &Module,
    op_defs: &mut FxHashMap<String, OperatorDef>,
    assumes: &mut Vec<(String, Spanned<Expr>)>,
) {
    for unit in &module.units {
        if let Unit::Assume(assume) = &unit.node {
            if let Some(name) = &assume.name {
                let op_def = OperatorDef {
                    name: name.clone(),
                    params: vec![],
                    body: assume.expr.clone(),
                    local: false,
                    contains_prime: false,
                    guards_depend_on_prime: false,
                    has_primed_param: false,
                    is_recursive: false,
                    self_call_count: 0,
                };
                op_defs.insert(name.node.clone(), op_def);
            }
            assumes.push((module.name.node.clone(), assume.expr.clone()));
        }
    }
}

fn collect_imported_assumes(
    module: &Module,
    module_by_name: &FxHashMap<&str, &Module>,
    seen_raw_modules: &mut std::collections::HashSet<String>,
    op_defs: &mut FxHashMap<String, OperatorDef>,
    assumes: &mut Vec<(String, Spanned<Expr>)>,
) {
    for ext in &module.extends {
        let Some(ext_mod) = module_by_name.get(ext.node.as_str()) else {
            continue;
        };
        if seen_raw_modules.insert(ext_mod.name.node.clone()) {
            collect_imported_assumes(ext_mod, module_by_name, seen_raw_modules, op_defs, assumes);
            collect_module_assumes(ext_mod, op_defs, assumes);
        }
    }

    for imported in materialized_standalone_imports(module, module_by_name) {
        collect_imported_assumes(
            &imported,
            module_by_name,
            seen_raw_modules,
            op_defs,
            assumes,
        );
        collect_module_assumes(&imported, op_defs, assumes);
    }

    for unit in &module.units {
        let Unit::Instance(inst) = &unit.node else {
            continue;
        };
        if inst.local || !inst.substitutions.is_empty() {
            continue;
        }
        let Some(inst_mod) = module_by_name.get(inst.module.node.as_str()) else {
            continue;
        };
        if seen_raw_modules.insert(inst_mod.name.node.clone()) {
            collect_imported_assumes(inst_mod, module_by_name, seen_raw_modules, op_defs, assumes);
            collect_module_assumes(inst_mod, op_defs, assumes);
        }
    }
}

/// Collect operator definitions, state variables, and ASSUME formulas from
/// a module graph.
///
/// This is the canonical 3-pass collection algorithm used by both sequential
/// and parallel model checkers:
///
/// 1. **Operators**: collect all operator definitions from unqualified-imported
///    modules, then from the main module (which may shadow imported operators).
/// 2. **Variables**: collect state variables from variable-contributing modules
///    (EXTENDS-chain only, per BUG FIX #295), skipping names already defined
///    as operators (implicit constant binding — #2787). Then collect main-module
///    variables (always state variables).
/// 3. **ASSUMEs**: collect ASSUME formulas from all unqualified modules and
///    the main module. Named assumes also get registered as operator definitions.
///
/// Variables are sorted for deterministic fingerprinting.
///
/// Both sequential (`setup_imports.rs:collect_ops_vars_and_assumes`) and parallel
/// (`module_setup.rs:collect_vars_and_ops` + `collect_assumes`) checkers previously
/// duplicated this entire algorithm. Extracting it prevents parity drift of the
/// kind that caused #2787.
#[allow(clippy::type_complexity)]
pub(crate) fn collect_ops_vars_and_assumes(
    main_module: &Module,
    extended_modules: &[&Module],
    is_unqualified: impl Fn(&str) -> bool,
    is_variable_contributing: impl Fn(&str) -> bool,
) -> (
    Vec<Arc<str>>,
    FxHashMap<String, OperatorDef>,
    Vec<(String, Spanned<Expr>)>,
) {
    let mut vars: Vec<Arc<str>> = Vec::new();
    let mut op_defs: FxHashMap<String, OperatorDef> = FxHashMap::default();
    let mut assumes: Vec<(String, Spanned<Expr>)> = Vec::new();

    // First pass: collect operator definitions from imported modules
    let ext_by_name: FxHashMap<&str, &Module> = extended_modules
        .iter()
        .map(|m| (m.name.node.as_str(), *m))
        .collect();
    for ext_mod in extended_modules {
        if !is_unqualified(ext_mod.name.node.as_str()) {
            continue;
        }
        // Part of #2834: Also collect operators from LOCAL INSTANCE declarations.
        // LOCAL INSTANCE brings the instanced module's operators into the declaring
        // module's scope. Without this, operators like MapThenFoldSet (from Folds,
        // LOCAL INSTANCE'd by Functions) are invisible when evaluating Functions'
        // FoldFunction/FoldFunctionOnSet operators.
        for unit in &ext_mod.units {
            if let Unit::Instance(inst) = &unit.node {
                if inst.local {
                    if let Some(inst_mod) = ext_by_name.get(inst.module.node.as_str()) {
                        for inner_unit in &inst_mod.units {
                            if let Unit::Operator(def) = &inner_unit.node {
                                op_defs
                                    .entry(def.name.node.clone())
                                    .or_insert_with(|| def.clone());
                            }
                        }
                    }
                }
            }
        }
        for imported in materialized_standalone_imports_recursive(ext_mod, &ext_by_name) {
            for unit in &imported.units {
                if let Unit::Operator(def) = &unit.node {
                    op_defs.insert(def.name.node.clone(), def.clone());
                }
            }
        }
        for unit in &ext_mod.units {
            if let Unit::Operator(def) = &unit.node {
                op_defs.insert(def.name.node.clone(), def.clone());
            }
        }
    }
    // Also from main module (may shadow), including its LOCAL INSTANCE operators
    for unit in &main_module.units {
        if let Unit::Instance(inst) = &unit.node {
            if inst.local {
                if let Some(inst_mod) = ext_by_name.get(inst.module.node.as_str()) {
                    for inner_unit in &inst_mod.units {
                        if let Unit::Operator(def) = &inner_unit.node {
                            op_defs
                                .entry(def.name.node.clone())
                                .or_insert_with(|| def.clone());
                        }
                    }
                }
            }
        }
    }
    for imported in materialized_standalone_imports_recursive(main_module, &ext_by_name) {
        for unit in &imported.units {
            if let Unit::Operator(def) = &unit.node {
                op_defs.insert(def.name.node.clone(), def.clone());
            }
        }
    }
    for unit in &main_module.units {
        if let Unit::Operator(def) = &unit.node {
            op_defs.insert(def.name.node.clone(), def.clone());
        }
    }

    // Second pass: collect variables from variable-contributing modules,
    // skipping names already defined as operators (implicit constant binding — #2787).
    // BUG FIX #295: Only collect variables from truly EXTENDS'd modules, not INSTANCE'd.
    for ext_mod in extended_modules {
        if !is_variable_contributing(ext_mod.name.node.as_str()) {
            continue;
        }
        for unit in &ext_mod.units {
            if let Unit::Variable(var_names) = &unit.node {
                for var in var_names {
                    let var_name = var.node.as_str();
                    // Skip if already a variable
                    if vars.iter().any(|v| v.as_ref() == var_name) {
                        continue;
                    }
                    // Skip if already an operator (implicit binding — #2787)
                    if op_defs.contains_key(var_name) {
                        continue;
                    }
                    vars.push(Arc::from(var_name));
                }
            }
        }
    }

    // Third pass: collect variables from main module
    // Main module variables are always state variables (not implicitly bound)
    for unit in &main_module.units {
        if let Unit::Variable(var_names) = &unit.node {
            for var in var_names {
                if !vars.iter().any(|v| v.as_ref() == var.node.as_str()) {
                    vars.push(Arc::from(var.node.as_str()));
                }
            }
        }
    }

    // Sort variables for deterministic fingerprinting
    // (OrdMap iterates in sorted key order, so VarRegistry must match)
    vars.sort();

    // Collect ASSUME statements from imported modules using the same explicit-WITH
    // materialization view as the runtime loader, then from the main module itself.
    let mut seen_raw_modules = std::collections::HashSet::new();
    collect_imported_assumes(
        main_module,
        &ext_by_name,
        &mut seen_raw_modules,
        &mut op_defs,
        &mut assumes,
    );
    collect_module_assumes(main_module, &mut op_defs, &mut assumes);

    (vars, op_defs, assumes)
}
