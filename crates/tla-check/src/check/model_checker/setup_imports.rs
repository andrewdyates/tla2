// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Import graph resolution and operator/variable collection helpers for model checker setup.
//!
//! Extracted from `setup.rs` as part of #2359 Phase 2 decomposition.
//! These free functions compute which modules contribute to the unqualified
//! operator namespace and collect operator definitions, variables, and ASSUME
//! formulas from the module graph.

use super::{
    module_set_validation, Arc, CheckError, Expr, FxHashMap, Module, OperatorDef, Spanned, Unit,
};
use module_set_validation::{missing_module_setup_error, ModuleReferenceKind};

pub(crate) type SetupCollections = (
    Vec<Arc<str>>,
    FxHashMap<String, OperatorDef>,
    Vec<(String, Spanned<Expr>)>,
);

pub(crate) fn compute_import_sets<'a>(
    module: &'a Module,
    module_by_name_orig: &FxHashMap<&'a str, &'a Module>,
    setup_error: &mut Option<CheckError>,
) -> (
    std::collections::HashSet<&'a str>,
    std::collections::HashSet<&'a str>,
) {
    let main_module_name = module.name.node.as_str();

    let mut unqualified_modules: std::collections::HashSet<&str> = std::collections::HashSet::new();
    let mut stack: Vec<(ModuleReferenceKind, &str, &str)> = Vec::new();
    // EXTENDS closure from the main module
    stack.extend(module.extends.iter().map(|s| {
        (
            ModuleReferenceKind::Extends,
            s.node.as_str(),
            main_module_name,
        )
    }));
    // Standalone INSTANCE imports from the main module
    for unit in &module.units {
        if let Unit::Instance(inst) = &unit.node {
            stack.push((
                ModuleReferenceKind::Instance,
                inst.module.node.as_str(),
                main_module_name,
            ));
        }
    }
    // Transitive closure: follow EXTENDS and standalone INSTANCE in imported modules.
    while let Some((ref_kind, name, from_module)) = stack.pop() {
        if setup_error.is_some() {
            break;
        }
        if !unqualified_modules.insert(name) {
            continue;
        }
        let Some(m) = module_by_name_orig.get(name) else {
            if !tla_core::is_stdlib_module(name) && setup_error.is_none() {
                missing_module_setup_error(setup_error, name, ref_kind, from_module);
            }
            continue;
        };
        stack.extend(m.extends.iter().map(|s| {
            (
                ModuleReferenceKind::Extends,
                s.node.as_str(),
                m.name.node.as_str(),
            )
        }));
        for unit in &m.units {
            if let Unit::Instance(inst) = &unit.node {
                // LOCAL INSTANCE operators are only visible within the declaring
                // module — they must not propagate to the main module's unqualified
                // namespace. This matches TLC's behavior where LOCAL limits visibility
                // to the declaring module only. Without this check, LOCAL INSTANCE'd
                // modules (e.g., NaturalsInduction via SequenceTheorems) leak theorem
                // operators with unbound higher-order parameters (e.g., "Def") into
                // the global namespace, causing "Undefined operator" errors (#2900).
                if !inst.local {
                    stack.push((
                        ModuleReferenceKind::Instance,
                        inst.module.node.as_str(),
                        m.name.node.as_str(),
                    ));
                }
            }
        }
    }

    // BUG FIX #295: Compute a separate set for modules that should contribute VARIABLES.
    // Only modules reachable via EXTENDS chain should contribute variables.
    // INSTANCE'd modules (even standalone) have their variables substituted and should NOT
    // add variables to the main module's state space.
    let mut variable_contributing_modules: std::collections::HashSet<&str> =
        std::collections::HashSet::new();
    let mut extends_stack: Vec<(&str, &str)> = Vec::new();
    // Only follow EXTENDS from the main module (not INSTANCE)
    extends_stack.extend(
        module
            .extends
            .iter()
            .map(|s| (s.node.as_str(), main_module_name)),
    );
    while let Some((name, from_module)) = extends_stack.pop() {
        if setup_error.is_some() {
            break;
        }
        if !variable_contributing_modules.insert(name) {
            continue;
        }
        let Some(m) = module_by_name_orig.get(name) else {
            if !tla_core::is_stdlib_module(name) && setup_error.is_none() {
                missing_module_setup_error(
                    setup_error,
                    name,
                    ModuleReferenceKind::Extends,
                    from_module,
                );
            }
            continue;
        };
        // Only follow EXTENDS chain, not INSTANCE declarations
        extends_stack.extend(
            m.extends
                .iter()
                .map(|s| (s.node.as_str(), m.name.node.as_str())),
        );
    }

    (unqualified_modules, variable_contributing_modules)
}

/// Lightweight check for whether any state variables exist in the module graph.
///
/// Unlike `collect_ops_vars_and_assumes`, this avoids collecting operators and assumes —
/// it only checks for `Unit::Variable` declarations in the main module and
/// variable-contributing (EXTENDS-chain) modules.
///
/// Note: this is slightly more conservative than the full collection because it does not
/// filter out variables that are shadowed by operators (implicit binding). For the
/// assume-only detection in `AdaptiveChecker`, this conservatism is correct — a module
/// with VARIABLE declarations is not an assume-only model even if some variables are shadowed.
pub(crate) fn has_any_variables(
    module: &Module,
    extended_modules: &[&Module],
    variable_contributing_modules: &std::collections::HashSet<&str>,
) -> bool {
    // Check main module first (cheapest path)
    for unit in &module.units {
        if matches!(unit.node, Unit::Variable(_)) {
            return true;
        }
    }
    // Check variable-contributing (EXTENDS-chain) modules
    for ext_mod in extended_modules {
        if !variable_contributing_modules.contains(ext_mod.name.node.as_str()) {
            continue;
        }
        for unit in &ext_mod.units {
            if matches!(unit.node, Unit::Variable(_)) {
                return true;
            }
        }
    }
    false
}

/// Collect operator definitions, state variables, and ASSUME formulas from
/// the module graph.
///
/// Delegates to `checker_ops::collect_ops_vars_and_assumes` — the single canonical
/// implementation shared with the parallel checker. The `FxHashMap` return type
/// is inferred from the `SetupCollections` type alias via the generic hasher
/// parameter.
///
/// Part of #810: eliminates near-verbatim duplication between sequential and
/// parallel collection paths that previously caused parity drift (#2787).
pub(crate) fn collect_ops_vars_and_assumes(
    module: &Module,
    extended_modules: &[&Module],
    unqualified_modules: &std::collections::HashSet<&str>,
    variable_contributing_modules: &std::collections::HashSet<&str>,
) -> SetupCollections {
    crate::checker_ops::collect_ops_vars_and_assumes(
        module,
        extended_modules,
        |name| unqualified_modules.contains(name),
        |name| variable_contributing_modules.contains(name),
    )
}
