// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::CheckError;
use crate::expr_visitor::{walk_expr, ExprVisitor};
use crate::ConfigCheckError;
use tla_core::ast::{Expr, Module, Unit};

#[derive(Debug, Clone, Copy)]
pub(crate) enum ModuleReferenceKind {
    Extends,
    /// A standalone `INSTANCE M` unit.
    Instance,
    /// An `INSTANCE M` expression appearing inside another expression (named or nested).
    InstanceExpr,
}

impl ModuleReferenceKind {
    pub(crate) fn display(self) -> &'static str {
        match self {
            ModuleReferenceKind::Extends => "EXTENDS",
            ModuleReferenceKind::Instance => "INSTANCE",
            ModuleReferenceKind::InstanceExpr => "INSTANCE",
        }
    }
}

pub(crate) fn missing_module_setup_error(
    setup_error: &mut Option<CheckError>,
    name: &str,
    ref_kind: ModuleReferenceKind,
    from_module: &str,
) {
    if setup_error.is_some() {
        return;
    }
    *setup_error = Some(
        ConfigCheckError::Setup(format!(
        "referenced module '{}' (via {} in module '{}') is missing from the provided module set",
        name,
        ref_kind.display(),
        from_module
    ))
        .into(),
    );
}

fn require_loaded_module<'a>(
    module_by_name: &std::collections::HashMap<&'a str, &'a Module>,
    setup_error: &mut Option<CheckError>,
    main_module_name: &str,
    name: &str,
    ref_kind: ModuleReferenceKind,
    from_module: &str,
) -> Option<&'a Module> {
    if setup_error.is_some() {
        return None;
    }
    if name == main_module_name {
        return None;
    }
    if tla_core::is_stdlib_module(name) {
        return None;
    }
    match module_by_name.get(name) {
        Some(m) => Some(*m),
        None => {
            missing_module_setup_error(setup_error, name, ref_kind, from_module);
            None
        }
    }
}

/// Visitor that collects `InstanceExpr` module references during expression traversal.
///
/// Replaces a 477-line hand-written match with `ExprVisitor`-based traversal.
/// The visitor intercepts `InstanceExpr` nodes, validates referenced modules,
/// and adds them to the visit queue. All other recursion is handled by `walk_expr`.
struct InstanceExprModuleVisitor<'a, 'b> {
    module_by_name: &'b std::collections::HashMap<&'a str, &'a Module>,
    setup_error: &'b mut Option<CheckError>,
    main_module_name: &'b str,
    from_module: &'b str,
    to_visit: &'b mut Vec<&'a Module>,
    queued: &'b mut std::collections::HashSet<&'a str>,
}

impl ExprVisitor for InstanceExprModuleVisitor<'_, '_> {
    type Output = ();

    fn visit_node(&mut self, expr: &Expr) -> Option<Self::Output> {
        if self.setup_error.is_some() {
            return Some(());
        }
        if let Expr::InstanceExpr(module_name, _) = expr {
            if let Some(m) = require_loaded_module(
                self.module_by_name,
                self.setup_error,
                self.main_module_name,
                module_name,
                ModuleReferenceKind::InstanceExpr,
                self.from_module,
            ) {
                if self.queued.insert(m.name.node.as_str()) {
                    self.to_visit.push(m);
                }
            }
        }
        None // continue default traversal for all nodes
    }
}

pub(crate) fn visit_expr_for_instance_expr_modules<'a>(
    module_by_name: &std::collections::HashMap<&'a str, &'a Module>,
    setup_error: &mut Option<CheckError>,
    main_module_name: &str,
    expr: &Expr,
    from_module: &str,
    to_visit: &mut Vec<&'a Module>,
    queued: &mut std::collections::HashSet<&'a str>,
) {
    let mut visitor = InstanceExprModuleVisitor {
        module_by_name,
        setup_error,
        main_module_name,
        from_module,
        to_visit,
        queued,
    };
    walk_expr(&mut visitor, expr);
}

/// Validate that the provided `extended_modules` form a loaded-module superset for this run.
///
/// This is intended for embedding APIs where the caller is expected to load the whole non-stdlib
/// module closure and pass it in.
pub(crate) fn validate_loaded_module_superset(
    module: &Module,
    extended_modules: &[&Module],
) -> Option<CheckError> {
    let mut setup_error: Option<CheckError> = None;

    let mut module_by_name: std::collections::HashMap<&str, &Module> =
        std::collections::HashMap::new();
    for ext_mod in extended_modules {
        module_by_name.insert(ext_mod.name.node.as_str(), *ext_mod);
    }

    let main_module_name = module.name.node.as_str();
    let mut visited: std::collections::HashSet<&str> = std::collections::HashSet::new();
    let mut queued: std::collections::HashSet<&str> = std::collections::HashSet::new();
    queued.insert(main_module_name);

    let mut to_visit: Vec<&Module> = vec![module];
    while let Some(m) = to_visit.pop() {
        if setup_error.is_some() {
            break;
        }
        let from = m.name.node.as_str();
        if !visited.insert(from) {
            continue;
        }

        for ext in &m.extends {
            let name = ext.node.as_str();
            if let Some(sub) = require_loaded_module(
                &module_by_name,
                &mut setup_error,
                main_module_name,
                name,
                ModuleReferenceKind::Extends,
                from,
            ) {
                if queued.insert(sub.name.node.as_str()) {
                    to_visit.push(sub);
                }
            }
        }

        for unit in &m.units {
            match &unit.node {
                Unit::Instance(inst) => {
                    let name = inst.module.node.as_str();
                    if let Some(sub) = require_loaded_module(
                        &module_by_name,
                        &mut setup_error,
                        main_module_name,
                        name,
                        ModuleReferenceKind::Instance,
                        from,
                    ) {
                        if queued.insert(sub.name.node.as_str()) {
                            to_visit.push(sub);
                        }
                    }
                    for sub in &inst.substitutions {
                        visit_expr_for_instance_expr_modules(
                            &module_by_name,
                            &mut setup_error,
                            main_module_name,
                            &sub.to.node,
                            from,
                            &mut to_visit,
                            &mut queued,
                        );
                    }
                }
                Unit::Operator(def) => {
                    visit_expr_for_instance_expr_modules(
                        &module_by_name,
                        &mut setup_error,
                        main_module_name,
                        &def.body.node,
                        from,
                        &mut to_visit,
                        &mut queued,
                    );
                }
                Unit::Assume(assume) => {
                    visit_expr_for_instance_expr_modules(
                        &module_by_name,
                        &mut setup_error,
                        main_module_name,
                        &assume.expr.node,
                        from,
                        &mut to_visit,
                        &mut queued,
                    );
                }
                _ => {}
            }
        }
    }

    setup_error
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::parse_module;

    #[test]
    fn test_validate_no_extends_no_instances() {
        let module = parse_module(
            r#"
---- MODULE Simple ----
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#,
        );
        let result = validate_loaded_module_superset(&module, &[]);
        assert!(
            result.is_none(),
            "Module with no extends/instances should succeed: {:?}",
            result
        );
    }

    #[test]
    fn test_validate_extends_stdlib_no_extra_modules() {
        let module = parse_module(
            r#"
---- MODULE WithStdlib ----
EXTENDS Integers, Sequences, FiniteSets
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="#,
        );
        // Stdlib modules should not need to be in the extended set
        let result = validate_loaded_module_superset(&module, &[]);
        assert!(
            result.is_none(),
            "Stdlib EXTENDS should not require modules in set: {:?}",
            result
        );
    }

    #[test]
    fn test_validate_extends_missing_module() {
        let module = parse_module(
            r#"
---- MODULE Main ----
EXTENDS MissingModule
VARIABLE x
Init == x = 0
===="#,
        );
        let result = validate_loaded_module_superset(&module, &[]);
        assert!(result.is_some(), "Missing EXTENDS module should fail");
        if let Some(CheckError::Config(ConfigCheckError::Setup(msg))) = result {
            assert!(
                msg.contains("MissingModule"),
                "Error should mention module name: {}",
                msg
            );
            assert!(
                msg.contains("EXTENDS"),
                "Error should mention EXTENDS: {}",
                msg
            );
        } else {
            panic!("Expected SetupError");
        }
    }

    #[test]
    fn test_validate_extends_module_present() {
        let main = parse_module(
            r#"
---- MODULE Main ----
EXTENDS Base
VARIABLE x
Init == x = 0
===="#,
        );
        let base = parse_module(
            r#"
---- MODULE Base ----
VARIABLE y
BaseOp == y = 1
===="#,
        );
        let result = validate_loaded_module_superset(&main, &[&base]);
        assert!(
            result.is_none(),
            "Module with EXTENDS of present module should succeed: {:?}",
            result
        );
    }

    #[test]
    fn test_validate_instance_missing_module() {
        let module = parse_module(
            r#"
---- MODULE Main ----
VARIABLE x
INSTANCE MissingInst
Init == x = 0
===="#,
        );
        let result = validate_loaded_module_superset(&module, &[]);
        assert!(result.is_some(), "Missing INSTANCE module should fail");
        if let Some(CheckError::Config(ConfigCheckError::Setup(msg))) = result {
            assert!(
                msg.contains("MissingInst"),
                "Error should mention module name: {}",
                msg
            );
            assert!(
                msg.contains("INSTANCE"),
                "Error should mention INSTANCE: {}",
                msg
            );
        } else {
            panic!("Expected SetupError");
        }
    }

    #[test]
    fn test_validate_transitive_extends_missing() {
        // Main EXTENDS Base, Base EXTENDS Deep — Deep is missing
        let main = parse_module(
            r#"
---- MODULE Main ----
EXTENDS Base
VARIABLE x
Init == x = 0
===="#,
        );
        let base = parse_module(
            r#"
---- MODULE Base ----
EXTENDS DeepModule
VARIABLE y
===="#,
        );
        let result = validate_loaded_module_superset(&main, &[&base]);
        assert!(result.is_some(), "Transitive missing module should fail");
        if let Some(CheckError::Config(ConfigCheckError::Setup(msg))) = result {
            assert!(
                msg.contains("DeepModule"),
                "Error should mention missing transitive module: {}",
                msg
            );
        }
    }
}
