// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Validation checks V001-V012 for `tla2 validate`.

use std::collections::{HashMap, HashSet};
use std::path::Path;

use tla_core::ast::{Expr, Module, Unit};
use tla_core::span::Span;

use super::{
    collect_constants, collect_defined_operators, collect_variables, ConfigInfo, IssueSeverity,
    ValidationIssue,
};

// ---------------------------------------------------------------------------
// V001: All referenced operator names are defined
// ---------------------------------------------------------------------------

/// V001: Check that all operator names referenced in expressions are defined
/// in the module or available via EXTENDS.
pub(super) fn check_operator_references(module: &Module, issues: &mut Vec<ValidationIssue>) {
    let defined = collect_defined_operators(module);
    let variables = collect_variables(module);
    let constants = collect_constants(module);

    // Collect operator parameters for each operator (they're local to the body)
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            let mut local_names: HashSet<String> = HashSet::new();
            for param in &op.params {
                local_names.insert(param.name.node.clone());
            }
            check_refs_in_expr(
                &op.body.node,
                &defined,
                &variables,
                &constants,
                &local_names,
                issues,
            );
        }
    }
}

fn check_refs_in_expr(
    expr: &Expr,
    defined: &HashSet<String>,
    variables: &HashSet<String>,
    constants: &HashSet<String>,
    local_names: &HashSet<String>,
    issues: &mut Vec<ValidationIssue>,
) {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            if !defined.contains(name)
                && !variables.contains(name)
                && !constants.contains(name)
                && !local_names.contains(name)
            {
                // We don't have perfect span data for the reference itself, but
                // Ident references are common enough that we rely on the parent
                // expression to set context. Use a dummy span rather than panic.
                issues.push(ValidationIssue {
                    code: "V001",
                    severity: IssueSeverity::Warning,
                    message: format!("operator or name `{name}` is referenced but not defined"),
                    span: Span::dummy(),
                });
            }
        }
        Expr::Apply(func, args) => {
            check_refs_in_expr(&func.node, defined, variables, constants, local_names, issues);
            for arg in args {
                check_refs_in_expr(&arg.node, defined, variables, constants, local_names, issues);
            }
        }
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            let mut local = local_names.clone();
            for bv in bounds {
                local.insert(bv.name.node.clone());
                if let Some(domain) = &bv.domain {
                    check_refs_in_expr(&domain.node, defined, variables, constants, &local, issues);
                }
            }
            check_refs_in_expr(&body.node, defined, variables, constants, &local, issues);
        }
        Expr::Choose(bv, body) | Expr::SetFilter(bv, body) => {
            let mut local = local_names.clone();
            local.insert(bv.name.node.clone());
            if let Some(domain) = &bv.domain {
                check_refs_in_expr(&domain.node, defined, variables, constants, &local, issues);
            }
            check_refs_in_expr(&body.node, defined, variables, constants, &local, issues);
        }
        Expr::SetBuilder(body, bounds) | Expr::FuncDef(bounds, body) => {
            let mut local = local_names.clone();
            for bv in bounds {
                local.insert(bv.name.node.clone());
                if let Some(domain) = &bv.domain {
                    check_refs_in_expr(&domain.node, defined, variables, constants, &local, issues);
                }
            }
            check_refs_in_expr(&body.node, defined, variables, constants, &local, issues);
        }
        Expr::Lambda(params, body) => {
            let mut local = local_names.clone();
            for p in params {
                local.insert(p.node.clone());
            }
            check_refs_in_expr(&body.node, defined, variables, constants, &local, issues);
        }
        Expr::Let(defs, body) => {
            let mut local = local_names.clone();
            for def in defs {
                local.insert(def.name.node.clone());
            }
            for def in defs {
                check_refs_in_expr(&def.body.node, defined, variables, constants, &local, issues);
            }
            check_refs_in_expr(&body.node, defined, variables, constants, &local, issues);
        }
        _ => visit_expr_children(expr, |child| {
            check_refs_in_expr(child, defined, variables, constants, local_names, issues);
        }),
    }
}

// ---------------------------------------------------------------------------
// V002: All variables referenced in expressions are declared
// ---------------------------------------------------------------------------

/// V002: Check that all variables referenced via priming (x') are declared as VARIABLE.
pub(super) fn check_variable_references(module: &Module, issues: &mut Vec<ValidationIssue>) {
    let variables = collect_variables(module);

    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            check_primed_vars_in_expr(&op.body.node, &variables, issues);
        }
    }
}

fn check_primed_vars_in_expr(
    expr: &Expr,
    variables: &HashSet<String>,
    issues: &mut Vec<ValidationIssue>,
) {
    match expr {
        Expr::Prime(inner) => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &inner.node {
                if !variables.contains(name) {
                    issues.push(ValidationIssue {
                        code: "V002",
                        severity: IssueSeverity::Error,
                        message: format!(
                            "primed name `{name}'` is not declared as a VARIABLE"
                        ),
                        span: Span::dummy(),
                    });
                }
            }
            // Also recurse into inner
            check_primed_vars_in_expr(&inner.node, variables, issues);
        }
        _ => visit_expr_children(expr, |child| {
            check_primed_vars_in_expr(child, variables, issues);
        }),
    }
}

// ---------------------------------------------------------------------------
// V003: CONSTANT values in .cfg match declarations in spec
// ---------------------------------------------------------------------------

/// V003: Check that constant names in .cfg match CONSTANT declarations in the spec.
pub(super) fn check_config_constants(
    module: &Module,
    config: &ConfigInfo,
    issues: &mut Vec<ValidationIssue>,
) {
    if !config.has_config {
        return;
    }

    let spec_constants = collect_constants(module);
    let cfg_constants: HashSet<&str> = config.constant_names.iter().map(|s| s.as_str()).collect();

    // Constants in config but not declared in spec
    for cfg_name in &config.constant_names {
        if !spec_constants.contains(cfg_name) {
            issues.push(ValidationIssue {
                code: "V003",
                severity: IssueSeverity::Warning,
                message: format!(
                    "config assigns constant `{cfg_name}` which is not declared in the spec"
                ),
                span: module.span,
            });
        }
    }

    // Constants declared in spec but not assigned in config
    for unit in &module.units {
        if let Unit::Constant(decls) = &unit.node {
            for decl in decls {
                if !cfg_constants.contains(decl.name.node.as_str()) {
                    issues.push(ValidationIssue {
                        code: "V003",
                        severity: IssueSeverity::Error,
                        message: format!(
                            "CONSTANT `{}` declared in spec but not assigned in config",
                            decl.name.node
                        ),
                        span: decl.name.span,
                    });
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// V004: EXTENDS modules exist and can be found
// ---------------------------------------------------------------------------

/// V004: Check that all EXTENDS modules are either standard library modules or
/// can be found as .tla files in the spec's directory.
pub(super) fn check_extends_modules(
    file: &Path,
    module: &Module,
    issues: &mut Vec<ValidationIssue>,
) {
    let base_dir = file.parent().unwrap_or_else(|| Path::new("."));

    for ext in &module.extends {
        let name = ext.node.as_str();
        // Standard library modules are always available
        if tla_core::is_stdlib_module(name) {
            continue;
        }
        // Check if the .tla file exists
        let tla_path = base_dir.join(format!("{name}.tla"));
        if !tla_path.exists() {
            issues.push(ValidationIssue {
                code: "V004",
                severity: IssueSeverity::Error,
                message: format!(
                    "EXTENDS `{name}`: module file `{}.tla` not found in {}",
                    name,
                    base_dir.display()
                ),
                span: ext.span,
            });
        }
    }
}

// ---------------------------------------------------------------------------
// V005: Init operator exists
// ---------------------------------------------------------------------------

/// V005: Check that the Init operator specified in config exists in the spec.
pub(super) fn check_init_exists(
    module: &Module,
    config: &ConfigInfo,
    issues: &mut Vec<ValidationIssue>,
) {
    let init_name = match &config.init {
        Some(name) => name.as_str(),
        None => return, // No Init in config = nothing to check
    };

    let has_init = module.units.iter().any(|u| {
        matches!(&u.node, Unit::Operator(op) if op.name.node == init_name)
    });

    if !has_init {
        issues.push(ValidationIssue {
            code: "V005",
            severity: IssueSeverity::Error,
            message: format!("INIT operator `{init_name}` specified in config is not defined in the spec"),
            span: module.span,
        });
    }
}

// ---------------------------------------------------------------------------
// V006: Next operator exists
// ---------------------------------------------------------------------------

/// V006: Check that the Next operator specified in config exists in the spec.
pub(super) fn check_next_exists(
    module: &Module,
    config: &ConfigInfo,
    issues: &mut Vec<ValidationIssue>,
) {
    let next_name = match &config.next {
        Some(name) => name.as_str(),
        None => return,
    };

    let has_next = module.units.iter().any(|u| {
        matches!(&u.node, Unit::Operator(op) if op.name.node == next_name)
    });

    if !has_next {
        issues.push(ValidationIssue {
            code: "V006",
            severity: IssueSeverity::Error,
            message: format!("NEXT operator `{next_name}` specified in config is not defined in the spec"),
            span: module.span,
        });
    }
}

// ---------------------------------------------------------------------------
// V007: All INVARIANT operators in config exist in the spec
// ---------------------------------------------------------------------------

/// V007: Check that all INVARIANT names in the config correspond to defined operators.
pub(super) fn check_config_invariants(
    module: &Module,
    config: &ConfigInfo,
    issues: &mut Vec<ValidationIssue>,
) {
    let defined = collect_defined_operators(module);

    for inv_name in &config.invariants {
        if !defined.contains(inv_name) {
            issues.push(ValidationIssue {
                code: "V007",
                severity: IssueSeverity::Error,
                message: format!(
                    "INVARIANT `{inv_name}` in config is not defined in the spec"
                ),
                span: module.span,
            });
        }
    }
}

// ---------------------------------------------------------------------------
// V008: All PROPERTY operators in config exist in the spec
// ---------------------------------------------------------------------------

/// V008: Check that all PROPERTY names in the config correspond to defined operators.
pub(super) fn check_config_properties(
    module: &Module,
    config: &ConfigInfo,
    issues: &mut Vec<ValidationIssue>,
) {
    let defined = collect_defined_operators(module);

    for prop_name in &config.properties {
        if !defined.contains(prop_name) {
            issues.push(ValidationIssue {
                code: "V008",
                severity: IssueSeverity::Error,
                message: format!(
                    "PROPERTY `{prop_name}` in config is not defined in the spec"
                ),
                span: module.span,
            });
        }
    }
}

// ---------------------------------------------------------------------------
// V009: SYMMETRY set in config is valid
// ---------------------------------------------------------------------------

/// V009: Check that the SYMMETRY set referenced in config is a valid set constant.
pub(super) fn check_symmetry_set(
    module: &Module,
    config: &ConfigInfo,
    issues: &mut Vec<ValidationIssue>,
) {
    let sym_name = match &config.symmetry {
        Some(name) => name.as_str(),
        None => return,
    };

    let defined = collect_defined_operators(module);
    let constants = collect_constants(module);

    if !defined.contains(sym_name) && !constants.contains(sym_name) {
        issues.push(ValidationIssue {
            code: "V009",
            severity: IssueSeverity::Error,
            message: format!(
                "SYMMETRY `{sym_name}` in config is not defined as an operator or constant in the spec"
            ),
            span: module.span,
        });
    }
}

// ---------------------------------------------------------------------------
// V010: Recursive operators have RECURSIVE declaration
// ---------------------------------------------------------------------------

/// V010: Check that recursive operators (those that reference themselves in
/// their body) have a corresponding RECURSIVE declaration.
pub(super) fn check_recursive_declarations(
    module: &Module,
    issues: &mut Vec<ValidationIssue>,
) {
    // Collect all RECURSIVE declarations
    let mut recursive_decls: HashSet<String> = HashSet::new();
    for unit in &module.units {
        if let Unit::Recursive(decls) = &unit.node {
            for decl in decls {
                recursive_decls.insert(decl.name.node.clone());
            }
        }
    }

    // Check each operator: if it references itself in its body, it must have RECURSIVE.
    // We can't rely solely on op.is_recursive since that flag is only set when the
    // RECURSIVE declaration exists. We need to detect self-references independently.
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            let name = &op.name.node;
            if expr_references_name(&op.body.node, name) && !recursive_decls.contains(name) {
                issues.push(ValidationIssue {
                    code: "V010",
                    severity: IssueSeverity::Error,
                    message: format!(
                        "operator `{name}` is recursive but has no RECURSIVE declaration"
                    ),
                    span: op.name.span,
                });
            }
        }
    }
}

/// Check if an expression directly references a given name (non-transitive).
fn expr_references_name(expr: &Expr, target: &str) -> bool {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => name == target,
        Expr::Apply(func, args) => {
            if let Expr::Ident(name, _) = &func.node {
                if name == target {
                    return true;
                }
            }
            expr_references_name(&func.node, target)
                || args.iter().any(|a| expr_references_name(&a.node, target))
        }
        _ => {
            let mut found = false;
            visit_expr_children(expr, |child| {
                if !found && expr_references_name(child, target) {
                    found = true;
                }
            });
            found
        }
    }
}

// ---------------------------------------------------------------------------
// V011: Operator arity matches at all call sites
// ---------------------------------------------------------------------------

/// V011: Check that operator applications use the correct number of arguments.
pub(super) fn check_operator_arity(module: &Module, issues: &mut Vec<ValidationIssue>) {
    // Build arity map: operator_name -> param_count
    let mut arity_map: HashMap<&str, usize> = HashMap::new();
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            arity_map.insert(op.name.node.as_str(), op.params.len());
        }
    }

    // Also include stdlib operator arities
    for ext in &module.extends {
        if tla_core::is_stdlib_module(&ext.node) {
            for (name, arity) in tla_core::get_module_operators(&ext.node) {
                arity_map.insert(name, (*arity).max(0) as usize);
            }
        }
    }

    // Walk all operator bodies looking for Apply nodes
    for unit in &module.units {
        if let Unit::Operator(op) = &unit.node {
            check_arity_in_expr(&op.body.node, &arity_map, issues);
        }
    }
}

fn check_arity_in_expr(
    expr: &Expr,
    arity_map: &HashMap<&str, usize>,
    issues: &mut Vec<ValidationIssue>,
) {
    match expr {
        Expr::Apply(func, args) => {
            if let Expr::Ident(name, _) = &func.node {
                if let Some(&expected) = arity_map.get(name.as_str()) {
                    if expected > 0 && args.len() != expected {
                        issues.push(ValidationIssue {
                            code: "V011",
                            severity: IssueSeverity::Error,
                            message: format!(
                                "operator `{name}` expects {expected} argument{}, but called with {}",
                                if expected == 1 { "" } else { "s" },
                                args.len()
                            ),
                            span: func.span,
                        });
                    }
                }
            }
            // Recurse into func and args
            check_arity_in_expr(&func.node, arity_map, issues);
            for arg in args {
                check_arity_in_expr(&arg.node, arity_map, issues);
            }
        }
        _ => visit_expr_children(expr, |child| {
            check_arity_in_expr(child, arity_map, issues);
        }),
    }
}

// ---------------------------------------------------------------------------
// V012: INSTANCE substitution targets exist
// ---------------------------------------------------------------------------

/// V012: Check that INSTANCE substitution targets (the LHS of WITH mappings)
/// are plausible names (variables or constants in the instanced module).
/// Since we may not have the instanced module loaded, we check that the
/// substitution source names are at least defined in the current module.
pub(super) fn check_instance_substitutions(
    module: &Module,
    issues: &mut Vec<ValidationIssue>,
) {
    let defined = collect_defined_operators(module);
    let variables = collect_variables(module);
    let constants = collect_constants(module);

    for unit in &module.units {
        if let Unit::Instance(inst) = &unit.node {
            for sub in &inst.substitutions {
                // The "to" expression should reference names that exist in the
                // current module scope
                check_substitution_expr(
                    &sub.to.node,
                    &defined,
                    &variables,
                    &constants,
                    &inst.module.node,
                    issues,
                );
            }
        }
    }
}

fn check_substitution_expr(
    expr: &Expr,
    defined: &HashSet<String>,
    variables: &HashSet<String>,
    constants: &HashSet<String>,
    _module_name: &str,
    issues: &mut Vec<ValidationIssue>,
) {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            if !defined.contains(name)
                && !variables.contains(name)
                && !constants.contains(name)
            {
                issues.push(ValidationIssue {
                    code: "V012",
                    severity: IssueSeverity::Warning,
                    message: format!(
                        "INSTANCE substitution references `{name}` which is not defined in the current module"
                    ),
                    span: Span::dummy(),
                });
            }
        }
        _ => visit_expr_children(expr, |child| {
            check_substitution_expr(child, defined, variables, constants, _module_name, issues);
        }),
    }
}

// ---------------------------------------------------------------------------
// Expression traversal helper (mirrors cmd_lint's visit_expr_children)
// ---------------------------------------------------------------------------

/// Visit all direct child expressions of an Expr node, calling `f` on each.
fn visit_expr_children(expr: &Expr, mut f: impl FnMut(&Expr)) {
    match expr {
        // Leaves
        Expr::Bool(_)
        | Expr::Int(_)
        | Expr::String(_)
        | Expr::Ident(_, _)
        | Expr::StateVar(_, _, _)
        | Expr::OpRef(_)
        | Expr::InstanceExpr(_, _) => {}

        // Unary
        Expr::Not(e)
        | Expr::Prime(e)
        | Expr::Always(e)
        | Expr::Eventually(e)
        | Expr::Enabled(e)
        | Expr::Unchanged(e)
        | Expr::Powerset(e)
        | Expr::BigUnion(e)
        | Expr::Domain(e)
        | Expr::Neg(e) => {
            f(&e.node);
        }

        // Binary
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Equiv(a, b)
        | Expr::In(a, b)
        | Expr::NotIn(a, b)
        | Expr::Subseteq(a, b)
        | Expr::Union(a, b)
        | Expr::Intersect(a, b)
        | Expr::SetMinus(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::Lt(a, b)
        | Expr::Leq(a, b)
        | Expr::Gt(a, b)
        | Expr::Geq(a, b)
        | Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::IntDiv(a, b)
        | Expr::Mod(a, b)
        | Expr::Pow(a, b)
        | Expr::Range(a, b)
        | Expr::LeadsTo(a, b)
        | Expr::WeakFair(a, b)
        | Expr::StrongFair(a, b)
        | Expr::FuncApply(a, b)
        | Expr::FuncSet(a, b) => {
            f(&a.node);
            f(&b.node);
        }

        // Apply
        Expr::Apply(func, args) => {
            f(&func.node);
            for arg in args {
                f(&arg.node);
            }
        }

        // Lambda
        Expr::Lambda(_, body) => {
            f(&body.node);
        }

        // Label
        Expr::Label(label) => {
            f(&label.body.node);
        }

        // ModuleRef
        Expr::ModuleRef(target, _, args) => {
            if let tla_core::ast::ModuleTarget::Parameterized(_, params) = target {
                for p in params {
                    f(&p.node);
                }
            }
            if let tla_core::ast::ModuleTarget::Chained(base) = target {
                f(&base.node);
            }
            for arg in args {
                f(&arg.node);
            }
        }

        // Quantifiers
        Expr::Forall(bounds, body) | Expr::Exists(bounds, body) => {
            for bv in bounds {
                if let Some(d) = &bv.domain {
                    f(&d.node);
                }
            }
            f(&body.node);
        }

        Expr::Choose(bv, body) => {
            if let Some(d) = &bv.domain {
                f(&d.node);
            }
            f(&body.node);
        }

        // Sets
        Expr::SetEnum(elems) | Expr::Tuple(elems) | Expr::Times(elems) => {
            for elem in elems {
                f(&elem.node);
            }
        }

        Expr::SetBuilder(body, bounds) | Expr::FuncDef(bounds, body) => {
            for bv in bounds {
                if let Some(d) = &bv.domain {
                    f(&d.node);
                }
            }
            f(&body.node);
        }

        Expr::SetFilter(bv, body) => {
            if let Some(d) = &bv.domain {
                f(&d.node);
            }
            f(&body.node);
        }

        // Records
        Expr::Record(fields) | Expr::RecordSet(fields) => {
            for (_, val) in fields {
                f(&val.node);
            }
        }

        Expr::RecordAccess(base, _) => {
            f(&base.node);
        }

        // Except
        Expr::Except(base, specs) => {
            f(&base.node);
            for spec in specs {
                f(&spec.value.node);
                for path_elem in &spec.path {
                    if let tla_core::ast::ExceptPathElement::Index(idx) = path_elem {
                        f(&idx.node);
                    }
                }
            }
        }

        // Control
        Expr::If(cond, then_, else_) => {
            f(&cond.node);
            f(&then_.node);
            f(&else_.node);
        }

        Expr::Case(arms, other) => {
            for arm in arms {
                f(&arm.guard.node);
                f(&arm.body.node);
            }
            if let Some(o) = other {
                f(&o.node);
            }
        }

        Expr::Let(defs, body) => {
            for def in defs {
                f(&def.body.node);
            }
            f(&body.node);
        }

        Expr::SubstIn(_, body) => {
            f(&body.node);
        }
    }
}
