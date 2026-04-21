// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Import operators from INSTANCE modules into a TIR module.
//!
//! When a TLA+ spec uses `INSTANCE M` or `INSTANCE M WITH x <- expr`,
//! operators from M (Init, Next, invariants, helpers) become available in the
//! main module. The TIR lowering pass (`lower_module_for_codegen`) only lowers
//! operators *directly defined* in the main module, skipping INSTANCE-definition
//! operators (whose AST bodies are `InstanceExpr`/`SubstIn`).
//!
//! This module bridges the gap by scanning the AST module for unnamed INSTANCE
//! declarations, finding importable operators in the instanced modules, and
//! lowering them through the TIR path with the correct substitutions. The
//! result is appended to the existing `TirModule.operators`.

use std::collections::{HashMap, HashSet};
use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::{intern_name, is_stdlib_module, Spanned};
use tla_tir::{
    lower_operator_in_instance_scope, lower_operator_with_env, TirBoundPattern, TirBoundVar,
    TirExpr, TirLetDef, TirLoweringEnv, TirModule, TirNameKind, TirOperator, TirOperatorRef,
};

/// Import operators from INSTANCE modules into the TIR module.
///
/// Scans the AST module for unnamed INSTANCE declarations (not
/// `I == INSTANCE M`, but bare `INSTANCE M WITH ...`), finds operators in the
/// instanced module that are importable for codegen (Init, Next, invariants,
/// non-primed helpers), and lowers them via TIR with the INSTANCE substitutions
/// applied. Already-present operators in the TIR module are not duplicated.
pub(super) fn import_instance_operators(
    tir_module: &mut TirModule,
    ast_module: &Module,
    env: &TirLoweringEnv<'_>,
) {
    let mut seen_names: HashSet<String> = tir_module
        .operators
        .iter()
        .map(|op| op.name.clone())
        .collect();

    import_extends_operators(tir_module, ast_module, env, &mut seen_names);
    import_unnamed_instance_operators(tir_module, ast_module, env, &mut seen_names);
    import_named_instance_operators(tir_module, ast_module, env, &mut seen_names);
}

/// Import operators from the main module's EXTENDS chain.
///
/// When a TLA+ module uses `EXTENDS Foo`, all non-LOCAL operators from `Foo`
/// (and transitively from Foo's own EXTENDS) become available in the main module.
/// The TIR lowering pass only lowers operators directly defined in the main module,
/// so EXTENDS-imported operators (Init, Next, helpers) are missing. This function
/// fills the gap by TIR-lowering operators from extended non-stdlib modules.
fn import_extends_operators(
    tir_module: &mut TirModule,
    ast_module: &Module,
    env: &TirLoweringEnv<'_>,
    seen_names: &mut HashSet<String>,
) {
    let mut visited_modules = HashSet::new();
    visited_modules.insert(ast_module.name.node.clone());
    import_extends_recursive(tir_module, ast_module, env, seen_names, &mut visited_modules);
}

/// Recursively import operators from EXTENDS modules.
fn import_extends_recursive(
    tir_module: &mut TirModule,
    ast_module: &Module,
    env: &TirLoweringEnv<'_>,
    seen_names: &mut HashSet<String>,
    visited_modules: &mut HashSet<String>,
) {
    for ext in &ast_module.extends {
        // Skip stdlib modules (Naturals, Sequences, FiniteSets, etc.)
        if is_stdlib_module(&ext.node) {
            continue;
        }

        // Skip already-visited modules to prevent circular EXTENDS recursion
        if !visited_modules.insert(ext.node.clone()) {
            continue;
        }

        let Some(ext_module) = env.module_ref(&ext.node) else {
            continue;
        };

        for dep_unit in &ext_module.units {
            let Unit::Operator(op_def) = &dep_unit.node else {
                continue;
            };

            // Skip LOCAL operators
            if op_def.local {
                continue;
            }

            // Skip operators whose bodies are INSTANCE expressions
            if is_instance_body(&op_def.body.node) {
                continue;
            }

            // Skip operators already present in the TIR module
            if seen_names.contains(&op_def.name.node) {
                continue;
            }

            // Lower the operator in the context of the extended module
            let result = lower_operator_with_env(env, ext_module, op_def);

            match result {
                Ok(tir_op) => {
                    seen_names.insert(tir_op.name.clone());
                    tir_module.operators.push(tir_op);
                }
                Err(e) => {
                    eprintln!(
                        "warning: failed to lower EXTENDS operator '{}' from module '{}': {e}",
                        op_def.name.node, ext.node
                    );
                }
            }
        }

        // Recurse into this extension's EXTENDS
        import_extends_recursive(tir_module, ext_module, env, seen_names, visited_modules);
    }
}

fn import_unnamed_instance_operators(
    tir_module: &mut TirModule,
    ast_module: &Module,
    env: &TirLoweringEnv<'_>,
    seen_names: &mut HashSet<String>,
) {
    for unit in &ast_module.units {
        let Unit::Instance(inst) = &unit.node else {
            continue;
        };

        // Find the instanced module in the environment
        let Some(instance_module) = env.module_ref(&inst.module.node) else {
            continue;
        };

        // Iterate over operators in the instanced module
        for dep_unit in &instance_module.units {
            let Unit::Operator(op_def) = &dep_unit.node else {
                continue;
            };

            // Skip LOCAL operators
            if op_def.local {
                continue;
            }

            // Skip operators already present in the TIR module
            if seen_names.contains(&op_def.name.node) {
                continue;
            }

            // Skip operators whose bodies are INSTANCE expressions (namespace carriers)
            if is_instance_body(&op_def.body.node) {
                continue;
            }

            // Lower the operator with the INSTANCE substitutions applied
            let result = lower_operator_in_instance_scope(
                env,
                ast_module,
                instance_module,
                op_def,
                &inst.substitutions,
            );

            match result {
                Ok(tir_op) => {
                    seen_names.insert(tir_op.name.clone());
                    tir_module.operators.push(tir_op);
                }
                Err(e) => {
                    // Operator could not be lowered (unsupported TIR construct).
                    // Log a warning so silent failures are visible during debugging.
                    eprintln!(
                        "warning: failed to lower INSTANCE operator '{}' from module '{}': {e}",
                        op_def.name.node, inst.module.node
                    );
                }
            }
        }

        // Also import from EXTENDS of the instanced module (transitive)
        let mut visited_modules = HashSet::new();
        // Insert the root module name to prevent circular EXTENDS from re-entering it
        visited_modules.insert(ast_module.name.node.clone());
        visited_modules.insert(inst.module.node.clone());
        import_from_extends(
            tir_module,
            ast_module,
            instance_module,
            &inst.substitutions,
            env,
            seen_names,
            &mut visited_modules,
            None,
        );
    }
}

fn import_named_instance_operators(
    tir_module: &mut TirModule,
    ast_module: &Module,
    env: &TirLoweringEnv<'_>,
    seen_names: &mut HashSet<String>,
) {
    for unit in &ast_module.units {
        let Unit::Operator(inst_op) = &unit.node else {
            continue;
        };

        // Only non-parameterized top-level named instances materialize as
        // standalone operators in the codegen namespace (`I!Op`).
        if inst_op.local || !inst_op.params.is_empty() {
            continue;
        }

        let Expr::InstanceExpr(module_name, substitutions) = &inst_op.body.node else {
            continue;
        };

        let Some(instance_module) = env.module_ref(module_name) else {
            continue;
        };

        let mut visited_modules = HashSet::new();
        visited_modules.insert(ast_module.name.node.clone());

        let mut visible_names = HashSet::new();
        let mut candidates = Vec::new();
        collect_named_import_candidates(
            instance_module,
            &inst_op.name.node,
            env,
            &mut visited_modules,
            &mut visible_names,
            &mut candidates,
        );

        let rename_map: HashMap<String, String> = candidates
            .iter()
            .map(|candidate| {
                (
                    candidate.op_def.name.node.clone(),
                    candidate.imported_name.clone(),
                )
            })
            .collect();

        for candidate in candidates {
            if seen_names.contains(&candidate.imported_name) {
                continue;
            }

            let result = lower_operator_in_instance_scope(
                env,
                ast_module,
                candidate.module,
                candidate.op_def,
                substitutions,
            );

            match result {
                Ok(mut tir_op) => {
                    tir_op.body = rewrite_operator_refs(
                        tir_op.body,
                        &rename_map,
                        &tir_op.params.iter().cloned().collect(),
                    );
                    rename_operator(&mut tir_op, &candidate.imported_name);
                    seen_names.insert(tir_op.name.clone());
                    tir_module.operators.push(tir_op);
                }
                Err(e) => {
                    eprintln!(
                        "warning: failed to lower named INSTANCE operator '{}' from '{}': {e}",
                        candidate.op_def.name.node, inst_op.name.node
                    );
                }
            }
        }
    }
}

/// Recursively import operators from modules extended by the instanced module.
///
/// `visited_modules` prevents infinite recursion on circular EXTENDS chains.
fn import_from_extends(
    tir_module: &mut TirModule,
    root_module: &Module,
    instance_module: &Module,
    substitutions: &[tla_core::ast::Substitution],
    env: &TirLoweringEnv<'_>,
    seen_names: &mut HashSet<String>,
    visited_modules: &mut HashSet<String>,
    prefix: Option<&str>,
) {
    // Update seen_names with what we just added
    for op in &tir_module.operators {
        seen_names.insert(op.name.clone());
    }

    for ext in &instance_module.extends {
        // Skip already-visited modules to prevent circular EXTENDS recursion
        if !visited_modules.insert(ext.node.clone()) {
            continue;
        }

        let Some(ext_module) = env.module_ref(&ext.node) else {
            continue;
        };

        for dep_unit in &ext_module.units {
            let Unit::Operator(op_def) = &dep_unit.node else {
                continue;
            };

            if op_def.local {
                continue;
            }

            if is_instance_body(&op_def.body.node) {
                continue;
            }

            let imported_name = prefixed_name(prefix, &op_def.name.node);
            if seen_names.contains(&imported_name) {
                continue;
            }

            // Lower through the instance_module scope with substitutions
            let result = lower_operator_in_instance_scope(
                env,
                root_module,
                ext_module,
                op_def,
                substitutions,
            );

            match result {
                Ok(mut tir_op) => {
                    rename_operator(&mut tir_op, &imported_name);
                    seen_names.insert(tir_op.name.clone());
                    tir_module.operators.push(tir_op);
                }
                Err(e) => {
                    eprintln!(
                        "warning: failed to lower EXTENDS operator '{}' from module '{}': {e}",
                        op_def.name.node, ext.node
                    );
                }
            }
        }

        // Recurse into this extension's extends
        import_from_extends(
            tir_module,
            root_module,
            ext_module,
            substitutions,
            env,
            seen_names,
            visited_modules,
            prefix,
        );
    }
}

#[derive(Clone)]
struct NamedImportCandidate<'a> {
    module: &'a Module,
    op_def: &'a OperatorDef,
    imported_name: String,
}

fn collect_named_import_candidates<'a>(
    module: &'a Module,
    prefix: &str,
    env: &'a TirLoweringEnv<'a>,
    visited_modules: &mut HashSet<String>,
    visible_names: &mut HashSet<String>,
    out: &mut Vec<NamedImportCandidate<'a>>,
) {
    if !visited_modules.insert(module.name.node.clone()) {
        return;
    }

    for unit in &module.units {
        let Unit::Operator(op_def) = &unit.node else {
            continue;
        };

        if is_instance_body(&op_def.body.node) {
            continue;
        }

        if !visible_names.insert(op_def.name.node.clone()) {
            continue;
        }

        out.push(NamedImportCandidate {
            module,
            op_def,
            imported_name: prefixed_name(Some(prefix), &op_def.name.node),
        });
    }

    for ext in &module.extends {
        let Some(ext_module) = env.module_ref(&ext.node) else {
            continue;
        };
        collect_named_import_candidates(
            ext_module,
            prefix,
            env,
            visited_modules,
            visible_names,
            out,
        );
    }
}

fn rename_operator(op: &mut TirOperator, imported_name: &str) {
    op.name = imported_name.to_string();
    op.name_id = intern_name(imported_name);
}

fn prefixed_name(prefix: Option<&str>, name: &str) -> String {
    match prefix {
        Some(prefix) => format!("{prefix}!{name}"),
        None => name.to_string(),
    }
}

fn rewrite_operator_refs(
    expr: Spanned<TirExpr>,
    rename_map: &HashMap<String, String>,
    bound_names: &HashSet<String>,
) -> Spanned<TirExpr> {
    let span = expr.span;
    let node = match expr.node {
        TirExpr::Const { value, ty } => TirExpr::Const { value, ty },
        TirExpr::Name(mut name_ref) => {
            if matches!(name_ref.kind, TirNameKind::Ident) && !bound_names.contains(&name_ref.name)
            {
                if let Some(imported_name) = rename_map.get(&name_ref.name) {
                    name_ref.name = imported_name.clone();
                    name_ref.name_id = intern_name(imported_name);
                }
            }
            TirExpr::Name(name_ref)
        }
        TirExpr::OperatorRef(op_ref) => {
            TirExpr::OperatorRef(rewrite_operator_ref(op_ref, rename_map, bound_names))
        }
        TirExpr::ArithBinOp { left, op, right } => TirExpr::ArithBinOp {
            left: Box::new(rewrite_operator_refs(*left, rename_map, bound_names)),
            op,
            right: Box::new(rewrite_operator_refs(*right, rename_map, bound_names)),
        },
        TirExpr::ArithNeg(inner) => TirExpr::ArithNeg(Box::new(rewrite_operator_refs(
            *inner,
            rename_map,
            bound_names,
        ))),
        TirExpr::BoolBinOp { left, op, right } => TirExpr::BoolBinOp {
            left: Box::new(rewrite_operator_refs(*left, rename_map, bound_names)),
            op,
            right: Box::new(rewrite_operator_refs(*right, rename_map, bound_names)),
        },
        TirExpr::BoolNot(inner) => TirExpr::BoolNot(Box::new(rewrite_operator_refs(
            *inner,
            rename_map,
            bound_names,
        ))),
        TirExpr::Cmp { left, op, right } => TirExpr::Cmp {
            left: Box::new(rewrite_operator_refs(*left, rename_map, bound_names)),
            op,
            right: Box::new(rewrite_operator_refs(*right, rename_map, bound_names)),
        },
        TirExpr::In { elem, set } => TirExpr::In {
            elem: Box::new(rewrite_operator_refs(*elem, rename_map, bound_names)),
            set: Box::new(rewrite_operator_refs(*set, rename_map, bound_names)),
        },
        TirExpr::Subseteq { left, right } => TirExpr::Subseteq {
            left: Box::new(rewrite_operator_refs(*left, rename_map, bound_names)),
            right: Box::new(rewrite_operator_refs(*right, rename_map, bound_names)),
        },
        TirExpr::Unchanged(inner) => TirExpr::Unchanged(Box::new(rewrite_operator_refs(
            *inner,
            rename_map,
            bound_names,
        ))),
        TirExpr::ActionSubscript {
            kind,
            action,
            subscript,
        } => TirExpr::ActionSubscript {
            kind,
            action: Box::new(rewrite_operator_refs(*action, rename_map, bound_names)),
            subscript: Box::new(rewrite_operator_refs(*subscript, rename_map, bound_names)),
        },
        TirExpr::Always(inner) => TirExpr::Always(Box::new(rewrite_operator_refs(
            *inner,
            rename_map,
            bound_names,
        ))),
        TirExpr::Eventually(inner) => TirExpr::Eventually(Box::new(rewrite_operator_refs(
            *inner,
            rename_map,
            bound_names,
        ))),
        TirExpr::RecordAccess { record, field } => TirExpr::RecordAccess {
            record: Box::new(rewrite_operator_refs(*record, rename_map, bound_names)),
            field,
        },
        TirExpr::Except { base, specs } => TirExpr::Except {
            base: Box::new(rewrite_operator_refs(*base, rename_map, bound_names)),
            specs: specs
                .into_iter()
                .map(|mut spec| {
                    spec.path = spec
                        .path
                        .into_iter()
                        .map(|element| match element {
                            tla_tir::TirExceptPathElement::Index(index) => {
                                tla_tir::TirExceptPathElement::Index(Box::new(
                                    rewrite_operator_refs(*index, rename_map, bound_names),
                                ))
                            }
                            tla_tir::TirExceptPathElement::Field(field) => {
                                tla_tir::TirExceptPathElement::Field(field)
                            }
                        })
                        .collect();
                    spec.value = rewrite_operator_refs(spec.value, rename_map, bound_names);
                    spec
                })
                .collect(),
        },
        TirExpr::ExceptAt => TirExpr::ExceptAt,
        TirExpr::Range { lo, hi } => TirExpr::Range {
            lo: Box::new(rewrite_operator_refs(*lo, rename_map, bound_names)),
            hi: Box::new(rewrite_operator_refs(*hi, rename_map, bound_names)),
        },
        TirExpr::If { cond, then_, else_ } => TirExpr::If {
            cond: Box::new(rewrite_operator_refs(*cond, rename_map, bound_names)),
            then_: Box::new(rewrite_operator_refs(*then_, rename_map, bound_names)),
            else_: Box::new(rewrite_operator_refs(*else_, rename_map, bound_names)),
        },
        TirExpr::Forall { vars, body } => {
            let (vars, bound_names) = rewrite_bound_vars(vars, rename_map, bound_names);
            TirExpr::Forall {
                vars,
                body: Box::new(rewrite_operator_refs(*body, rename_map, &bound_names)),
            }
        }
        TirExpr::Exists { vars, body } => {
            let (vars, bound_names) = rewrite_bound_vars(vars, rename_map, bound_names);
            TirExpr::Exists {
                vars,
                body: Box::new(rewrite_operator_refs(*body, rename_map, &bound_names)),
            }
        }
        TirExpr::Choose { var, body } => {
            let (var, bound_names) = rewrite_bound_var(var, rename_map, bound_names);
            TirExpr::Choose {
                var,
                body: Box::new(rewrite_operator_refs(*body, rename_map, &bound_names)),
            }
        }
        TirExpr::SetEnum(elems) => TirExpr::SetEnum(
            elems
                .into_iter()
                .map(|elem| rewrite_operator_refs(elem, rename_map, bound_names))
                .collect(),
        ),
        TirExpr::SetFilter { var, body } => {
            let (var, bound_names) = rewrite_bound_var(var, rename_map, bound_names);
            TirExpr::SetFilter {
                var,
                body: Box::new(rewrite_operator_refs(*body, rename_map, &bound_names)),
            }
        }
        TirExpr::SetBuilder { body, vars } => {
            let (vars, bound_names) = rewrite_bound_vars(vars, rename_map, bound_names);
            TirExpr::SetBuilder {
                body: Box::new(rewrite_operator_refs(*body, rename_map, &bound_names)),
                vars,
            }
        }
        TirExpr::SetBinOp { left, op, right } => TirExpr::SetBinOp {
            left: Box::new(rewrite_operator_refs(*left, rename_map, bound_names)),
            op,
            right: Box::new(rewrite_operator_refs(*right, rename_map, bound_names)),
        },
        TirExpr::Powerset(inner) => TirExpr::Powerset(Box::new(rewrite_operator_refs(
            *inner,
            rename_map,
            bound_names,
        ))),
        TirExpr::BigUnion(inner) => TirExpr::BigUnion(Box::new(rewrite_operator_refs(
            *inner,
            rename_map,
            bound_names,
        ))),
        TirExpr::KSubset { base, k } => TirExpr::KSubset {
            base: Box::new(rewrite_operator_refs(*base, rename_map, bound_names)),
            k: Box::new(rewrite_operator_refs(*k, rename_map, bound_names)),
        },
        TirExpr::FuncDef { vars, body } => {
            let (vars, bound_names) = rewrite_bound_vars(vars, rename_map, bound_names);
            TirExpr::FuncDef {
                vars,
                body: Box::new(rewrite_operator_refs(*body, rename_map, &bound_names)),
            }
        }
        TirExpr::FuncApply { func, arg } => TirExpr::FuncApply {
            func: Box::new(rewrite_operator_refs(*func, rename_map, bound_names)),
            arg: Box::new(rewrite_operator_refs(*arg, rename_map, bound_names)),
        },
        TirExpr::FuncSet { domain, range } => TirExpr::FuncSet {
            domain: Box::new(rewrite_operator_refs(*domain, rename_map, bound_names)),
            range: Box::new(rewrite_operator_refs(*range, rename_map, bound_names)),
        },
        TirExpr::Domain(inner) => TirExpr::Domain(Box::new(rewrite_operator_refs(
            *inner,
            rename_map,
            bound_names,
        ))),
        TirExpr::Record(fields) => TirExpr::Record(
            fields
                .into_iter()
                .map(|(field, value)| {
                    (field, rewrite_operator_refs(value, rename_map, bound_names))
                })
                .collect(),
        ),
        TirExpr::RecordSet(fields) => TirExpr::RecordSet(
            fields
                .into_iter()
                .map(|(field, value)| {
                    (field, rewrite_operator_refs(value, rename_map, bound_names))
                })
                .collect(),
        ),
        TirExpr::Tuple(elems) => TirExpr::Tuple(
            elems
                .into_iter()
                .map(|elem| rewrite_operator_refs(elem, rename_map, bound_names))
                .collect(),
        ),
        TirExpr::Times(elems) => TirExpr::Times(
            elems
                .into_iter()
                .map(|elem| rewrite_operator_refs(elem, rename_map, bound_names))
                .collect(),
        ),
        TirExpr::Let { defs, body } => {
            let let_bound_names: HashSet<String> = bound_names
                .iter()
                .cloned()
                .chain(defs.iter().map(|def| def.name.clone()))
                .collect();
            TirExpr::Let {
                defs: defs
                    .into_iter()
                    .map(|def| rewrite_let_def(def, rename_map, &let_bound_names))
                    .collect(),
                body: Box::new(rewrite_operator_refs(*body, rename_map, &let_bound_names)),
            }
        }
        TirExpr::Case { arms, other } => TirExpr::Case {
            arms: arms
                .into_iter()
                .map(|mut arm| {
                    arm.guard = rewrite_operator_refs(arm.guard, rename_map, bound_names);
                    arm.body = rewrite_operator_refs(arm.body, rename_map, bound_names);
                    arm
                })
                .collect(),
            other: other
                .map(|other| Box::new(rewrite_operator_refs(*other, rename_map, bound_names))),
        },
        TirExpr::Prime(inner) => TirExpr::Prime(Box::new(rewrite_operator_refs(
            *inner,
            rename_map,
            bound_names,
        ))),
        TirExpr::Apply { op, args } => TirExpr::Apply {
            op: Box::new(rewrite_operator_refs(*op, rename_map, bound_names)),
            args: args
                .into_iter()
                .map(|arg| rewrite_operator_refs(arg, rename_map, bound_names))
                .collect(),
        },
        TirExpr::Lambda {
            params,
            body,
            ast_body,
        } => {
            let lambda_bound_names: HashSet<String> = bound_names
                .iter()
                .cloned()
                .chain(params.iter().cloned())
                .collect();
            TirExpr::Lambda {
                params,
                body: Box::new(rewrite_operator_refs(
                    *body,
                    rename_map,
                    &lambda_bound_names,
                )),
                ast_body,
            }
        }
        TirExpr::OpRef(mut name) => {
            if !bound_names.contains(&name) {
                if let Some(imported_name) = rename_map.get(&name) {
                    name = imported_name.clone();
                }
            }
            TirExpr::OpRef(name)
        }
        TirExpr::Label { name, body } => TirExpr::Label {
            name,
            body: Box::new(rewrite_operator_refs(*body, rename_map, bound_names)),
        },
        TirExpr::LeadsTo { left, right } => TirExpr::LeadsTo {
            left: Box::new(rewrite_operator_refs(*left, rename_map, bound_names)),
            right: Box::new(rewrite_operator_refs(*right, rename_map, bound_names)),
        },
        TirExpr::WeakFair { vars, action } => TirExpr::WeakFair {
            vars: Box::new(rewrite_operator_refs(*vars, rename_map, bound_names)),
            action: Box::new(rewrite_operator_refs(*action, rename_map, bound_names)),
        },
        TirExpr::StrongFair { vars, action } => TirExpr::StrongFair {
            vars: Box::new(rewrite_operator_refs(*vars, rename_map, bound_names)),
            action: Box::new(rewrite_operator_refs(*action, rename_map, bound_names)),
        },
        TirExpr::Enabled(inner) => TirExpr::Enabled(Box::new(rewrite_operator_refs(
            *inner,
            rename_map,
            bound_names,
        ))),
    };
    Spanned::new(node, span)
}

fn rewrite_operator_ref(
    mut op_ref: TirOperatorRef,
    rename_map: &HashMap<String, String>,
    bound_names: &HashSet<String>,
) -> TirOperatorRef {
    op_ref.path = op_ref
        .path
        .into_iter()
        .map(|mut segment| {
            segment.args = segment
                .args
                .into_iter()
                .map(|arg| rewrite_operator_refs(arg, rename_map, bound_names))
                .collect();
            segment
        })
        .collect();
    op_ref.args = op_ref
        .args
        .into_iter()
        .map(|arg| rewrite_operator_refs(arg, rename_map, bound_names))
        .collect();
    if op_ref.path.is_empty() && !bound_names.contains(&op_ref.operator) {
        if let Some(imported_name) = rename_map.get(&op_ref.operator) {
            op_ref.operator = imported_name.clone();
            op_ref.operator_id = intern_name(imported_name);
        }
    }
    op_ref
}

fn rewrite_let_def(
    mut def: TirLetDef,
    rename_map: &HashMap<String, String>,
    bound_names: &HashSet<String>,
) -> TirLetDef {
    def.body = rewrite_operator_refs(def.body, rename_map, bound_names);
    def
}

fn rewrite_bound_vars(
    vars: Vec<TirBoundVar>,
    rename_map: &HashMap<String, String>,
    bound_names: &HashSet<String>,
) -> (Vec<TirBoundVar>, HashSet<String>) {
    let mut rewritten = Vec::with_capacity(vars.len());
    let mut scope_bound_names = bound_names.clone();
    for var in vars {
        let (var, next_bound_names) = rewrite_bound_var(var, rename_map, &scope_bound_names);
        scope_bound_names = next_bound_names;
        rewritten.push(var);
    }
    (rewritten, scope_bound_names)
}

fn rewrite_bound_var(
    mut var: TirBoundVar,
    rename_map: &HashMap<String, String>,
    bound_names: &HashSet<String>,
) -> (TirBoundVar, HashSet<String>) {
    if let Some(domain) = var.domain.take() {
        var.domain = Some(Box::new(rewrite_operator_refs(
            *domain,
            rename_map,
            bound_names,
        )));
    }

    let mut next_bound_names = bound_names.clone();
    next_bound_names.insert(var.name.clone());
    if let Some(pattern) = &var.pattern {
        match pattern {
            TirBoundPattern::Var(name, _) => {
                next_bound_names.insert(name.clone());
            }
            TirBoundPattern::Tuple(names) => {
                for (name, _) in names {
                    next_bound_names.insert(name.clone());
                }
            }
        }
    }

    (var, next_bound_names)
}

/// Check if an expression is an INSTANCE expression (namespace carrier).
fn is_instance_body(expr: &Expr) -> bool {
    match expr {
        Expr::InstanceExpr(_, _) => true,
        Expr::SubstIn(_, body) => is_instance_body(&body.node),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::import_instance_operators;
    use crate::tir_emit::{generate_rust_from_tir_with_modules, TirCodeGenOptions};
    use std::collections::{HashMap, HashSet};
    use std::path::Path;
    use tla_core::ast::Unit;
    use tla_core::{lower, parse_to_syntax_tree, FileId, ModuleLoader, SyntaxNode};
    use tla_tir::{lower_module_for_codegen, TirLoweringEnv, TirModule};

    fn lower_main_module(source: &str) -> (tla_core::ast::Module, SyntaxNode) {
        let tree = parse_to_syntax_tree(source);
        let result = lower(FileId(0), &tree);
        assert!(
            result.errors.is_empty(),
            "lower errors: {:?}",
            result.errors.iter().map(|e| &e.message).collect::<Vec<_>>()
        );
        (result.module.expect("main module"), tree)
    }

    fn lower_tir_with_instance_imports(source: &str) -> TirModule {
        let (module, tree) = lower_main_module(source);
        let spec_path = Path::new("/tmp/tla2-codegen-tir-instance-import.tla");
        let mut loader = ModuleLoader::new(spec_path);
        loader.seed_from_syntax_tree(&tree, spec_path);
        loader.load_extends(&module).expect("load extends");
        loader.load_instances(&module).expect("load instances");

        let dep_modules = loader.modules_for_model_checking(&module);
        let mut env = TirLoweringEnv::new(&module);
        for dep in &dep_modules {
            env.add_module(dep);
        }

        let mut tir_module =
            lower_module_for_codegen(&env, &module).expect("lower module for codegen");
        import_instance_operators(&mut tir_module, &module, &env);
        tir_module
    }

    fn generate_tir_rust(source: &str, invariant_names: &[&str]) -> String {
        let (module, tree) = lower_main_module(source);
        let spec_path = Path::new("/tmp/tla2-codegen-tir-instance-import.tla");
        let mut loader = ModuleLoader::new(spec_path);
        loader.seed_from_syntax_tree(&tree, spec_path);
        loader.load_extends(&module).expect("load extends");
        loader.load_instances(&module).expect("load instances");

        let dep_modules = loader.modules_for_model_checking(&module);
        let mut env = TirLoweringEnv::new(&module);
        for dep in &dep_modules {
            env.add_module(dep);
        }

        let tir_module = lower_module_for_codegen(&env, &module).expect("lower module for codegen");
        let state_vars = module
            .units
            .iter()
            .filter_map(|unit| match &unit.node {
                Unit::Variable(vars) => Some(vars.iter().map(|var| var.node.clone())),
                _ => None,
            })
            .flatten()
            .collect::<Vec<_>>();

        generate_rust_from_tir_with_modules(
            &tir_module,
            &module,
            &env,
            &state_vars,
            &HashMap::new(),
            &invariant_names
                .iter()
                .map(|name| (*name).to_string())
                .collect::<Vec<_>>(),
            &TirCodeGenOptions::default(),
        )
        .expect("generate rust from tir")
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn imports_named_instance_operators_into_tir_module() {
        let tir_module = lower_tir_with_instance_imports(
            r#"
---- MODULE Main ----
VARIABLE x

I == INSTANCE Inner
====

---- MODULE Inner ----
Init == x = 0
Next == x' = x + 1
Helper(v) == v >= 0
InvOk == Helper(x)
====
"#,
        );

        let op_names = tir_module
            .operators
            .iter()
            .map(|op| op.name.as_str())
            .collect::<HashSet<_>>();

        assert!(op_names.contains("I!Init"), "{op_names:?}");
        assert!(op_names.contains("I!Next"), "{op_names:?}");
        assert!(op_names.contains("I!Helper"), "{op_names:?}");
        assert!(op_names.contains("I!InvOk"), "{op_names:?}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn imports_named_instance_substitutions_into_codegen_helpers() {
        let rust = generate_tir_rust(
            r#"
---- MODULE Main ----
VARIABLE x

I == INSTANCE Inner WITH limit <- 5
====

---- MODULE Inner ----
CONSTANT limit
Helper(v) == v >= limit
InvOk == Helper(x)
====
"#,
            &["I!InvOk"],
        );

        assert!(rust.contains("fn check_i_inv_ok"), "{rust}");
        assert!(rust.contains("Self::i_helper(&state.x)") || rust.contains("Self::i_helper(&state.x.clone())"), "{rust}");
        assert!(rust.contains("fn i_helper"), "{rust}");
        assert!(rust.contains("(v >= 5_i64)"), "{rust}");
        assert!(!rust.contains("invariant operator not found"), "{rust}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn imports_unnamed_instance_operators_into_tir_module() {
        let tir_module = lower_tir_with_instance_imports(
            r#"
---- MODULE Main ----
VARIABLE x

INSTANCE Inner
====

---- MODULE Inner ----
Init == x = 0
Next == x' = x + 1
Helper(v) == v >= 0
InvOk == Helper(x)
====
"#,
        );

        let op_names = tir_module
            .operators
            .iter()
            .map(|op| op.name.as_str())
            .collect::<HashSet<_>>();

        assert!(op_names.contains("Init"), "{op_names:?}");
        assert!(op_names.contains("Next"), "{op_names:?}");
        assert!(op_names.contains("Helper"), "{op_names:?}");
        assert!(op_names.contains("InvOk"), "{op_names:?}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn imports_unnamed_instance_with_substitutions() {
        let tir_module = lower_tir_with_instance_imports(
            r#"
---- MODULE Main ----
VARIABLE x

INSTANCE Inner WITH limit <- 10
====

---- MODULE Inner ----
CONSTANT limit
Init == x = limit
Next == x' = x + 1
InvBounded == x >= limit
====
"#,
        );

        let op_names = tir_module
            .operators
            .iter()
            .map(|op| op.name.as_str())
            .collect::<HashSet<_>>();

        assert!(op_names.contains("Init"), "{op_names:?}");
        assert!(op_names.contains("Next"), "{op_names:?}");
        assert!(op_names.contains("InvBounded"), "{op_names:?}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn imports_operators_from_extends_of_instanced_module() {
        let tir_module = lower_tir_with_instance_imports(
            r#"
---- MODULE Main ----
VARIABLE x

INSTANCE Inner
====

---- MODULE Inner ----
EXTENDS Helpers
Init == x = 0
Next == x' = x + 1
InvOk == Helper(x)
====

---- MODULE Helpers ----
Helper(v) == v >= 0
====
"#,
        );

        let op_names = tir_module
            .operators
            .iter()
            .map(|op| op.name.as_str())
            .collect::<HashSet<_>>();

        assert!(op_names.contains("Init"), "{op_names:?}");
        assert!(op_names.contains("Helper"), "{op_names:?}");
        assert!(op_names.contains("InvOk"), "{op_names:?}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn named_instance_generates_prefixed_operator_names() {
        let rust = generate_tir_rust(
            r#"
---- MODULE Main ----
VARIABLE x

I == INSTANCE Inner
====

---- MODULE Inner ----
Init == x = 0
Next == x' = x + 1
InvOk == x >= 0
====
"#,
            &["I!InvOk"],
        );

        assert!(rust.contains("fn check_i_inv_ok"), "{rust}");
        assert!(rust.contains("(state.x >= 0_i64)") || rust.contains("(state.x.clone() >= 0_i64)"), "{rust}");
        assert!(!rust.contains("invariant operator not found"), "{rust}");
    }

    #[cfg_attr(test, ntest::timeout(10000))]
    #[test]
    fn unnamed_instance_generates_tir_code_with_substituted_constants() {
        let rust = generate_tir_rust(
            r#"
---- MODULE Main ----
VARIABLE x

INSTANCE Inner WITH limit <- 5
====

---- MODULE Inner ----
CONSTANT limit
Init == x = limit
Next == x' = x + 1
InvBounded == x >= limit
====
"#,
            &["InvBounded"],
        );

        assert!(rust.contains("fn check_inv_bounded"), "{rust}");
        assert!(rust.contains("x: 5_i64"), "{rust}");
        assert!(rust.contains("(state.x >= 5_i64)") || rust.contains("(state.x.clone() >= 5_i64)"), "{rust}");
    }
}
