// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TIR-based Rust code generation.
//!
//! Generates Rust `StateMachine` implementations from lowered TIR modules.
//! This is the TIR counterpart of the AST-based `emit` module. The TIR path
//! benefits from type information, resolved INSTANCE references, and
//! operator inlining that happen during TIR lowering.
//!
//! Entry point: [`generate_rust_from_tir`].

mod expr;
mod instance_import;
#[cfg(test)]
mod tests;
mod util;

use crate::error::CodegenError;

/// Stack overflow protection for recursive tree walks.
#[inline(always)]
fn stack_safe<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(1024 * 1024, 16 * 1024 * 1024, f)
}
use crate::types::struct_registry::StructRegistry;
use crate::types::TlaType;
use expr::{tir_expr_to_rust, ExprScope};
use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use tla_tir::{
    TirBoolOp, TirBoundVar, TirCmpOp, TirExceptPathElement, TirExpr, TirLetDef, TirModule,
    TirNameKind, TirOperator, TirType,
};
use tla_value::Value;
use util::{to_pascal_case, to_snake_case};

const WRITE_ERR: &str = "writing generated Rust into an in-memory String should not fail";

/// Thread-local set of all operator names in the current TIR module.
/// Used by `tir_expr_to_rust` to emit `false` stubs for action/temporal
/// operators that are not emitted as helpers.
std::thread_local! {
    static ALL_OPERATOR_NAMES: std::cell::RefCell<HashSet<String>> = std::cell::RefCell::new(HashSet::new());
}

/// Thread-local map of operator names to their inferred return types.
/// Used by `infer_element_type_from_tir_set` to resolve Name references
/// to operators (e.g., `Node == 0..N-1` => `Set(Int)`).
std::thread_local! {
    static OPERATOR_RETURN_TYPES: std::cell::RefCell<HashMap<String, TlaType>> = std::cell::RefCell::new(HashMap::new());
}

/// Options for TIR-based code generation.
#[derive(Debug, Clone, Default)]
pub struct TirCodeGenOptions {
    /// Override the module name (defaults to TIR module name).
    pub module_name: Option<String>,
    /// Override the Init operator name (defaults to "Init").
    pub init_name: Option<String>,
    /// Override the Next operator name (defaults to "Next").
    pub next_name: Option<String>,
}

/// Generate Rust code from a lowered TIR module.
///
/// Produces a self-contained Rust source file implementing `StateMachine`
/// for the given TLA+ specification, using TIR type information for
/// more precise Rust type mappings.
pub fn generate_rust_from_tir(
    tir_module: &TirModule,
    state_vars: &[String],
    constants: &HashMap<String, String>,
    invariant_names: &[String],
    options: &TirCodeGenOptions,
) -> Result<String, CodegenError> {
    let mod_name = options
        .module_name
        .as_ref()
        .unwrap_or(&tir_module.name)
        .clone();

    let operators: HashMap<String, &TirOperator> = tir_module
        .operators
        .iter()
        .map(|op| (op.name.clone(), op))
        .collect();

    // Resolve Init/Next operator names (config may override defaults)
    let init_name = options
        .init_name
        .as_deref()
        .unwrap_or("Init")
        .to_string();
    let next_name = options
        .next_name
        .as_deref()
        .unwrap_or("Next")
        .to_string();

    let state_var_set: HashSet<String> = state_vars.iter().cloned().collect();
    let constant_names: HashSet<String> = constants.keys().cloned().collect();

    // Build set of helper operator names (non-Init/Next/Spec/vars, non-action, non-invariant)
    let skip_names: HashSet<String> = [
        init_name.clone(),
        next_name.clone(),
        "Spec".to_string(),
        "vars".to_string(),
    ]
    .into_iter()
    .collect();
    let inv_names_set: HashSet<&str> = invariant_names.iter().map(|s| s.as_str()).collect();
    let helper_names: HashSet<String> = operators
        .values()
        .filter(|op| {
            !skip_names.contains(op.name.as_str())
                && !inv_names_set.contains(op.name.as_str())
                && !contains_prime_with_ops(&op.body, &operators)
                && !expr_contains_temporal(&op.body.node)
        })
        .map(|op| op.name.clone())
        .collect();
    let recursive_helper_names: HashSet<String> = operators
        .values()
        .filter(|op| op.is_recursive && !skip_names.contains(op.name.as_str()))
        .map(|op| op.name.clone())
        .collect();
    // Build helper parameter counts for higher-order operator reference codegen
    let helper_param_counts: HashMap<String, usize> = operators
        .values()
        .filter(|op| helper_names.contains(&op.name))
        .map(|op| (op.name.clone(), op.params.len()))
        .collect();

    // All operator names (including action/temporal that are skipped from helpers).
    // Set thread-local for expr.rs to emit `false` stubs when these names appear.
    ALL_OPERATOR_NAMES.with(|cell| {
        *cell.borrow_mut() = operators.keys().cloned().collect();
    });

    // Also include invariant names (they're also Self:: methods)
    let mut all_method_names = helper_names.clone();
    for inv in invariant_names {
        all_method_names.insert(inv.clone());
    }

    // Build constant type map for Exists-bound variable type inference
    let constant_types: HashMap<String, TlaType> = constants
        .iter()
        .map(|(name, value)| {
            let (rust_type, _) = translate_constant_value_with_name(value, Some(name));
            let tla_ty = match rust_type.as_str() {
                "i64" => TlaType::Int,
                "bool" => TlaType::Bool,
                "String" => TlaType::String,
                "Value" => TlaType::Unknown, // Model values use dynamic Value type
                "set" => {
                    let trimmed = value.trim();
                    if trimmed.contains("{{") {
                        TlaType::Set(Box::new(TlaType::Set(Box::new(infer_set_element_type_from_cfg(trimmed)))))
                    } else {
                        TlaType::Set(Box::new(infer_set_element_type_from_cfg(trimmed)))
                    }
                }
                _ => TlaType::Unknown,
            };
            (name.clone(), tla_ty)
        })
        .collect();

    // Populate operator return types for Name reference resolution in type inference.
    // This allows `infer_element_type_from_tir_set` to resolve references like
    // `Node == 0..N-1` to determine that the element type is Int.
    {
        let mut op_ret_types = HashMap::new();
        for (name, op) in &operators {
            if op.params.is_empty() && !state_var_set.contains(name.as_str()) {
                let ret_ty = infer_type_from_tir_expr(&op.body.node);
                if !matches!(ret_ty, TlaType::Unknown) {
                    op_ret_types.insert(name.clone(), ret_ty);
                }
            }
        }
        // Also include constant types (CONSTANT N = 6 => Int)
        for (name, ty) in &constant_types {
            if !matches!(ty, TlaType::Unknown) {
                op_ret_types.insert(name.clone(), ty.clone());
            }
        }
        OPERATOR_RETURN_TYPES.with(|cell| {
            *cell.borrow_mut() = op_ret_types;
        });
    }

    // Infer variable types from Init operator (with Append-based refinement)
    let var_types = infer_var_types_from_tir(&operators, state_vars, constants, &constant_types, &init_name);

    // Compute set of state variables that are sequences (for FuncApply indexing)
    let seq_vars: HashSet<String> = var_types
        .iter()
        .filter_map(|(name, ty)| {
            if matches!(ty, TlaType::Seq(_)) {
                Some(name.clone())
            } else {
                None
            }
        })
        .collect();

    // Compute helpers that transitively reference state variables
    let helpers_needing_state = compute_helpers_needing_state(&operators, &state_var_set, &skip_names);

    // Build struct registry for type-specialized record structs.
    // Scans variable types and operator bodies for record types with
    // statically-known fields, generating named Rust structs instead of
    // TlaRecord<Value>.
    let struct_registry = build_struct_registry(&var_types, &operators);

    let mut out = String::new();

    // Header
    writeln!(out, "//! Generated from TLA+ module: {}", tir_module.name).expect(WRITE_ERR);
    writeln!(out, "//!").expect(WRITE_ERR);
    writeln!(
        out,
        "//! This file was auto-generated by tla-codegen (TIR path)."
    )
    .expect(WRITE_ERR);
    writeln!(out, "//! Do not edit manually.").expect(WRITE_ERR);
    writeln!(out).expect(WRITE_ERR);
    writeln!(out, "#![allow(unused)]").expect(WRITE_ERR);
    writeln!(out).expect(WRITE_ERR);
    writeln!(out, "use tla_runtime::prelude::*;").expect(WRITE_ERR);
    writeln!(out).expect(WRITE_ERR);

    // Type-specialized record structs
    if struct_registry.has_structs() {
        writeln!(out, "// Type-specialized record structs").expect(WRITE_ERR);
        out.push_str(&struct_registry.emit_all_definitions());
    }

    // Constants
    if !constants.is_empty() {
        writeln!(out, "// Constants from config").expect(WRITE_ERR);
        for (name, value) in constants {
            let const_name = to_snake_case(name);
            let (rust_type, rust_value) = translate_constant_value_with_name(value, Some(name));
            if rust_type == "set" {
                // Complex constant: emit as function returning the set
                let set_ret_ty = constant_types
                    .get(name)
                    .map(|t| t.to_rust_type())
                    .unwrap_or_else(|| "TlaSet<TlaSet<i64>>".to_string());
                writeln!(out, "fn {const_name}() -> {set_ret_ty} {{").expect(WRITE_ERR);
                writeln!(out, "    {rust_value}").expect(WRITE_ERR);
                writeln!(out, "}}").expect(WRITE_ERR);
            } else {
                writeln!(out, "fn {const_name}() -> {rust_type} {{ {rust_value} }}")
                    .expect(WRITE_ERR);
            }
        }
        writeln!(out).expect(WRITE_ERR);
    }

    // State struct
    emit_state_struct(&mut out, &mod_name, state_vars, &var_types, &struct_registry)?;

    // StateMachine trait impl
    emit_state_machine_impl(
        &mut out,
        &mod_name,
        state_vars,
        &state_var_set,
        &constant_names,
        &all_method_names,
        &helpers_needing_state,
        &recursive_helper_names,
        &seq_vars,
        &operators,
        invariant_names,
        constants,
        &struct_registry,
        &helper_param_counts,
        &var_types,
        &init_name,
        &next_name,
    )?;

    // Invariant methods
    if !invariant_names.is_empty() {
        emit_invariant_methods(
            &mut out,
            &mod_name,
            &state_var_set,
            &constant_names,
            &all_method_names,
            &helpers_needing_state,
            &recursive_helper_names,
            &seq_vars,
            &operators,
            invariant_names,
            &struct_registry,
            &helper_param_counts,
            &var_types,
        )?;
    }

    // Helper operator methods
    emit_helper_operators(
        &mut out,
        &mod_name,
        &state_var_set,
        &constant_names,
        &all_method_names,
        &helpers_needing_state,
        &recursive_helper_names,
        &seq_vars,
        &operators,
        state_vars,
        invariant_names,
        &struct_registry,
        &helper_param_counts,
        &var_types,
        &skip_names,
    )?;

    Ok(out)
}

/// Generate Rust code from a TIR module with INSTANCE operator importing.
///
/// Like [`generate_rust_from_tir`], but additionally imports operators from
/// INSTANCE modules (e.g., `INSTANCE M WITH x <- expr` brings Init, Next, and
/// invariants from M into scope). The AST module and TIR lowering environment
/// are needed to resolve INSTANCE declarations and lower the imported operator
/// bodies into TIR.
///
/// This is the TIR counterpart of the AST path's `prepare_module_for_codegen`.
pub fn generate_rust_from_tir_with_modules(
    tir_module: &TirModule,
    ast_module: &tla_core::ast::Module,
    env: &tla_tir::TirLoweringEnv<'_>,
    state_vars: &[String],
    constants: &HashMap<String, String>,
    invariant_names: &[String],
    options: &TirCodeGenOptions,
) -> Result<String, CodegenError> {
    let mut enriched = tir_module.clone();
    instance_import::import_instance_operators(&mut enriched, ast_module, env);
    generate_rust_from_tir(&enriched, state_vars, constants, invariant_names, options)
}

/// Compute which helper operators transitively reference state variables.
///
/// A helper needs state if it directly references a state variable, OR if it
/// calls another helper that needs state. We compute the transitive closure.
fn compute_helpers_needing_state(
    operators: &HashMap<String, &TirOperator>,
    state_vars: &HashSet<String>,
    skip_names: &HashSet<String>,
) -> HashSet<String> {
    // First pass: direct references
    let mut needs_state: HashSet<String> = HashSet::new();
    let mut helper_ops: Vec<&str> = Vec::new();

    for op in operators.values() {
        if skip_names.contains(&op.name) || contains_prime_with_ops(&op.body, operators) {
            continue;
        }
        helper_ops.push(&op.name);
        if expr_references_state_vars(&op.body.node, state_vars) {
            needs_state.insert(op.name.clone());
        }
    }

    // Transitive closure: if helper A calls helper B, and B needs state, then A needs state.
    // Repeat until stable.
    loop {
        let mut changed = false;
        for &op_name in &helper_ops {
            if needs_state.contains(op_name) {
                continue;
            }
            if let Some(op) = operators.get(op_name) {
                if expr_calls_any_of(&op.body.node, &needs_state) {
                    needs_state.insert(op_name.to_string());
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    needs_state
}

/// Build a struct registry from inferred variable types and operator bodies.
///
/// Scans variable types for Record types with statically-known fields and
/// registers them as struct candidates for type-specialized codegen output.
/// Also scans Init/Next operator bodies for record literal patterns to
/// discover struct types that aren't captured by variable type inference.
fn build_struct_registry(
    var_types: &HashMap<String, TlaType>,
    operators: &HashMap<String, &TirOperator>,
) -> StructRegistry {
    let mut registry = StructRegistry::new();
    // Phase 1: Register from inferred variable types
    for ty in var_types.values() {
        register_record_types_from_tla_type(ty, &mut registry);
    }
    // Phase 2: Scan Init/Next/helper operator bodies for record literals
    for op in operators.values() {
        scan_tir_expr_for_records(&op.body.node, &mut registry, var_types);
    }
    registry
}

/// Recursively register Record types found inside a TlaType (including nested
/// types like Set<Record>, Seq<Record>, etc.).
fn register_record_types_from_tla_type(ty: &TlaType, registry: &mut StructRegistry) {
    match ty {
        TlaType::Record(fields) => {
            let fields_vec: Vec<(String, TlaType)> = fields
                .iter()
                .map(|(name, ftype)| (name.clone(), ftype.clone()))
                .collect();
            registry.try_register_record(&fields_vec);
        }
        TlaType::Set(inner) | TlaType::Seq(inner) => {
            register_record_types_from_tla_type(inner, registry);
        }
        TlaType::Func(k, v) => {
            register_record_types_from_tla_type(k, registry);
            register_record_types_from_tla_type(v, registry);
        }
        TlaType::Tuple(elems) => {
            for elem in elems {
                register_record_types_from_tla_type(elem, registry);
            }
        }
        _ => {}
    }
}

/// Scan a TIR expression tree for record literals and register their field
/// patterns in the struct registry. This discovers record types that appear
/// in operator bodies but aren't captured by variable type inference (e.g.,
/// records constructed in Next actions, helper operators, etc.).
fn scan_tir_expr_for_records(
    expr: &TirExpr,
    registry: &mut StructRegistry,
    var_types: &HashMap<String, TlaType>,
) {
    stack_safe(|| scan_tir_expr_for_records_inner(expr, registry, var_types));
}

fn scan_tir_expr_for_records_inner(
    expr: &TirExpr,
    registry: &mut StructRegistry,
    var_types: &HashMap<String, TlaType>,
) {
    match expr {
        TirExpr::Record(fields) => {
            // Try to infer field types from the record literal's value expressions
            let typed_fields: Vec<(String, TlaType)> = fields
                .iter()
                .map(|(f, v)| (f.name.clone(), infer_type_from_tir_expr(&v.node)))
                .collect();
            registry.try_register_record(&typed_fields);
            // Also recurse into field value expressions
            for (_, v) in fields {
                scan_tir_expr_for_records(&v.node, registry, var_types);
            }
        }
        TirExpr::RecordSet(fields) => {
            // RecordSet: [field: SetOfValues, ...] — element type is the element
            // type of each set
            let typed_fields: Vec<(String, TlaType)> = fields
                .iter()
                .map(|(f, v)| (f.name.clone(), infer_element_type_from_tir_set(&v.node)))
                .collect();
            registry.try_register_record(&typed_fields);
            for (_, v) in fields {
                scan_tir_expr_for_records(&v.node, registry, var_types);
            }
        }
        // Recurse into all sub-expressions
        TirExpr::BoolBinOp { left, right, .. }
        | TirExpr::Cmp { left, right, .. }
        | TirExpr::ArithBinOp { left, right, .. }
        | TirExpr::SetBinOp { left, right, .. }
        | TirExpr::Subseteq { left, right, .. } => {
            scan_tir_expr_for_records(&left.node, registry, var_types);
            scan_tir_expr_for_records(&right.node, registry, var_types);
        }
        TirExpr::BoolNot(inner)
        | TirExpr::ArithNeg(inner)
        | TirExpr::Prime(inner)
        | TirExpr::Unchanged(inner)
        | TirExpr::Powerset(inner)
        | TirExpr::BigUnion(inner)
        | TirExpr::Domain(inner) => {
            scan_tir_expr_for_records(&inner.node, registry, var_types);
        }
        TirExpr::Range { lo, hi } => {
            scan_tir_expr_for_records(&lo.node, registry, var_types);
            scan_tir_expr_for_records(&hi.node, registry, var_types);
        }
        TirExpr::In { elem, set } => {
            scan_tir_expr_for_records(&elem.node, registry, var_types);
            scan_tir_expr_for_records(&set.node, registry, var_types);
        }
        TirExpr::If { cond, then_, else_ } => {
            scan_tir_expr_for_records(&cond.node, registry, var_types);
            scan_tir_expr_for_records(&then_.node, registry, var_types);
            scan_tir_expr_for_records(&else_.node, registry, var_types);
        }
        TirExpr::SetEnum(elems) | TirExpr::Tuple(elems) | TirExpr::Times(elems) => {
            for e in elems {
                scan_tir_expr_for_records(&e.node, registry, var_types);
            }
        }
        TirExpr::Forall { body, vars, .. }
        | TirExpr::Exists { body, vars, .. }
        | TirExpr::SetBuilder { body, vars, .. } => {
            for v in vars {
                if let Some(d) = &v.domain {
                    scan_tir_expr_for_records(&d.node, registry, var_types);
                }
            }
            scan_tir_expr_for_records(&body.node, registry, var_types);
        }
        TirExpr::Choose { var, body } | TirExpr::SetFilter { var, body } => {
            if let Some(d) = &var.domain {
                scan_tir_expr_for_records(&d.node, registry, var_types);
            }
            scan_tir_expr_for_records(&body.node, registry, var_types);
        }
        TirExpr::FuncDef { vars, body } => {
            for v in vars {
                if let Some(d) = &v.domain {
                    scan_tir_expr_for_records(&d.node, registry, var_types);
                }
            }
            scan_tir_expr_for_records(&body.node, registry, var_types);
        }
        TirExpr::FuncApply { func, arg } => {
            scan_tir_expr_for_records(&func.node, registry, var_types);
            scan_tir_expr_for_records(&arg.node, registry, var_types);
        }
        TirExpr::RecordAccess { record, .. } => {
            scan_tir_expr_for_records(&record.node, registry, var_types);
        }
        TirExpr::Except { base, specs } => {
            scan_tir_expr_for_records(&base.node, registry, var_types);
            for s in specs {
                scan_tir_expr_for_records(&s.value.node, registry, var_types);
            }
        }
        TirExpr::Let { defs, body } => {
            for d in defs {
                scan_tir_expr_for_records(&d.body.node, registry, var_types);
            }
            scan_tir_expr_for_records(&body.node, registry, var_types);
        }
        TirExpr::Label { body, .. } | TirExpr::Lambda { body, .. } => {
            scan_tir_expr_for_records(&body.node, registry, var_types);
        }
        TirExpr::Case { arms, other } => {
            for a in arms {
                scan_tir_expr_for_records(&a.guard.node, registry, var_types);
                scan_tir_expr_for_records(&a.body.node, registry, var_types);
            }
            if let Some(o) = other {
                scan_tir_expr_for_records(&o.node, registry, var_types);
            }
        }
        TirExpr::Apply { op, args } => {
            scan_tir_expr_for_records(&op.node, registry, var_types);
            for a in args {
                scan_tir_expr_for_records(&a.node, registry, var_types);
            }
        }
        TirExpr::FuncSet { domain, range } => {
            scan_tir_expr_for_records(&domain.node, registry, var_types);
            scan_tir_expr_for_records(&range.node, registry, var_types);
        }
        _ => {}
    }
}

/// Check if a TIR expression calls any operator in the given set.
fn expr_calls_any_of(expr: &TirExpr, names: &HashSet<String>) -> bool {
    stack_safe(|| expr_calls_any_of_inner(expr, names))
}

fn expr_calls_any_of_inner(expr: &TirExpr, names: &HashSet<String>) -> bool {
    match expr {
        TirExpr::Apply { op, args } => {
            if let TirExpr::Name(name_ref) = &op.node {
                if names.contains(&name_ref.name) {
                    return true;
                }
            }
            expr_calls_any_of(&op.node, names)
                || args.iter().any(|a| expr_calls_any_of(&a.node, names))
        }
        TirExpr::BoolBinOp { left, right, .. }
        | TirExpr::Cmp { left, right, .. }
        | TirExpr::ArithBinOp { left, right, .. }
        | TirExpr::SetBinOp { left, right, .. }
        | TirExpr::Subseteq { left, right, .. } => {
            expr_calls_any_of(&left.node, names) || expr_calls_any_of(&right.node, names)
        }
        TirExpr::BoolNot(inner)
        | TirExpr::ArithNeg(inner)
        | TirExpr::Prime(inner)
        | TirExpr::Unchanged(inner)
        | TirExpr::Powerset(inner)
        | TirExpr::BigUnion(inner)
        | TirExpr::Domain(inner) => expr_calls_any_of(&inner.node, names),
        TirExpr::KSubset { base, k } => {
            expr_calls_any_of(&base.node, names) || expr_calls_any_of(&k.node, names)
        }
        TirExpr::Range { lo, hi } => {
            expr_calls_any_of(&lo.node, names) || expr_calls_any_of(&hi.node, names)
        }
        TirExpr::In { elem, set } => {
            expr_calls_any_of(&elem.node, names) || expr_calls_any_of(&set.node, names)
        }
        TirExpr::If { cond, then_, else_ } => {
            expr_calls_any_of(&cond.node, names)
                || expr_calls_any_of(&then_.node, names)
                || expr_calls_any_of(&else_.node, names)
        }
        TirExpr::SetEnum(elems) | TirExpr::Tuple(elems) | TirExpr::Times(elems) => {
            elems.iter().any(|e| expr_calls_any_of(&e.node, names))
        }
        TirExpr::Forall { body, vars, .. }
        | TirExpr::Exists { body, vars, .. }
        | TirExpr::SetBuilder { body, vars, .. } => {
            vars.iter().any(|v| {
                v.domain
                    .as_ref()
                    .map_or(false, |d| expr_calls_any_of(&d.node, names))
            }) || expr_calls_any_of(&body.node, names)
        }
        TirExpr::Choose { var, body } | TirExpr::SetFilter { var, body } => {
            var.domain
                .as_ref()
                .map_or(false, |d| expr_calls_any_of(&d.node, names))
                || expr_calls_any_of(&body.node, names)
        }
        TirExpr::FuncDef { vars, body } => {
            vars.iter().any(|v| {
                v.domain
                    .as_ref()
                    .map_or(false, |d| expr_calls_any_of(&d.node, names))
            }) || expr_calls_any_of(&body.node, names)
        }
        TirExpr::FuncApply { func, arg } => {
            expr_calls_any_of(&func.node, names) || expr_calls_any_of(&arg.node, names)
        }
        TirExpr::Record(fields) => fields
            .iter()
            .any(|(_, v)| expr_calls_any_of(&v.node, names)),
        TirExpr::RecordAccess { record, .. } => expr_calls_any_of(&record.node, names),
        TirExpr::Except { base, specs } => {
            expr_calls_any_of(&base.node, names)
                || specs
                    .iter()
                    .any(|s| expr_calls_any_of(&s.value.node, names))
        }
        TirExpr::Let { defs, body } => {
            defs.iter().any(|d| expr_calls_any_of(&d.body.node, names))
                || expr_calls_any_of(&body.node, names)
        }
        TirExpr::Label { body, .. } | TirExpr::Lambda { body, .. } => {
            expr_calls_any_of(&body.node, names)
        }
        TirExpr::Case { arms, other } => {
            arms.iter().any(|a| {
                expr_calls_any_of(&a.guard.node, names) || expr_calls_any_of(&a.body.node, names)
            }) || other
                .as_ref()
                .map_or(false, |o| expr_calls_any_of(&o.node, names))
        }
        // Zero-arg operator references appear as bare Name nodes in TIR
        TirExpr::Name(name_ref) => names.contains(&name_ref.name),
        _ => false,
    }
}

fn emit_state_struct(
    out: &mut String,
    name: &str,
    variables: &[String],
    var_types: &HashMap<String, TlaType>,
    struct_registry: &StructRegistry,
) -> Result<(), CodegenError> {
    let struct_name = format!("{}State", to_pascal_case(name));
    writeln!(out, "/// State for {name}").expect(WRITE_ERR);
    writeln!(out, "#[derive(Clone, Debug, PartialEq, Eq, Hash)]").expect(WRITE_ERR);
    writeln!(out, "pub struct {struct_name} {{").expect(WRITE_ERR);
    for var in variables {
        let rust_var = to_snake_case(var);
        let rust_type = var_types
            .get(var)
            .map(|t| t.to_rust_type_with_structs(struct_registry))
            .unwrap_or_else(|| "Value".to_string());
        writeln!(out, "    pub {rust_var}: {rust_type},").expect(WRITE_ERR);
    }
    writeln!(out, "}}").expect(WRITE_ERR);
    writeln!(out).expect(WRITE_ERR);
    Ok(())
}

fn emit_state_machine_impl(
    out: &mut String,
    name: &str,
    variables: &[String],
    state_var_set: &HashSet<String>,
    constant_names: &HashSet<String>,
    helper_names: &HashSet<String>,
    helpers_needing_state: &HashSet<String>,
    recursive_helper_names: &HashSet<String>,
    seq_vars: &HashSet<String>,
    operators: &HashMap<String, &TirOperator>,
    invariant_names: &[String],
    constants: &HashMap<String, String>,
    struct_registry: &StructRegistry,
    helper_param_counts: &HashMap<String, usize>,
    var_types: &HashMap<String, TlaType>,
    init_name: &str,
    next_name: &str,
) -> Result<(), CodegenError> {
    let struct_name = to_pascal_case(name);
    let state_name = format!("{struct_name}State");

    writeln!(out, "/// State machine for {name}").expect(WRITE_ERR);
    writeln!(out, "pub struct {struct_name};").expect(WRITE_ERR);
    writeln!(out).expect(WRITE_ERR);
    writeln!(out, "impl StateMachine for {struct_name} {{").expect(WRITE_ERR);
    writeln!(out, "    type State = {state_name};").expect(WRITE_ERR);
    writeln!(out).expect(WRITE_ERR);

    // init()
    writeln!(out, "    fn init(&self) -> Vec<Self::State> {{").expect(WRITE_ERR);
    if let Some(init_op) = operators.get(init_name) {
        emit_init_body(
            out,
            &init_op.body.node,
            variables,
            state_var_set,
            constant_names,
            helper_names,
            helpers_needing_state,
            recursive_helper_names,
            seq_vars,
            constants,
            struct_registry,
            helper_param_counts,
            var_types,
        )?;
    } else {
        writeln!(out, "        // No Init operator found").expect(WRITE_ERR);
        writeln!(out, "        vec![]").expect(WRITE_ERR);
    }
    writeln!(out, "    }}").expect(WRITE_ERR);
    writeln!(out).expect(WRITE_ERR);

    // next()
    writeln!(
        out,
        "    fn next(&self, state: &Self::State) -> Vec<Self::State> {{"
    )
    .expect(WRITE_ERR);
    if let Some(next_op) = operators.get(next_name) {
        emit_next_body(
            out,
            &next_op.body.node,
            variables,
            state_var_set,
            constant_names,
            helper_names,
            helpers_needing_state,
            recursive_helper_names,
            seq_vars,
            operators,
            struct_registry,
            helper_param_counts,
            var_types,
        )?;
    } else {
        writeln!(out, "        // No Next operator found").expect(WRITE_ERR);
        writeln!(out, "        let _ = state;").expect(WRITE_ERR);
        writeln!(out, "        vec![]").expect(WRITE_ERR);
    }
    writeln!(out, "    }}").expect(WRITE_ERR);
    writeln!(out).expect(WRITE_ERR);

    // Invariants
    if !invariant_names.is_empty() {
        // invariant_names()
        writeln!(out, "    fn invariant_names(&self) -> Vec<&'static str> {{").expect(WRITE_ERR);
        let names_str: Vec<_> = invariant_names.iter().map(|n| format!("\"{n}\"")).collect();
        writeln!(out, "        vec![{}]", names_str.join(", ")).expect(WRITE_ERR);
        writeln!(out, "    }}").expect(WRITE_ERR);
        writeln!(out).expect(WRITE_ERR);

        // check_named_invariant()
        writeln!(out, "    fn check_named_invariant(&self, name: &str, state: &Self::State) -> Option<bool> {{").expect(WRITE_ERR);
        writeln!(out, "        match name {{").expect(WRITE_ERR);
        for inv_name in invariant_names {
            writeln!(
                out,
                "            \"{inv_name}\" => Some({struct_name}::check_{fn_name}(state)),",
                fn_name = to_snake_case(inv_name)
            )
            .expect(WRITE_ERR);
        }
        writeln!(out, "            _ => None,").expect(WRITE_ERR);
        writeln!(out, "        }}").expect(WRITE_ERR);
        writeln!(out, "    }}").expect(WRITE_ERR);
        writeln!(out).expect(WRITE_ERR);

        // check_invariant()
        writeln!(
            out,
            "    fn check_invariant(&self, state: &Self::State) -> Option<bool> {{"
        )
        .expect(WRITE_ERR);
        let checks: Vec<_> = invariant_names
            .iter()
            .map(|n| format!("{struct_name}::check_{}(state)", to_snake_case(n)))
            .collect();
        writeln!(out, "        Some({})", checks.join(" && ")).expect(WRITE_ERR);
        writeln!(out, "    }}").expect(WRITE_ERR);
    }

    writeln!(out, "}}").expect(WRITE_ERR);
    writeln!(out).expect(WRITE_ERR);
    Ok(())
}

/// Emit Init body: analyze conjuncts to find variable assignments.
fn emit_init_body(
    out: &mut String,
    expr: &TirExpr,
    variables: &[String],
    state_var_set: &HashSet<String>,
    constant_names: &HashSet<String>,
    helper_names: &HashSet<String>,
    helpers_needing_state: &HashSet<String>,
    recursive_helper_names: &HashSet<String>,
    seq_vars: &HashSet<String>,
    _constants: &HashMap<String, String>,
    struct_registry: &StructRegistry,
    helper_param_counts: &HashMap<String, usize>,
    var_types: &HashMap<String, TlaType>,
) -> Result<(), CodegenError> {
    let mut assignments: HashMap<String, InitAssignment> = HashMap::new();
    analyze_init_conjuncts(expr, &mut assignments, state_var_set);

    let scope = ExprScope::bare(
        state_var_set,
        constant_names,
        helper_names,
        helpers_needing_state,
        recursive_helper_names,
        seq_vars,
    )
    .with_helper_param_counts(helper_param_counts)
    .with_struct_registry(struct_registry)
    .with_var_types(var_types);

    // Check for non-deterministic init (any variable uses \in)
    let has_choice: Vec<_> = variables
        .iter()
        .filter(|v| matches!(assignments.get(*v), Some(InitAssignment::InSet(_))))
        .cloned()
        .collect();

    if has_choice.is_empty() {
        // Deterministic init: single state
        writeln!(out, "        vec![Self::State {{").expect(WRITE_ERR);
        for var in variables {
            let rust_var = to_snake_case(var);
            if let Some(assignment) = assignments.get(var) {
                let val = match assignment {
                    InitAssignment::Eq(expr) => tir_expr_to_rust(expr, &scope),
                    InitAssignment::InSet(_) => unreachable!(),
                };
                let val = wrap_for_value_type(&val, var_types.get(var));
                writeln!(out, "            {rust_var}: {val},").expect(WRITE_ERR);
            } else {
                let default = type_aware_default(var_types.get(var));
                writeln!(out, "            {rust_var}: {default},").expect(WRITE_ERR);
            }
        }
        writeln!(out, "        }}]").expect(WRITE_ERR);
    } else {
        // Non-deterministic: enumerate combinations
        writeln!(out, "        let mut states = Vec::new();").expect(WRITE_ERR);
        for var in &has_choice {
            let rust_var = to_snake_case(var);
            if let Some(InitAssignment::InSet(set_expr)) = assignments.get(var) {
                let set_str = tir_expr_to_rust(set_expr, &scope);
                writeln!(out, "        for {rust_var} in {set_str} {{").expect(WRITE_ERR);
            }
        }
        writeln!(out, "        states.push(Self::State {{").expect(WRITE_ERR);
        for var in variables {
            let rust_var = to_snake_case(var);
            if has_choice.contains(var) {
                let val = wrap_for_value_type(&format!("{rust_var}.clone()"), var_types.get(var));
                writeln!(out, "            {rust_var}: {val},").expect(WRITE_ERR);
            } else if let Some(assignment) = assignments.get(var) {
                let val = match assignment {
                    InitAssignment::Eq(expr) => tir_expr_to_rust(expr, &scope),
                    InitAssignment::InSet(expr) => tir_expr_to_rust(expr, &scope),
                };
                let val = wrap_for_value_type(&val, var_types.get(var));
                writeln!(out, "            {rust_var}: {val},").expect(WRITE_ERR);
            } else {
                let default = type_aware_default(var_types.get(var));
                writeln!(out, "            {rust_var}: {default},").expect(WRITE_ERR);
            }
        }
        writeln!(out, "        }});").expect(WRITE_ERR);
        for _ in &has_choice {
            writeln!(out, "        }}").expect(WRITE_ERR);
        }
        writeln!(out, "        states").expect(WRITE_ERR);
    }
    Ok(())
}

enum InitAssignment {
    Eq(TirExpr),
    InSet(TirExpr),
}

fn analyze_init_conjuncts(
    expr: &TirExpr,
    assignments: &mut HashMap<String, InitAssignment>,
    state_vars: &HashSet<String>,
) {
    let is_state = |name_ref: &tla_tir::TirNameRef| -> bool {
        matches!(name_ref.kind, TirNameKind::StateVar { .. }) || state_vars.contains(&name_ref.name)
    };

    match expr {
        TirExpr::BoolBinOp {
            left,
            op: TirBoolOp::And,
            right,
        } => {
            analyze_init_conjuncts(&left.node, assignments, state_vars);
            analyze_init_conjuncts(&right.node, assignments, state_vars);
        }
        TirExpr::Cmp {
            left,
            op: TirCmpOp::Eq,
            right,
        } => {
            // var = expr
            if let TirExpr::Name(name_ref) = &left.node {
                if is_state(name_ref) {
                    assignments.insert(
                        name_ref.name.clone(),
                        InitAssignment::Eq(right.node.clone()),
                    );
                    return;
                }
            }
            // expr = var (reversed)
            if let TirExpr::Name(name_ref) = &right.node {
                if is_state(name_ref) {
                    assignments
                        .insert(name_ref.name.clone(), InitAssignment::Eq(left.node.clone()));
                }
            }
        }
        TirExpr::In { elem, set } => {
            if let TirExpr::Name(name_ref) = &elem.node {
                if is_state(name_ref) {
                    assignments.insert(
                        name_ref.name.clone(),
                        InitAssignment::InSet(set.node.clone()),
                    );
                }
            }
        }
        TirExpr::Label { body, .. } => {
            analyze_init_conjuncts(&body.node, assignments, state_vars);
        }
        _ => {}
    }
}

/// Emit Next body: collect disjunctive actions and generate transitions.
fn emit_next_body(
    out: &mut String,
    expr: &TirExpr,
    variables: &[String],
    state_var_set: &HashSet<String>,
    constant_names: &HashSet<String>,
    helper_names: &HashSet<String>,
    helpers_needing_state: &HashSet<String>,
    recursive_helper_names: &HashSet<String>,
    seq_vars: &HashSet<String>,
    operators: &HashMap<String, &TirOperator>,
    struct_registry: &StructRegistry,
    helper_param_counts: &HashMap<String, usize>,
    var_types: &HashMap<String, TlaType>,
) -> Result<(), CodegenError> {
    let actions = collect_tir_actions_with_ops(expr, operators);
    let scope = ExprScope::with_state(
        state_var_set,
        constant_names,
        helper_names,
        helpers_needing_state,
        recursive_helper_names,
        seq_vars,
    )
    .with_helper_param_counts(helper_param_counts)
    .with_struct_registry(struct_registry)
    .with_var_types(var_types);

    writeln!(out, "        let mut next_states = Vec::new();").expect(WRITE_ERR);

    for (i, action) in actions.iter().enumerate() {
        writeln!(out, "        // Action {}", i + 1).expect(WRITE_ERR);
        // If the action is a reference to a named operator, resolve it
        let resolved = resolve_action_operator(action, operators);
        emit_single_action(
            out,
            resolved.as_ref().unwrap_or(action),
            variables,
            &scope,
            operators,
        )?;
    }

    writeln!(out, "        next_states").expect(WRITE_ERR);
    Ok(())
}

/// Emit a single sub-action within an Exists for-loop.
///
/// This handles the inner body of `\E i \in S : body` where body may be a
/// single conjunction of primed assignments, or one disjunct of a larger
/// disjunction that has been decomposed by the caller.
fn emit_exists_sub_action(
    out: &mut String,
    body: &TirExpr,
    variables: &[String],
    scope: &ExprScope<'_>,
    operators: &HashMap<String, &TirOperator>,
    outer_analysis: &ActionAnalysis,
) -> Result<(), CodegenError> {
    let inner_analysis = analyze_tir_action(body, operators);

    // Separate inner guards: nested Exists with primed vars become nested loops
    let mut inner_exists: Vec<(&[TirBoundVar], &TirExpr)> = Vec::new();
    let mut inner_pure: Vec<&TirExpr> = Vec::new();
    for g in &inner_analysis.guards {
        if let TirExpr::Exists { vars: ev, body: eb } = g {
            if contains_prime_with_ops(eb, operators) {
                inner_exists.push((ev, &eb.node));
                continue;
            }
        }
        inner_pure.push(g);
    }

    // Emit Let-defs as local variable bindings BEFORE guards,
    // since guards may reference let-bound variables (e.g., PlusCal self).
    for def in &inner_analysis.let_defs {
        let def_name = to_snake_case(&def.name);
        if def.params.is_empty() {
            let val = tir_expr_to_rust(&def.body.node, scope);
            writeln!(out, "        let {def_name} = {val};").expect(WRITE_ERR);
        }
    }

    let inner_guard_parts: Vec<String> = inner_pure
        .iter()
        .map(|g| tir_expr_to_rust(g, scope))
        .collect();
    if !inner_guard_parts.is_empty() {
        writeln!(out, "        if {} {{", inner_guard_parts.join(" && ")).expect(WRITE_ERR);
    }

    // Emit nested Exists as additional for-loops
    let mut nested_analysis: Option<ActionAnalysis> = None;
    let mut nested_depth = 0usize;
    for (evars, ebody) in &inner_exists {
        for ev in *evars {
            let ev_name = to_snake_case(&ev.name);
            let ev_domain = ev
                .domain
                .as_ref()
                .map(|d| tir_expr_to_rust(&d.node, scope))
                .unwrap_or_else(|| "Vec::<Value>::new()".to_string());
            writeln!(out, "        for __{ev_name} in {ev_domain} {{").expect(WRITE_ERR);
            writeln!(out, "        let {ev_name} = __{ev_name}.clone();").expect(WRITE_ERR);
            nested_depth += 1;
        }
        nested_analysis = Some(analyze_tir_action(ebody, operators));
    }
    if let Some(ref na) = nested_analysis {
        for def in &na.let_defs {
            let def_name = to_snake_case(&def.name);
            if def.params.is_empty() {
                let val = tir_expr_to_rust(&def.body.node, scope);
                writeln!(out, "        let {def_name} = {val};").expect(WRITE_ERR);
            }
        }
    }

    // Build state using deepest available assignments
    writeln!(out, "        next_states.push(Self::State {{").expect(WRITE_ERR);
    for var in variables {
        let rust_var = to_snake_case(var);
        let assigned = nested_analysis
            .as_ref()
            .and_then(|na| na.primed_assigns.get(var))
            .or_else(|| inner_analysis.primed_assigns.get(var))
            .or_else(|| outer_analysis.primed_assigns.get(var));
        let is_unchanged = inner_analysis.unchanged.contains(var)
            || outer_analysis.unchanged.contains(var)
            || nested_analysis
                .as_ref()
                .map_or(false, |na| na.unchanged.contains(var));
        if is_unchanged {
            writeln!(out, "            {rust_var}: state.{rust_var}.clone(),")
                .expect(WRITE_ERR);
        } else if let Some(expr) = assigned {
            let val = tir_expr_to_rust(expr, scope);
            let vt = scope.var_types.and_then(|vts| vts.get(var));
            let val = wrap_for_value_type(&val, vt);
            writeln!(out, "            {rust_var}: {val},").expect(WRITE_ERR);
        } else {
            writeln!(out, "            {rust_var}: state.{rust_var}.clone(),")
                .expect(WRITE_ERR);
        }
    }
    writeln!(out, "        }});").expect(WRITE_ERR);

    for _ in 0..nested_depth {
        writeln!(out, "        }}").expect(WRITE_ERR);
    }
    if !inner_guard_parts.is_empty() {
        writeln!(out, "        }}").expect(WRITE_ERR);
    }
    Ok(())
}

/// If an action is a reference to a named operator, resolve it to that
/// operator's body.
///
/// For zero-arg operators, returns the body directly. For operators with
/// parameters, wraps the body in a LET binding that maps parameters to the
/// call-site arguments. This allows `analyze_tir_action` to see the primed
/// assignments inside the operator body (Bug 4 fix, #3912).
fn resolve_action_operator(
    action: &TirExpr,
    operators: &HashMap<String, &TirOperator>,
) -> Option<TirExpr> {
    match action {
        TirExpr::Name(name_ref) => {
            if let Some(op) = operators.get(&name_ref.name) {
                if op.params.is_empty() {
                    return Some(op.body.node.clone());
                }
            }
            None
        }
        TirExpr::Apply { op, args } => {
            if let TirExpr::Name(name_ref) = &op.node {
                if let Some(op_def) = operators.get(&name_ref.name) {
                    if op_def.params.is_empty() && args.is_empty() {
                        return Some(op_def.body.node.clone());
                    }
                    // Parameterized operator: wrap body in Let bindings that
                    // bind each parameter to its argument expression.
                    if op_def.params.len() == args.len() && !args.is_empty() {
                        let defs: Vec<TirLetDef> = op_def
                            .params
                            .iter()
                            .zip(args.iter())
                            .map(|(param, arg)| TirLetDef {
                                name: param.clone(),
                                name_id: tla_core::intern_name(param),
                                params: Vec::new(),
                                body: arg.clone(),
                            })
                            .collect();
                        return Some(TirExpr::Let {
                            defs,
                            body: Box::new(op_def.body.clone()),
                        });
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Collect top-level disjunctions as separate actions, resolving operator
/// references to expose nested disjunctions (e.g., `Next == \E self: p(self)`
/// where `p(self) == a(self) \/ b(self) \/ ...`).
fn collect_tir_actions(expr: &TirExpr) -> Vec<TirExpr> {
    collect_tir_actions_with_ops(expr, &HashMap::new())
}

/// Collect top-level disjunctions as separate actions, resolving through
/// operator references to expose nested disjunctions.
fn collect_tir_actions_with_ops(
    expr: &TirExpr,
    operators: &HashMap<String, &TirOperator>,
) -> Vec<TirExpr> {
    match expr {
        TirExpr::BoolBinOp {
            left,
            op: TirBoolOp::Or,
            right,
        } => {
            let mut actions = collect_tir_actions_with_ops(&left.node, operators);
            actions.extend(collect_tir_actions_with_ops(&right.node, operators));
            actions
        }
        TirExpr::Label { body, .. } => collect_tir_actions_with_ops(&body.node, operators),
        // Resolve operator references to expose disjunctions inside them
        TirExpr::Name(_) | TirExpr::Apply { .. } if !operators.is_empty() => {
            if let Some(resolved) = resolve_action_operator(expr, operators) {
                // Check if the resolved body is a disjunction — if so, collect sub-actions
                if is_disjunction(&resolved) {
                    return collect_tir_actions_with_ops(&resolved, operators);
                }
                // Otherwise use the resolved body as a single action
                return vec![resolved];
            }
            vec![expr.clone()]
        }
        _ => vec![expr.clone()],
    }
}

/// Check if an expression is a top-level disjunction (Or) or Let wrapping one.
fn is_disjunction(expr: &TirExpr) -> bool {
    match expr {
        TirExpr::BoolBinOp {
            op: TirBoolOp::Or, ..
        } => true,
        TirExpr::Let { body, .. } => is_disjunction(&body.node),
        TirExpr::Label { body, .. } => is_disjunction(&body.node),
        _ => false,
    }
}

struct ActionAnalysis {
    guards: Vec<TirExpr>,
    primed_assigns: HashMap<String, TirExpr>,
    unchanged: HashSet<String>,
    let_defs: Vec<TirLetDef>,
}

fn analyze_tir_action(
    expr: &TirExpr,
    operators: &HashMap<String, &TirOperator>,
) -> ActionAnalysis {
    let mut analysis = ActionAnalysis {
        guards: Vec::new(),
        primed_assigns: HashMap::new(),
        unchanged: HashSet::new(),
        let_defs: Vec::new(),
    };
    analyze_tir_action_inner(expr, &mut analysis, operators);
    analysis
}

fn analyze_tir_action_inner(
    expr: &TirExpr,
    analysis: &mut ActionAnalysis,
    operators: &HashMap<String, &TirOperator>,
) {
    match expr {
        TirExpr::BoolBinOp {
            left,
            op: TirBoolOp::And,
            right,
        } => {
            analyze_tir_action_inner(&left.node, analysis, operators);
            analyze_tir_action_inner(&right.node, analysis, operators);
        }
        TirExpr::Cmp {
            left,
            op: TirCmpOp::Eq,
            right,
        } => {
            // x' = expr
            if let TirExpr::Prime(inner) = &left.node {
                if let TirExpr::Name(name_ref) = &inner.node {
                    analysis
                        .primed_assigns
                        .insert(name_ref.name.clone(), right.node.clone());
                    return;
                }
            }
            analysis.guards.push(expr.clone());
        }
        TirExpr::In { elem, .. } => {
            // x' \in S
            if let TirExpr::Prime(inner) = &elem.node {
                if let TirExpr::Name(name_ref) = &inner.node {
                    analysis
                        .primed_assigns
                        .insert(name_ref.name.clone(), expr.clone());
                    return;
                }
            }
            analysis.guards.push(expr.clone());
        }
        TirExpr::Unchanged(inner) => {
            collect_unchanged_vars(&inner.node, &mut analysis.unchanged);
        }
        // Exists at top level for non-deterministic actions like
        // \E v \in S : /\ guard /\ x' = f(v)
        TirExpr::Exists { .. } => {
            // Non-deterministic choice at action level — pushed as a guard,
            // then expanded during action emission.
            analysis.guards.push(expr.clone());
        }
        // IF cond THEN (primed assignments) ELSE (primed assignments)
        // Synthesize conditional primed assignments from both branches.
        TirExpr::If { cond, then_, else_ } => {
            let then_analysis = analyze_tir_action(&then_.node, operators);
            let else_analysis = analyze_tir_action(&else_.node, operators);

            // If both branches contain primed assignments, synthesize conditional
            // expressions: var' = IF cond THEN then_val ELSE else_val
            if !then_analysis.primed_assigns.is_empty()
                || !else_analysis.primed_assigns.is_empty()
            {
                // Merge primed assignments from both branches using IF/THEN/ELSE
                let all_vars: HashSet<String> = then_analysis
                    .primed_assigns
                    .keys()
                    .chain(else_analysis.primed_assigns.keys())
                    .cloned()
                    .collect();

                for var in all_vars {
                    let then_expr = then_analysis.primed_assigns.get(&var);
                    let else_expr = else_analysis.primed_assigns.get(&var);
                    if let (Some(t), Some(e)) = (then_expr, else_expr) {
                        // Both branches assign this variable: synthesize conditional
                        let dummy_span = tla_core::Span::default();
                        let cond_assign = TirExpr::If {
                            cond: Box::new(tla_core::Spanned {
                                node: cond.node.clone(),
                                span: dummy_span,
                            }),
                            then_: Box::new(tla_core::Spanned {
                                node: t.clone(),
                                span: dummy_span,
                            }),
                            else_: Box::new(tla_core::Spanned {
                                node: e.clone(),
                                span: dummy_span,
                            }),
                        };
                        analysis.primed_assigns.insert(var, cond_assign);
                    } else if let Some(t) = then_expr {
                        // Only THEN branch assigns: use the THEN value when condition holds
                        analysis.primed_assigns.insert(var, t.clone());
                    } else if let Some(e) = else_expr {
                        // Only ELSE branch assigns: use the ELSE value when condition fails
                        analysis.primed_assigns.insert(var, e.clone());
                    }
                }

                // Merge unchanged from both branches (variable is unchanged if
                // unchanged in BOTH branches)
                for var in &then_analysis.unchanged {
                    if else_analysis.unchanged.contains(var) {
                        analysis.unchanged.insert(var.clone());
                    }
                }

                // Merge let_defs from both branches
                analysis.let_defs.extend(then_analysis.let_defs);
                analysis.let_defs.extend(else_analysis.let_defs);
            } else {
                // Neither branch has primed assignments; treat as a guard
                analysis.guards.push(expr.clone());
            }
        }
        TirExpr::Let { defs, body } => {
            // Collect Let-defs as local variable bindings that will be emitted
            // before the state construction. Then recurse into body.
            for def in defs {
                analysis.let_defs.push(def.clone());
            }
            analyze_tir_action_inner(&body.node, analysis, operators);
        }
        TirExpr::Label { body, .. } => {
            analyze_tir_action_inner(&body.node, analysis, operators);
        }
        // Resolve operator references: Name("Op") -> expand Op's body
        TirExpr::Name(name_ref) if name_ref.kind == TirNameKind::Ident => {
            if let Some(resolved) = resolve_action_operator(expr, operators) {
                analyze_tir_action_inner(&resolved, analysis, operators);
            } else {
                analysis.guards.push(expr.clone());
            }
        }
        // Resolve parameterized operator calls: Apply(Name("Op"), args)
        TirExpr::Apply { .. } => {
            if let Some(resolved) = resolve_action_operator(expr, operators) {
                analyze_tir_action_inner(&resolved, analysis, operators);
            } else {
                analysis.guards.push(expr.clone());
            }
        }
        _ => {
            analysis.guards.push(expr.clone());
        }
    }
}

fn collect_unchanged_vars(expr: &TirExpr, unchanged: &mut HashSet<String>) {
    match expr {
        TirExpr::Name(name_ref) => {
            unchanged.insert(name_ref.name.clone());
        }
        TirExpr::Tuple(elems) => {
            for elem in elems {
                collect_unchanged_vars(&elem.node, unchanged);
            }
        }
        _ => {}
    }
}

fn emit_single_action(
    out: &mut String,
    action: &TirExpr,
    variables: &[String],
    scope: &ExprScope<'_>,
    operators: &HashMap<String, &TirOperator>,
) -> Result<(), CodegenError> {
    let analysis = analyze_tir_action(action, operators);

    // Check for top-level Exists guards (non-deterministic choice)
    let mut exists_loops: Vec<(&[TirBoundVar], &TirExpr)> = Vec::new();
    let mut pure_guards: Vec<&TirExpr> = Vec::new();

    for guard in &analysis.guards {
        if let TirExpr::Exists { vars, body } = guard {
            // Check if this is a top-level nondeterministic choice that contains primed assignments
            if contains_prime_with_ops(body, operators) {
                exists_loops.push((vars, &body.node));
                continue;
            }
        }
        pure_guards.push(guard);
    }

    // If there are exists loops with primed assignments, handle them
    if !exists_loops.is_empty() {
        // Emit pure guards first
        let guard_parts: Vec<String> = pure_guards
            .iter()
            .map(|g| tir_expr_to_rust(g, scope))
            .collect();

        if !guard_parts.is_empty() {
            writeln!(out, "        if {} {{", guard_parts.join(" && ")).expect(WRITE_ERR);
        }

        // For each exists loop, emit a for loop.
        // Use __var prefix to avoid shadowing constant functions with the
        // same name (e.g., `for h in h()` where `h` is both a constant and
        // loop variable).
        for (vars, body) in &exists_loops {
            // Emit all for-loops first, then bind clean names, so domain
            // expressions of nested loops don't see shadowed names.
            for var in *vars {
                let var_name = to_snake_case(&var.name);
                let domain = var
                    .domain
                    .as_ref()
                    .map(|d| tir_expr_to_rust(&d.node, scope))
                    .unwrap_or_else(|| "Vec::<Value>::new()".to_string());
                writeln!(out, "        for __{var_name} in {domain} {{").expect(WRITE_ERR);
            }
            // Now bind clean names (after all for-loop domains are evaluated)
            for var in *vars {
                let var_name = to_snake_case(&var.name);
                writeln!(out, "        let {var_name} = __{var_name}.clone();").expect(WRITE_ERR);
            }

            // Check if the body is a disjunction of action operators.
            // Pattern: \E i \in S : Action1(i) \/ Action2(i) \/ ...
            // Each disjunct is a separate action with its own primed assignments.
            let sub_actions = collect_tir_actions_with_ops(body, operators);
            if sub_actions.len() > 1 {
                // Multiple sub-actions: emit each one separately within the for-loop
                for (j, sub_action) in sub_actions.iter().enumerate() {
                    writeln!(out, "        // Sub-action {}", j + 1).expect(WRITE_ERR);
                    emit_exists_sub_action(
                        out,
                        sub_action,
                        variables,
                        scope,
                        operators,
                        &analysis,
                    )?;
                }
            } else {
                // Single action body (the original path)
                emit_exists_sub_action(
                    out,
                    body,
                    variables,
                    scope,
                    operators,
                    &analysis,
                )?;
            }

            for _ in *vars {
                writeln!(out, "        }}").expect(WRITE_ERR);
            }
        }

        if !guard_parts.is_empty() {
            writeln!(out, "        }}").expect(WRITE_ERR);
        }
        return Ok(());
    }

    // Simple case: no top-level Exists with primed assignments
    // Check for non-deterministic choice in primed assigns (x' \in S)
    let loop_choices: Vec<(String, TirExpr)> = analysis
        .primed_assigns
        .iter()
        .filter_map(|(var, expr)| {
            if let TirExpr::In { elem, set } = expr {
                if let TirExpr::Prime(_) = &elem.node {
                    if !analysis.unchanged.contains(var) {
                        return Some((var.clone(), set.node.clone()));
                    }
                }
            }
            None
        })
        .collect();
    let loop_choice_vars: HashSet<_> = loop_choices.iter().map(|(v, _)| v.clone()).collect();

    // Emit guards
    let guard_parts: Vec<String> = pure_guards
        .iter()
        .map(|g| tir_expr_to_rust(g, scope))
        .collect();

    if !guard_parts.is_empty() {
        writeln!(out, "        if {} {{", guard_parts.join(" && ")).expect(WRITE_ERR);
    }

    // Emit Let-defs as local variable bindings
    for def in &analysis.let_defs {
        let def_name = to_snake_case(&def.name);
        if def.params.is_empty() {
            let val = tir_expr_to_rust(&def.body.node, scope);
            writeln!(out, "        let {def_name} = {val};").expect(WRITE_ERR);
        }
    }

    // Emit loops for non-deterministic choices
    for (var, set_expr) in &loop_choices {
        let rust_var = to_snake_case(var);
        let set_str = tir_expr_to_rust(&set_expr, scope);
        writeln!(out, "        for {rust_var}_next in {set_str} {{").expect(WRITE_ERR);
    }

    // Emit primed variable bindings for cross-references.
    // When a primed assignment RHS references another primed variable (e.g.,
    // small' = small - (big' - big)), we need to compute the values first.
    // Emit `let var_next = expr;` for each primed assignment, then use the
    // _next bindings in the state constructor.
    let has_prime_cross_ref = analysis.primed_assigns.iter().any(|(_, expr)| {
        expr_contains_prime(expr)
    });
    if has_prime_cross_ref || analysis.primed_assigns.len() > 1 {
        // Emit let bindings for all primed assignments in variable order
        for var in variables {
            let rust_var = to_snake_case(var);
            if loop_choice_vars.contains(var) || analysis.unchanged.contains(var) {
                continue;
            }
            if let Some(expr) = analysis.primed_assigns.get(var) {
                let val = tir_expr_to_rust(expr, scope);
                writeln!(out, "        let {rust_var}_next = {val};").expect(WRITE_ERR);
            }
        }
    }

    // Build next state
    writeln!(out, "        next_states.push(Self::State {{").expect(WRITE_ERR);
    for var in variables {
        let rust_var = to_snake_case(var);
        let vt = scope.var_types.and_then(|vts| vts.get(var));
        if loop_choice_vars.contains(var) {
            let val = wrap_for_value_type(&format!("{rust_var}_next.clone()"), vt);
            writeln!(out, "            {rust_var}: {val},").expect(WRITE_ERR);
        } else if analysis.unchanged.contains(var) {
            writeln!(out, "            {rust_var}: state.{rust_var}.clone(),").expect(WRITE_ERR);
        } else if analysis.primed_assigns.contains_key(var) {
            if has_prime_cross_ref || analysis.primed_assigns.len() > 1 {
                // Use the pre-computed binding
                let val = wrap_for_value_type(&format!("{rust_var}_next.clone()"), vt);
                writeln!(out, "            {rust_var}: {val},").expect(WRITE_ERR);
            } else {
                let val = tir_expr_to_rust(analysis.primed_assigns.get(var).expect("checked"), scope);
                let val = wrap_for_value_type(&val, vt);
                writeln!(out, "            {rust_var}: {val},").expect(WRITE_ERR);
            }
        } else {
            writeln!(out, "            {rust_var}: state.{rust_var}.clone(),").expect(WRITE_ERR);
        }
    }
    writeln!(out, "        }});").expect(WRITE_ERR);

    // Close loops
    for _ in &loop_choices {
        writeln!(out, "        }}").expect(WRITE_ERR);
    }
    if !guard_parts.is_empty() {
        writeln!(out, "        }}").expect(WRITE_ERR);
    }
    Ok(())
}

fn contains_prime_with_ops(
    expr: &tla_core::Spanned<TirExpr>,
    operators: &HashMap<String, &TirOperator>,
) -> bool {
    stack_safe(|| contains_prime_with_ops_inner(expr, operators))
}

fn contains_prime_with_ops_inner(
    expr: &tla_core::Spanned<TirExpr>,
    operators: &HashMap<String, &TirOperator>,
) -> bool {
    match &expr.node {
        TirExpr::Prime(_) => true,
        TirExpr::BoolBinOp { left, right, .. } => {
            contains_prime_with_ops(left, operators)
                || contains_prime_with_ops(right, operators)
        }
        TirExpr::Cmp { left, right, .. } => {
            contains_prime_with_ops(left, operators)
                || contains_prime_with_ops(right, operators)
        }
        TirExpr::In { elem, set } => {
            contains_prime_with_ops(elem, operators)
                || contains_prime_with_ops(set, operators)
        }
        TirExpr::Unchanged(_) => true,
        TirExpr::Label { body, .. } => contains_prime_with_ops(body, operators),
        TirExpr::Let { body, defs } => {
            contains_prime_with_ops(body, operators)
                || defs.iter().any(|d| contains_prime_with_ops(&d.body, operators))
        }
        TirExpr::Exists { body, .. } | TirExpr::Forall { body, .. } => {
            contains_prime_with_ops(body, operators)
        }
        // Look through operator references: Name("Op") may reference an
        // operator whose body contains primed assignments.
        TirExpr::Name(name_ref) if name_ref.kind == TirNameKind::Ident => {
            if let Some(op) = operators.get(&name_ref.name) {
                expr_contains_prime(&op.body.node)
            } else {
                false
            }
        }
        // Look through parameterized operator calls: Apply(Name("Op"), args)
        TirExpr::Apply { op, args } => {
            if let TirExpr::Name(name_ref) = &op.node {
                if let Some(op_def) = operators.get(&name_ref.name) {
                    if expr_contains_prime(&op_def.body.node) {
                        return true;
                    }
                }
            }
            // Also check if args themselves contain primes
            contains_prime_with_ops(op, operators)
                || args.iter().any(|a| contains_prime_with_ops(a, operators))
        }
        _ => false,
    }
}

fn emit_invariant_methods(
    out: &mut String,
    name: &str,
    state_var_set: &HashSet<String>,
    constant_names: &HashSet<String>,
    helper_names: &HashSet<String>,
    helpers_needing_state: &HashSet<String>,
    recursive_helper_names: &HashSet<String>,
    seq_vars: &HashSet<String>,
    operators: &HashMap<String, &TirOperator>,
    invariant_names: &[String],
    struct_registry: &StructRegistry,
    helper_param_counts: &HashMap<String, usize>,
    var_types: &HashMap<String, TlaType>,
) -> Result<(), CodegenError> {
    let struct_name = to_pascal_case(name);
    let state_name = format!("{struct_name}State");
    let inv_name_set: HashSet<String> = invariant_names.iter().cloned().collect();
    let scope = ExprScope::with_state(
        state_var_set,
        constant_names,
        helper_names,
        helpers_needing_state,
        recursive_helper_names,
        seq_vars,
    )
    .with_helper_param_counts(helper_param_counts)
    .with_struct_registry(struct_registry)
    .with_var_types(var_types)
    .with_invariant_names(&inv_name_set);

    writeln!(out, "impl {struct_name} {{").expect(WRITE_ERR);
    for inv_name in invariant_names {
        let fn_name = to_snake_case(inv_name);
        writeln!(
            out,
            "    fn check_{fn_name}(state: &{state_name}) -> bool {{"
        )
        .expect(WRITE_ERR);
        if let Some(op) = operators.get(inv_name) {
            if op.is_recursive {
                writeln!(out, "        Self::{fn_name}(state, 0)").expect(WRITE_ERR);
            } else {
                let expr_str = tir_expr_to_rust(&op.body.node, &scope);
                writeln!(out, "        {expr_str}").expect(WRITE_ERR);
            }
        } else {
            writeln!(out, "        true // invariant operator not found").expect(WRITE_ERR);
        }
        writeln!(out, "    }}").expect(WRITE_ERR);
        writeln!(out).expect(WRITE_ERR);
    }
    writeln!(out, "}}").expect(WRITE_ERR);
    writeln!(out).expect(WRITE_ERR);
    Ok(())
}

fn emit_helper_operators(
    out: &mut String,
    name: &str,
    state_var_set: &HashSet<String>,
    constant_names: &HashSet<String>,
    helper_names: &HashSet<String>,
    helpers_needing_state: &HashSet<String>,
    recursive_helper_names: &HashSet<String>,
    seq_vars: &HashSet<String>,
    operators: &HashMap<String, &TirOperator>,
    _variables: &[String],
    invariant_names: &[String],
    struct_registry: &StructRegistry,
    helper_param_counts: &HashMap<String, usize>,
    var_types: &HashMap<String, TlaType>,
    skip_names: &HashSet<String>,
) -> Result<(), CodegenError> {
    // Emit non-Init, non-Next, non-invariant operators as helper functions
    let inv_set: HashSet<&str> = invariant_names.iter().map(|s| s.as_str()).collect();

    let struct_name = to_pascal_case(name);
    let state_name = format!("{struct_name}State");

    let mut helpers: Vec<&TirOperator> = Vec::new();
    for op in operators.values() {
        if skip_names.contains(&op.name) {
            continue;
        }
        if !op.is_recursive && inv_set.contains(op.name.as_str()) {
            continue;
        }
        // Skip non-recursive action operators (contain primed variables,
        // including transitively through operator references)
        if !op.is_recursive && contains_prime_with_ops(&op.body, operators) {
            continue;
        }
        // Skip operators containing temporal constructs (Always, Eventually, etc.)
        if !op.is_recursive && expr_contains_temporal(&op.body.node) {
            continue;
        }
        helpers.push(op);
    }

    if helpers.is_empty() {
        return Ok(());
    }

    // Emit helpers as methods on the state machine impl block
    // Helpers that reference state vars get a `state` parameter
    writeln!(out, "// Helper operators").expect(WRITE_ERR);
    writeln!(out, "impl {struct_name} {{").expect(WRITE_ERR);
    if helpers.iter().any(|op| op.is_recursive) {
        writeln!(out, "    const MAX_RECURSION_DEPTH: u32 = 10000;").expect(WRITE_ERR);
        writeln!(out).expect(WRITE_ERR);
    }
    for op in &helpers {
        let fn_name = to_snake_case(&op.name);
        let needs_state = helpers_needing_state.contains(&op.name);
        let scope = ExprScope::with_state(
            state_var_set,
            constant_names,
            helper_names,
            helpers_needing_state,
            recursive_helper_names,
            seq_vars,
        )
        .with_helper_param_counts(helper_param_counts)
        .with_struct_registry(struct_registry)
        .with_var_types(var_types);
        let scope = if op.is_recursive {
            scope.with_recursive_depth("__depth")
        } else {
            scope
        };

        let mut params: Vec<String> = Vec::new();
        if needs_state {
            params.push(format!("state: &{state_name}"));
        }
        // Infer param types from how they're used in the body.
        // Params that are used with .iter()/.contains() get the type of their
        // domain from calling context. For now, use generic type params so Rust
        // infers the correct type from each call site.
        let mut generic_params: Vec<String> = Vec::new();
        for (idx, p) in op.params.iter().enumerate() {
            let mut param_type = infer_param_type_with_ops(&op.body.node, p, operators);
            // If direct inference failed, try FuncApply-based inference:
            // when the param is used as a key in state_var.apply(&param),
            // infer the type from the function's key type.
            if param_type == "_" {
                if let Some(key_ty) = infer_param_from_func_apply(&op.body.node, p, state_var_set, var_types) {
                    let ty_str = key_ty.to_rust_type();
                    if ty_str != "Value" {
                        param_type = ty_str;
                    }
                }
            }
            if param_type == "_" {
                // Use a generic: P0, P1, etc.
                let gen_name = format!("P{idx}");
                generic_params.push(gen_name.clone());
                params.push(format!("{}: &{gen_name}", to_snake_case(p)));
            } else {
                params.push(format!("{}: &{param_type}", to_snake_case(p)));
            }
        }
        if op.is_recursive {
            params.push("__depth: u32".to_string());
        }

        let body = tir_expr_to_rust(&op.body.node, &scope);

        // Infer return type from body structure, resolving through operator defs
        let ret_type = infer_return_type_hint_with_vars(&op.body.node, Some(operators), var_types);
        if generic_params.is_empty() {
            writeln!(
                out,
                "    fn {fn_name}({}) -> {ret_type} {{",
                params.join(", ")
            )
            .expect(WRITE_ERR);
        } else {
            writeln!(
                out,
                "    fn {fn_name}<{}>({}) -> {ret_type} {{",
                generic_params.join(", "),
                params.join(", ")
            )
            .expect(WRITE_ERR);
        }
        if op.is_recursive {
            // Stack overflow protection: wrap recursive body in stacker guard
            // (1MB red zone, 16MB growth — matches evaluator constants).
            writeln!(out, "        recursive_stack_guard(|| {{").expect(WRITE_ERR);
            writeln!(out, "        if __depth > Self::MAX_RECURSION_DEPTH {{").expect(WRITE_ERR);
            writeln!(
                out,
                "            panic!(\"recursive operator {} exceeded max recursion depth {{}}\", Self::MAX_RECURSION_DEPTH);",
                op.name
            )
            .expect(WRITE_ERR);
            writeln!(out, "        }}").expect(WRITE_ERR);
        }
        // Clone params into owned local bindings so body can use them by value.
        // Params are passed as &T, so .clone() produces T.
        for p in &op.params {
            let pname = to_snake_case(p);
            writeln!(out, "        let {pname} = {pname}.clone();").expect(WRITE_ERR);
        }
        // Bind the body to a local to avoid drop-order issues when the body
        // borrows a cloned parameter (e.g., `c.iter().all(|...|)` where `c` is
        // cloned from a reference parameter).
        writeln!(out, "        let __r = {body};").expect(WRITE_ERR);
        // Add .into() for type coercion between Value and concrete types.
        // Handles both directions: concrete→Value and Value→concrete (e.g.,
        // when TlaRecord<Value>.get() returns Value but function returns i64).
        // Skip when generic type parameters are present because we cannot
        // guarantee that arbitrary P0/P1 implement Into<_>.
        // Only apply for simple concrete types where From/Into impls exist.
        let needs_into = generic_params.is_empty()
            && matches!(ret_type.as_str(), "Value" | "i64" | "bool" | "String");
        let ret_expr = if needs_into { "__r.into()" } else { "__r" };
        if op.is_recursive {
            writeln!(out, "        {ret_expr}").expect(WRITE_ERR);
            writeln!(out, "        }})").expect(WRITE_ERR);
        } else {
            writeln!(out, "        {ret_expr}").expect(WRITE_ERR);
        }
        writeln!(out, "    }}").expect(WRITE_ERR);
        writeln!(out).expect(WRITE_ERR);
    }
    writeln!(out, "}}").expect(WRITE_ERR);
    writeln!(out).expect(WRITE_ERR);

    Ok(())
}

/// Check if a TIR expression contains any state variable references.
fn expr_references_state_vars(expr: &TirExpr, state_vars: &HashSet<String>) -> bool {
    stack_safe(|| expr_references_state_vars_inner(expr, state_vars))
}

fn expr_references_state_vars_inner(expr: &TirExpr, state_vars: &HashSet<String>) -> bool {
    match expr {
        TirExpr::Name(name_ref) => {
            matches!(name_ref.kind, TirNameKind::StateVar { .. })
                || state_vars.contains(&name_ref.name)
        }
        TirExpr::Const { .. } | TirExpr::ExceptAt => false,
        TirExpr::BoolBinOp { left, right, .. }
        | TirExpr::Cmp { left, right, .. }
        | TirExpr::ArithBinOp { left, right, .. }
        | TirExpr::SetBinOp { left, right, .. }
        | TirExpr::Subseteq { left, right, .. } => {
            expr_references_state_vars(&left.node, state_vars)
                || expr_references_state_vars(&right.node, state_vars)
        }
        TirExpr::KSubset { base, k } => {
            expr_references_state_vars(&base.node, state_vars)
                || expr_references_state_vars(&k.node, state_vars)
        }
        TirExpr::BoolNot(inner)
        | TirExpr::ArithNeg(inner)
        | TirExpr::Prime(inner)
        | TirExpr::Unchanged(inner)
        | TirExpr::Powerset(inner)
        | TirExpr::BigUnion(inner)
        | TirExpr::Domain(inner)
        | TirExpr::Always(inner)
        | TirExpr::Eventually(inner)
        | TirExpr::Enabled(inner) => expr_references_state_vars(&inner.node, state_vars),
        TirExpr::Range { lo, hi } => {
            expr_references_state_vars(&lo.node, state_vars)
                || expr_references_state_vars(&hi.node, state_vars)
        }
        TirExpr::In { elem, set } => {
            expr_references_state_vars(&elem.node, state_vars)
                || expr_references_state_vars(&set.node, state_vars)
        }
        TirExpr::If { cond, then_, else_ } => {
            expr_references_state_vars(&cond.node, state_vars)
                || expr_references_state_vars(&then_.node, state_vars)
                || expr_references_state_vars(&else_.node, state_vars)
        }
        TirExpr::SetEnum(elems) | TirExpr::Tuple(elems) | TirExpr::Times(elems) => elems
            .iter()
            .any(|e| expr_references_state_vars(&e.node, state_vars)),
        TirExpr::Forall { vars, body }
        | TirExpr::Exists { vars, body }
        | TirExpr::SetBuilder { vars, body, .. } => {
            vars.iter().any(|v| {
                v.domain
                    .as_ref()
                    .map_or(false, |d| expr_references_state_vars(&d.node, state_vars))
            }) || expr_references_state_vars(&body.node, state_vars)
        }
        TirExpr::Choose { var, body } => {
            var.domain
                .as_ref()
                .map_or(false, |d| expr_references_state_vars(&d.node, state_vars))
                || expr_references_state_vars(&body.node, state_vars)
        }
        TirExpr::SetFilter { var, body } => {
            var.domain
                .as_ref()
                .map_or(false, |d| expr_references_state_vars(&d.node, state_vars))
                || expr_references_state_vars(&body.node, state_vars)
        }
        TirExpr::FuncDef { vars, body } => {
            vars.iter().any(|v| {
                v.domain
                    .as_ref()
                    .map_or(false, |d| expr_references_state_vars(&d.node, state_vars))
            }) || expr_references_state_vars(&body.node, state_vars)
        }
        TirExpr::FuncApply { func, arg } => {
            expr_references_state_vars(&func.node, state_vars)
                || expr_references_state_vars(&arg.node, state_vars)
        }
        TirExpr::FuncSet { domain, range } => {
            expr_references_state_vars(&domain.node, state_vars)
                || expr_references_state_vars(&range.node, state_vars)
        }
        TirExpr::Record(fields) => fields
            .iter()
            .any(|(_, v)| expr_references_state_vars(&v.node, state_vars)),
        TirExpr::RecordAccess { record, .. } => {
            expr_references_state_vars(&record.node, state_vars)
        }
        TirExpr::RecordSet(fields) => fields
            .iter()
            .any(|(_, v)| expr_references_state_vars(&v.node, state_vars)),
        TirExpr::Except { base, specs } => {
            expr_references_state_vars(&base.node, state_vars)
                || specs.iter().any(|s| {
                    expr_references_state_vars(&s.value.node, state_vars)
                        || s.path.iter().any(|p| match p {
                            TirExceptPathElement::Index(idx) => {
                                expr_references_state_vars(&idx.node, state_vars)
                            }
                            TirExceptPathElement::Field(_) => false,
                        })
                })
        }
        TirExpr::Let { defs, body } => {
            defs.iter()
                .any(|d| expr_references_state_vars(&d.body.node, state_vars))
                || expr_references_state_vars(&body.node, state_vars)
        }
        TirExpr::Case { arms, other } => {
            arms.iter().any(|a| {
                expr_references_state_vars(&a.guard.node, state_vars)
                    || expr_references_state_vars(&a.body.node, state_vars)
            }) || other
                .as_ref()
                .map_or(false, |o| expr_references_state_vars(&o.node, state_vars))
        }
        TirExpr::Label { body, .. } => expr_references_state_vars(&body.node, state_vars),
        TirExpr::Lambda { body, .. } => expr_references_state_vars(&body.node, state_vars),
        TirExpr::Apply { op, args } => {
            expr_references_state_vars(&op.node, state_vars)
                || args
                    .iter()
                    .any(|a| expr_references_state_vars(&a.node, state_vars))
        }
        _ => false,
    }
}

/// Check if a TIR expression contains primed variable references.
fn expr_contains_prime(expr: &TirExpr) -> bool {
    stack_safe(|| expr_contains_prime_inner(expr))
}

/// Public wrapper for `expr_contains_prime` (used by CLI for Spec operator analysis).
pub fn expr_contains_prime_pub(expr: &TirExpr) -> bool {
    expr_contains_prime(expr)
}

fn expr_contains_prime_inner(expr: &TirExpr) -> bool {
    match expr {
        TirExpr::Prime(_) | TirExpr::Unchanged(_) => true,
        TirExpr::BoolBinOp { left, right, .. }
        | TirExpr::Cmp { left, right, .. }
        | TirExpr::ArithBinOp { left, right, .. }
        | TirExpr::SetBinOp { left, right, .. }
        | TirExpr::Subseteq { left, right, .. } => {
            expr_contains_prime(&left.node) || expr_contains_prime(&right.node)
        }
        TirExpr::BoolNot(inner)
        | TirExpr::ArithNeg(inner)
        | TirExpr::Powerset(inner)
        | TirExpr::BigUnion(inner)
        | TirExpr::Domain(inner) => expr_contains_prime(&inner.node),
        TirExpr::KSubset { base, k } => {
            expr_contains_prime(&base.node) || expr_contains_prime(&k.node)
        }
        TirExpr::Range { lo, hi } => expr_contains_prime(&lo.node) || expr_contains_prime(&hi.node),
        TirExpr::In { elem, set } => {
            expr_contains_prime(&elem.node) || expr_contains_prime(&set.node)
        }
        TirExpr::If { cond, then_, else_ } => {
            expr_contains_prime(&cond.node)
                || expr_contains_prime(&then_.node)
                || expr_contains_prime(&else_.node)
        }
        TirExpr::SetEnum(elems) | TirExpr::Tuple(elems) | TirExpr::Times(elems) => {
            elems.iter().any(|e| expr_contains_prime(&e.node))
        }
        TirExpr::Forall { body, .. }
        | TirExpr::Exists { body, .. }
        | TirExpr::SetBuilder { body, .. }
        | TirExpr::Choose { body, .. }
        | TirExpr::SetFilter { body, .. }
        | TirExpr::FuncDef { body, .. } => expr_contains_prime(&body.node),
        TirExpr::FuncApply { func, arg } => {
            expr_contains_prime(&func.node) || expr_contains_prime(&arg.node)
        }
        TirExpr::FuncSet { domain, range } => {
            expr_contains_prime(&domain.node) || expr_contains_prime(&range.node)
        }
        TirExpr::Record(fields) => fields.iter().any(|(_, v)| expr_contains_prime(&v.node)),
        TirExpr::RecordAccess { record, .. } => expr_contains_prime(&record.node),
        TirExpr::Except { base, specs } => {
            expr_contains_prime(&base.node)
                || specs.iter().any(|s| expr_contains_prime(&s.value.node))
        }
        TirExpr::Let { defs, body } => {
            defs.iter().any(|d| expr_contains_prime(&d.body.node))
                || expr_contains_prime(&body.node)
        }
        TirExpr::Label { body, .. } => expr_contains_prime(&body.node),
        TirExpr::Apply { op, args } => {
            expr_contains_prime(&op.node) || args.iter().any(|a| expr_contains_prime(&a.node))
        }
        _ => false,
    }
}

/// Check if a TIR expression contains temporal operators (Always, Eventually,
/// LeadsTo, WeakFair, StrongFair, ActionSubscript, Enabled).
///
/// Operators containing temporal constructs cannot be compiled as regular
/// Rust helpers — they are liveness/fairness properties, not state predicates.
fn expr_contains_temporal(expr: &TirExpr) -> bool {
    stack_safe(|| expr_contains_temporal_inner(expr))
}

fn expr_contains_temporal_inner(expr: &TirExpr) -> bool {
    match expr {
        TirExpr::Always(_)
        | TirExpr::Eventually(_)
        | TirExpr::LeadsTo { .. }
        | TirExpr::WeakFair { .. }
        | TirExpr::StrongFair { .. }
        | TirExpr::Enabled(_)
        | TirExpr::ActionSubscript { .. } => true,
        TirExpr::BoolBinOp { left, right, .. }
        | TirExpr::Cmp { left, right, .. }
        | TirExpr::ArithBinOp { left, right, .. }
        | TirExpr::SetBinOp { left, right, .. }
        | TirExpr::Subseteq { left, right, .. } => {
            expr_contains_temporal(&left.node) || expr_contains_temporal(&right.node)
        }
        TirExpr::BoolNot(inner)
        | TirExpr::ArithNeg(inner)
        | TirExpr::Powerset(inner)
        | TirExpr::BigUnion(inner)
        | TirExpr::Domain(inner) => expr_contains_temporal(&inner.node),
        TirExpr::KSubset { base, k } => {
            expr_contains_temporal(&base.node) || expr_contains_temporal(&k.node)
        }
        TirExpr::Range { lo, hi } => {
            expr_contains_temporal(&lo.node) || expr_contains_temporal(&hi.node)
        }
        TirExpr::In { elem, set } => {
            expr_contains_temporal(&elem.node) || expr_contains_temporal(&set.node)
        }
        TirExpr::If { cond, then_, else_ } => {
            expr_contains_temporal(&cond.node)
                || expr_contains_temporal(&then_.node)
                || expr_contains_temporal(&else_.node)
        }
        TirExpr::SetEnum(elems) | TirExpr::Tuple(elems) | TirExpr::Times(elems) => {
            elems.iter().any(|e| expr_contains_temporal(&e.node))
        }
        TirExpr::Forall { body, .. }
        | TirExpr::Exists { body, .. }
        | TirExpr::SetBuilder { body, .. }
        | TirExpr::Choose { body, .. }
        | TirExpr::SetFilter { body, .. }
        | TirExpr::FuncDef { body, .. } => expr_contains_temporal(&body.node),
        TirExpr::FuncApply { func, arg } => {
            expr_contains_temporal(&func.node) || expr_contains_temporal(&arg.node)
        }
        TirExpr::FuncSet { domain, range } => {
            expr_contains_temporal(&domain.node) || expr_contains_temporal(&range.node)
        }
        TirExpr::Record(fields) => fields.iter().any(|(_, v)| expr_contains_temporal(&v.node)),
        TirExpr::RecordAccess { record, .. } => expr_contains_temporal(&record.node),
        TirExpr::Except { base, specs } => {
            expr_contains_temporal(&base.node)
                || specs.iter().any(|s| expr_contains_temporal(&s.value.node))
        }
        TirExpr::Let { defs, body } => {
            defs.iter().any(|d| expr_contains_temporal(&d.body.node))
                || expr_contains_temporal(&body.node)
        }
        TirExpr::Label { body, .. } => expr_contains_temporal(&body.node),
        TirExpr::Apply { op, args } => {
            expr_contains_temporal(&op.node)
                || args.iter().any(|a| expr_contains_temporal(&a.node))
        }
        _ => false,
    }
}

/// Infer the type of an operator parameter from how it's used in the body.
///
/// Returns a Rust type string, or `"_"` if the type can't be determined and
/// a generic parameter should be used.
fn infer_param_type(body: &TirExpr, param_name: &str) -> &'static str {
    // Check if the param is used in arithmetic operations
    if param_used_in_arithmetic(body, param_name) {
        return "i64";
    }
    // Default: use a generic type parameter
    "_"
}

/// Check if a parameter is used in arithmetic context (compared to int, used with +/-/*).
fn param_used_in_arithmetic(expr: &TirExpr, param_name: &str) -> bool {
    stack_safe(|| param_used_in_arithmetic_inner(expr, param_name))
}

fn param_used_in_arithmetic_inner(expr: &TirExpr, param_name: &str) -> bool {
    let is_param = |e: &TirExpr| matches!(e, TirExpr::Name(n) if n.name == param_name);
    let is_int_ctx = |e: &TirExpr| {
        matches!(
            e,
            TirExpr::Const {
                value: Value::SmallInt(_) | Value::Int(_),
                ..
            } | TirExpr::ArithBinOp { .. }
                | TirExpr::ArithNeg(_)
        )
    };

    match expr {
        TirExpr::ArithBinOp { left, right, .. } => {
            if is_param(&left.node) || is_param(&right.node) {
                return true;
            }
            param_used_in_arithmetic(&left.node, param_name)
                || param_used_in_arithmetic(&right.node, param_name)
        }
        TirExpr::ArithNeg(inner) => {
            if is_param(&inner.node) {
                return true;
            }
            param_used_in_arithmetic(&inner.node, param_name)
        }
        TirExpr::Cmp { left, right, .. } => {
            if (is_param(&left.node) && is_int_ctx(&right.node))
                || (is_param(&right.node) && is_int_ctx(&left.node))
            {
                return true;
            }
            param_used_in_arithmetic(&left.node, param_name)
                || param_used_in_arithmetic(&right.node, param_name)
        }
        TirExpr::BoolBinOp { left, right, .. } => {
            param_used_in_arithmetic(&left.node, param_name)
                || param_used_in_arithmetic(&right.node, param_name)
        }
        TirExpr::If { cond, then_, else_ } => {
            param_used_in_arithmetic(&cond.node, param_name)
                || param_used_in_arithmetic(&then_.node, param_name)
                || param_used_in_arithmetic(&else_.node, param_name)
        }
        TirExpr::Let { defs, body } => {
            defs.iter()
                .any(|d| param_used_in_arithmetic(&d.body.node, param_name))
                || param_used_in_arithmetic(&body.node, param_name)
        }
        TirExpr::Label { body, .. } => param_used_in_arithmetic(&body.node, param_name),
        TirExpr::BoolNot(inner) => param_used_in_arithmetic(&inner.node, param_name),
        TirExpr::Apply { args, .. } => args
            .iter()
            .any(|a| param_used_in_arithmetic(&a.node, param_name)),
        TirExpr::FuncApply { func, arg } => {
            param_used_in_arithmetic(&func.node, param_name)
                || param_used_in_arithmetic(&arg.node, param_name)
        }
        TirExpr::Forall { body, .. } | TirExpr::Exists { body, .. } => {
            param_used_in_arithmetic(&body.node, param_name)
        }
        _ => false,
    }
}

/// Infer a simple return type hint from a TIR expression.
///
/// Accepts an optional operators map to resolve Apply targets to their body's
/// return type, breaking through the `TirType::Dyn` barrier.
///
/// Uses a depth limit to prevent stack overflow on mutually-recursive operators.
fn infer_return_type_hint(
    expr: &TirExpr,
    operators: Option<&HashMap<String, &TirOperator>>,
) -> String {
    infer_return_type_hint_depth(expr, operators, 0, None)
}

fn infer_return_type_hint_with_vars(
    expr: &TirExpr,
    operators: Option<&HashMap<String, &TirOperator>>,
    var_types: &HashMap<String, TlaType>,
) -> String {
    infer_return_type_hint_depth(expr, operators, 0, Some(var_types))
}

/// Maximum recursion depth for type inference through operator definitions.
/// Prevents stack overflow on recursive/mutually-recursive operators.
const MAX_TYPE_INFER_DEPTH: usize = 16;

fn infer_return_type_hint_depth(
    expr: &TirExpr,
    operators: Option<&HashMap<String, &TirOperator>>,
    depth: usize,
    var_types: Option<&HashMap<String, TlaType>>,
) -> String {
    if depth > MAX_TYPE_INFER_DEPTH {
        return "Value".to_string();
    }
    match expr {
        TirExpr::Const { value, .. } => match value {
            Value::Bool(_) => "bool".to_string(),
            Value::SmallInt(_) | Value::Int(_) => "i64".to_string(),
            Value::String(_) => "String".to_string(),
            Value::Set(s) => {
                // Infer element type from set elements
                if let Some(first) = s.iter().next() {
                    let elem_ty = match first {
                        Value::Bool(_) => "bool",
                        Value::SmallInt(_) | Value::Int(_) => "i64",
                        Value::String(_) | Value::ModelValue(_) => "String",
                        _ => "Value",
                    };
                    format!("TlaSet<{elem_ty}>")
                } else {
                    "TlaSet<Value>".to_string()
                }
            }
            Value::Seq(elems) => {
                if let Some(first) = elems.first() {
                    let elem_ty = match first {
                        Value::Bool(_) => "bool",
                        Value::SmallInt(_) | Value::Int(_) => "i64",
                        Value::String(_) => "String",
                        _ => "Value",
                    };
                    format!("Vec<{elem_ty}>")
                } else {
                    "Vec<Value>".to_string()
                }
            }
            Value::Tuple(elems) => {
                let types: Vec<&str> = elems
                    .iter()
                    .map(|v| match v {
                        Value::Bool(_) => "bool",
                        Value::SmallInt(_) | Value::Int(_) => "i64",
                        Value::String(_) => "String",
                        _ => "Value",
                    })
                    .collect();
                format!("({})", types.join(", "))
            }
            Value::ModelValue(_) => "String".to_string(),
            _ => "Value".to_string(),
        },
        TirExpr::BoolBinOp { .. }
        | TirExpr::BoolNot(_)
        | TirExpr::Cmp { .. }
        | TirExpr::In { .. }
        | TirExpr::Subseteq { .. }
        | TirExpr::Forall { .. }
        | TirExpr::Exists { .. } => "bool".to_string(),
        TirExpr::ArithBinOp { .. } | TirExpr::ArithNeg(_) => "i64".to_string(),
        TirExpr::Range { .. } => "TlaSet<i64>".to_string(),
        TirExpr::SetEnum(elems) => {
            // Infer element type from elements
            if let Some(first) = elems.first() {
                let elem_ty = infer_return_type_hint_depth(&first.node, operators, depth + 1, var_types);
                format!("TlaSet<{elem_ty}>")
            } else {
                "TlaSet<Value>".to_string()
            }
        }
        TirExpr::SetFilter { var, .. } => {
            // Filter preserves the element type of the domain
            if let Some(domain) = &var.domain {
                let dom_ty = infer_return_type_hint_depth(&domain.node, operators, depth + 1, var_types);
                if dom_ty != "Value" {
                    return dom_ty;
                }
            }
            "TlaSet<Value>".to_string()
        }
        TirExpr::SetBuilder { body, .. } => {
            let body_ty = infer_return_type_hint_depth(&body.node, operators, depth + 1, var_types);
            format!("TlaSet<{body_ty}>")
        }
        TirExpr::SetBinOp { left, .. } => {
            // Union/intersect/difference preserves type
            infer_return_type_hint_depth(&left.node, operators, depth + 1, var_types)
        }
        TirExpr::Powerset(inner) => {
            let inner_ty = infer_return_type_hint_depth(&inner.node, operators, depth + 1, var_types);
            format!("TlaSet<{inner_ty}>")
        }
        TirExpr::BigUnion(_) => "TlaSet<Value>".to_string(),
        TirExpr::Tuple(elems) => {
            let types: Vec<String> = elems
                .iter()
                .map(|e| infer_return_type_hint_depth(&e.node, operators, depth + 1, var_types))
                .collect();
            format!("({})", types.join(", "))
        }
        TirExpr::Times(_) => {
            // Times produces set of tuples, complex to infer
            "Value".to_string()
        }
        TirExpr::Record(_) => "TlaRecord<Value>".to_string(),
        TirExpr::RecordAccess { .. } => "Value".to_string(),
        TirExpr::RecordSet(fields) => {
            // RecordSet: [field: SetOfValues, ...] -> TlaSet<Value>
            // Records are wrapped as Value in the generated set.
            let _ = fields;
            "TlaSet<Value>".to_string()
        }
        TirExpr::FuncDef { vars, body } => {
            // Infer key and value types
            let key_ty = if vars.len() == 1 {
                if let Some(domain) = &vars[0].domain {
                    let elem_ty = infer_element_type_from_tir_set(&domain.node);
                    elem_ty.to_rust_type()
                } else {
                    "Value".to_string()
                }
            } else {
                "Value".to_string()
            };
            let val_ty = infer_return_type_hint_depth(&body.node, operators, depth + 1, var_types);
            format!("TlaFunc<{key_ty}, {val_ty}>")
        }
        TirExpr::FuncSet { .. } => "TlaSet<Value>".to_string(),
        TirExpr::Domain(_inner) => {
            // Domain of a function — we'd need to know the function type
            "TlaSet<Value>".to_string()
        }
        TirExpr::If { then_, else_, .. } => {
            let then_ty = infer_return_type_hint_depth(&then_.node, operators, depth + 1, var_types);
            if then_ty != "Value" {
                then_ty
            } else {
                infer_return_type_hint_depth(&else_.node, operators, depth + 1, var_types)
            }
        }
        TirExpr::Case { arms, other } => {
            // Try first arm, then other
            if let Some(arm) = arms.first() {
                let arm_ty = infer_return_type_hint_depth(&arm.body.node, operators, depth + 1, var_types);
                if arm_ty != "Value" {
                    return arm_ty;
                }
            }
            if let Some(other) = other {
                return infer_return_type_hint_depth(&other.node, operators, depth + 1, var_types);
            }
            "Value".to_string()
        }
        TirExpr::Let { body, .. } => {
            infer_return_type_hint_depth(&body.node, operators, depth + 1, var_types)
        }
        TirExpr::Label { body, .. } => {
            infer_return_type_hint_depth(&body.node, operators, depth + 1, var_types)
        }
        TirExpr::Except { base, .. } => {
            // EXCEPT preserves the type of the base
            infer_return_type_hint_depth(&base.node, operators, depth + 1, var_types)
        }
        TirExpr::Apply { op, args } => {
            // Try to resolve the Apply target to a known operator body
            if let TirExpr::Name(name_ref) = &op.node {
                // Known stdlib operators
                match name_ref.name.as_str() {
                    "Len" | "Cardinality" => return "i64".to_string(),
                    "Head" => {
                        // Head of a sequence: return element type
                        if let Some(arg) = args.first() {
                            let seq_ty = infer_return_type_hint_depth(
                                &arg.node,
                                operators,
                                depth + 1,
                                var_types,
                            );
                            if let Some(inner) = seq_ty.strip_prefix("Vec<").and_then(|s| s.strip_suffix('>')) {
                                return inner.to_string();
                            }
                        }
                        return "Value".to_string();
                    }
                    "Tail" | "Append" | "SubSeq" | "SelectSeq" => {
                        // These preserve the sequence type
                        if let Some(arg) = args.first() {
                            return infer_return_type_hint_depth(
                                &arg.node,
                                operators,
                                depth + 1,
                                var_types,
                            );
                        }
                        return "Vec<Value>".to_string();
                    }
                    _ => {}
                }
                // Try to resolve to a known operator
                if let Some(ops) = operators {
                    if let Some(target_op) = ops.get(&name_ref.name) {
                        return infer_return_type_hint_depth(
                            &target_op.body.node,
                            Some(ops),
                            depth + 1,
                            var_types,
                        );
                    }
                }
            }
            "Value".to_string()
        }
        TirExpr::FuncApply { func, arg: _ } => {
            // If we can determine the function type, return the value type
            let func_ty = infer_return_type_hint_depth(&func.node, operators, depth + 1, var_types);
            // Check if it's a TlaFunc<K, V> — extract V
            if let Some(rest) = func_ty.strip_prefix("TlaFunc<") {
                if let Some(comma_pos) = rest.find(", ") {
                    let val_part = &rest[comma_pos + 2..];
                    if let Some(val_ty) = val_part.strip_suffix('>') {
                        return val_ty.to_string();
                    }
                }
            }
            // Check if it's a Vec<T> (sequence indexing) — extract T
            if let Some(inner) = func_ty.strip_prefix("Vec<").and_then(|s| s.strip_suffix('>')) {
                return inner.to_string();
            }
            "Value".to_string()
        }
        TirExpr::Choose { var, body } => {
            // CHOOSE x \in S : P(x) returns the element type of S
            if let Some(domain) = &var.domain {
                let elem_ty = infer_element_type_from_tir_set(&domain.node);
                match elem_ty {
                    TlaType::Int => return "i64".to_string(),
                    TlaType::Bool => return "bool".to_string(),
                    TlaType::String => return "String".to_string(),
                    _ => {}
                }
                // Domain is a param or unknown set. Check how the bound var is used
                // in the body/predicate to determine element type.
                if param_used_in_arithmetic(&body.node, &var.name) {
                    return "i64".to_string();
                }
                // Also check transitively through operator calls in body
                if let Some(ops) = operators {
                    if param_arithmetic_via_apply_depth(&body.node, &var.name, ops, 0) {
                        return "i64".to_string();
                    }
                }
            }
            "Value".to_string()
        }
        TirExpr::Name(name_ref) => {
            // Built-in constants
            match name_ref.name.as_str() {
                "TRUE" | "FALSE" => "bool".to_string(),
                "BOOLEAN" => "TlaSet<bool>".to_string(),
                _ => {
                    // Check if this is a state variable with a known type
                    if let Some(vt) = var_types {
                        if let Some(ty) = vt.get(&name_ref.name) {
                            if !matches!(ty, TlaType::Unknown) {
                                return ty.to_rust_type();
                            }
                        }
                    }
                    // Try to resolve the name to an operator body
                    if let Some(ops) = operators {
                        if let Some(target_op) = ops.get(&name_ref.name) {
                            return infer_return_type_hint_depth(
                                &target_op.body.node,
                                Some(ops),
                                depth + 1,
                                var_types,
                            );
                        }
                    }
                    "Value".to_string()
                }
            }
        }
        TirExpr::OperatorRef(op_ref) => {
            // Try to resolve the operator
            if let Some(ops) = operators {
                if let Some(target_op) = ops.get(&op_ref.operator) {
                    return infer_return_type_hint_depth(
                        &target_op.body.node,
                        Some(ops),
                        depth + 1,
                        var_types,
                    );
                }
            }
            "Value".to_string()
        }
        _ => "Value".to_string(),
    }
}

/// Infer Rust types for state variables from TIR type information.
fn infer_var_types_from_tir(
    operators: &HashMap<String, &TirOperator>,
    state_vars: &[String],
    _constants: &HashMap<String, String>,
    constant_types: &HashMap<String, TlaType>,
    init_name: &str,
) -> HashMap<String, TlaType> {
    let mut types = HashMap::new();
    let state_var_set: HashSet<String> = state_vars.iter().cloned().collect();

    // Try to infer from Init operator
    if let Some(init) = operators.get(init_name) {
        let mut assignments: HashMap<String, InitAssignment> = HashMap::new();
        analyze_init_conjuncts(&init.body.node, &mut assignments, &state_var_set);

        for var in state_vars {
            if let Some(assignment) = assignments.get(var) {
                let ty = match assignment {
                    InitAssignment::Eq(expr) => infer_type_from_tir_expr(expr),
                    InitAssignment::InSet(set_expr) => infer_element_type_from_tir_set(set_expr),
                };
                types.insert(var.clone(), ty);
            }
        }

        // Second pass: resolve Unknown types by looking at assignments that
        // reference other state variables whose types are now known.
        // e.g., s_ack = s_bit → if s_bit was inferred as Int, s_ack is Int too.
        for var in state_vars {
            if matches!(types.get(var), Some(TlaType::Unknown) | None) {
                if let Some(InitAssignment::Eq(expr)) = assignments.get(var) {
                    if let TirExpr::Name(name_ref) = expr {
                        if let Some(other_ty) = types.get(&name_ref.name) {
                            if !matches!(other_ty, TlaType::Unknown) {
                                types.insert(var.clone(), other_ty.clone());
                            }
                        }
                    }
                }
            }
        }
    }

    // Refine unknown sequence element types by scanning Append calls.
    // Try all operators and keep the most specific result (fewest Unknown fields).
    for var in state_vars {
        if let Some(TlaType::Seq(elem)) = types.get(var) {
            if matches!(**elem, TlaType::Unknown) {
                let mut best: Option<TlaType> = None;
                for op in operators.values() {
                    if let Some(elem_ty) =
                        find_append_elem_type(var, &op.body.node, operators, constant_types)
                    {
                        let unknown_count = count_unknowns(&elem_ty);
                        let is_better = match &best {
                            None => true,
                            Some(prev) => unknown_count < count_unknowns(prev),
                        };
                        if is_better {
                            best = Some(elem_ty);
                        }
                    }
                }
                if let Some(elem_ty) = best {
                    types.insert(var.clone(), TlaType::Seq(Box::new(elem_ty)));
                }
            }
        }
    }

    types
}

/// Count how many Unknown type nodes exist in a TlaType tree.
fn count_unknowns(ty: &TlaType) -> usize {
    match ty {
        TlaType::Unknown => 1,
        TlaType::Set(inner) | TlaType::Seq(inner) => count_unknowns(inner),
        TlaType::Tuple(elems) => elems.iter().map(count_unknowns).sum(),
        TlaType::Func(k, v) => count_unknowns(k) + count_unknowns(v),
        TlaType::Record(fields) => fields.iter().map(|(_, t)| count_unknowns(t)).sum(),
        _ => 0,
    }
}

/// Scan for `Append(seq, elem)` calls to determine sequence element type.
fn find_append_elem_type(
    var_name: &str,
    expr: &TirExpr,
    operators: &HashMap<String, &TirOperator>,
    constant_types: &HashMap<String, TlaType>,
) -> Option<TlaType> {
    find_append_elem_type_ctx(var_name, expr, &HashMap::new(), operators, constant_types)
}

fn find_append_elem_type_ctx(
    var_name: &str,
    expr: &TirExpr,
    let_ctx: &HashMap<String, TirExpr>,
    operators: &HashMap<String, &TirOperator>,
    ct: &HashMap<String, TlaType>,
) -> Option<TlaType> {
    match expr {
        TirExpr::Apply { op, args } => {
            if let TirExpr::Name(name_ref) = &op.node {
                if name_ref.name == "Append" && args.len() == 2 {
                    let first_is_var = match &args[0].node {
                        TirExpr::Prime(inner) => {
                            matches!(&inner.node, TirExpr::Name(n) if n.name == var_name)
                        }
                        TirExpr::Name(n) => n.name == var_name,
                        _ => false,
                    };
                    if first_is_var {
                        if let TirExpr::Tuple(elems) = &args[1].node {
                            if !elems.is_empty() {
                                let elem_types: Vec<_> = elems
                                    .iter()
                                    .map(|e| resolve_elem_type(e, let_ctx, operators, ct))
                                    .collect();
                                let has_real =
                                    elem_types.iter().any(|t| !matches!(t, TlaType::Unknown));
                                if has_real {
                                    let all_same = elem_types.iter().all(|t| t == &elem_types[0]);
                                    return if all_same {
                                        Some(elem_types[0].clone())
                                    } else {
                                        Some(TlaType::Tuple(elem_types))
                                    };
                                }
                            }
                        }
                        return Some(infer_type_from_tir_expr(&args[1].node));
                    }
                }
            }
            for a in args {
                if let Some(t) =
                    find_append_elem_type_ctx(var_name, &a.node, let_ctx, operators, ct)
                {
                    return Some(t);
                }
            }
            None
        }
        TirExpr::BoolBinOp { left, right, .. }
        | TirExpr::Cmp { left, right, .. }
        | TirExpr::ArithBinOp { left, right, .. } => {
            find_append_elem_type_ctx(var_name, &left.node, let_ctx, operators, ct).or_else(|| {
                find_append_elem_type_ctx(var_name, &right.node, let_ctx, operators, ct)
            })
        }
        TirExpr::If { cond, then_, else_ } => {
            find_append_elem_type_ctx(var_name, &cond.node, let_ctx, operators, ct)
                .or_else(|| {
                    find_append_elem_type_ctx(var_name, &then_.node, let_ctx, operators, ct)
                })
                .or_else(|| {
                    find_append_elem_type_ctx(var_name, &else_.node, let_ctx, operators, ct)
                })
        }
        TirExpr::Let { defs, body } => {
            let mut ext = let_ctx.clone();
            for d in defs {
                ext.insert(d.name.clone(), d.body.node.clone());
                if let Some(t) =
                    find_append_elem_type_ctx(var_name, &d.body.node, &ext, operators, ct)
                {
                    return Some(t);
                }
            }
            find_append_elem_type_ctx(var_name, &body.node, &ext, operators, ct)
        }
        TirExpr::Exists { vars, body } | TirExpr::Forall { vars, body } => {
            let mut ext = let_ctx.clone();
            for v in vars {
                if let Some(domain) = &v.domain {
                    ext.insert(v.name.clone(), domain.node.clone());
                }
            }
            find_append_elem_type_ctx(var_name, &body.node, &ext, operators, ct)
        }
        TirExpr::Label { body, .. } => {
            find_append_elem_type_ctx(var_name, &body.node, let_ctx, operators, ct)
        }
        TirExpr::BoolNot(inner) | TirExpr::Prime(inner) => {
            find_append_elem_type_ctx(var_name, &inner.node, let_ctx, operators, ct)
        }
        _ => None,
    }
}

/// Resolve element type through Let/Exists context, constant types, and operator return types.
fn resolve_elem_type(
    elem: &tla_core::Spanned<TirExpr>,
    let_ctx: &HashMap<String, TirExpr>,
    operators: &HashMap<String, &TirOperator>,
    ct: &HashMap<String, TlaType>,
) -> TlaType {
    if let TirExpr::Name(n) = &elem.node {
        if let Some(bound_expr) = let_ctx.get(&n.name) {
            // For Exists-bound variables, let_ctx stores the domain expression.
            // Use infer_element_type_from_tir_set which understands Range -> Int.
            let set_elem_ty = infer_element_type_from_tir_set(bound_expr);
            if !matches!(set_elem_ty, TlaType::Unknown) {
                return set_elem_ty;
            }
            let resolved = infer_type_from_tir_expr(bound_expr);
            if !matches!(resolved, TlaType::Unknown) {
                if let TlaType::Set(inner) = &resolved {
                    return (**inner).clone();
                }
                return resolved;
            }
            if let TirExpr::Apply { op, .. } = bound_expr {
                if let TirExpr::Name(op_name) = &op.node {
                    if let Some(target) = operators.get(&op_name.name) {
                        if let Some(ty) = return_hint_to_tla_type(&infer_return_type_hint(
                            &target.body.node,
                            Some(operators),
                        )) {
                            return ty;
                        }
                    }
                }
            }
            if let TirExpr::Name(domain_name) = bound_expr {
                if let Some(cty) = ct.get(&domain_name.name) {
                    if let TlaType::Set(inner) = cty {
                        return (**inner).clone();
                    }
                }
            }
        }
        let name_ty = tir_type_to_tla_type(&n.ty);
        if !matches!(name_ty, TlaType::Unknown) {
            return name_ty;
        }
    }
    if let TirExpr::Apply { op, .. } = &elem.node {
        if let TirExpr::Name(op_name) = &op.node {
            if let Some(target) = operators.get(&op_name.name) {
                if let Some(ty) = return_hint_to_tla_type(&infer_return_type_hint(
                    &target.body.node,
                    Some(operators),
                )) {
                    return ty;
                }
            }
        }
    }
    infer_type_from_tir_expr(&elem.node)
}

fn return_hint_to_tla_type(hint: &str) -> Option<TlaType> {
    match hint {
        "bool" => Some(TlaType::Bool),
        "i64" => Some(TlaType::Int),
        "String" => Some(TlaType::String),
        _ => None,
    }
}

/// Infer param type with transitive resolution through operator calls.
fn infer_param_type_with_ops(
    body: &TirExpr,
    param_name: &str,
    operators: &HashMap<String, &TirOperator>,
) -> String {
    let direct = infer_param_type(body, param_name);
    if direct != "_" {
        return direct.to_string();
    }
    if param_arithmetic_via_apply(body, param_name, operators) {
        return "i64".to_string();
    }
    // Check if param is used as a set domain (in Forall/Exists/SetFilter/Choose).
    // If so, determine element type and return TlaSet<elem>.
    if let Some(elem_ty) = param_used_as_set_domain(body, param_name, operators) {
        let elem_str = elem_ty.to_rust_type();
        return format!("TlaSet<{elem_str}>");
    }
    "_".to_string()
}

/// Infer parameter type from FuncApply patterns.
/// When a param is used as `state_var[param]` (FuncApply with state var as func
/// and param as arg), infer the param type from the function's key type.
fn infer_param_from_func_apply(
    expr: &TirExpr,
    param_name: &str,
    state_vars: &HashSet<String>,
    var_types: &HashMap<String, TlaType>,
) -> Option<TlaType> {
    stack_safe(|| infer_param_from_func_apply_inner(expr, param_name, state_vars, var_types))
}

fn infer_param_from_func_apply_inner(
    expr: &TirExpr,
    param_name: &str,
    state_vars: &HashSet<String>,
    var_types: &HashMap<String, TlaType>,
) -> Option<TlaType> {
    match expr {
        TirExpr::FuncApply { func, arg } => {
            // Check if the arg is this param
            let arg_is_param = matches!(&arg.node, TirExpr::Name(n) if n.name == param_name);
            if arg_is_param {
                // Check if the func is a state var with known type
                if let TirExpr::Name(name_ref) = &func.node {
                    if state_vars.contains(&name_ref.name) {
                        if let Some(TlaType::Func(key_ty, _)) = var_types.get(&name_ref.name) {
                            if !matches!(**key_ty, TlaType::Unknown) {
                                return Some(*key_ty.clone());
                            }
                        }
                    }
                }
            }
            // Recurse into func and arg
            infer_param_from_func_apply(&func.node, param_name, state_vars, var_types)
                .or_else(|| infer_param_from_func_apply(&arg.node, param_name, state_vars, var_types))
        }
        // Recurse into all sub-expressions
        TirExpr::BoolBinOp { left, right, .. }
        | TirExpr::Cmp { left, right, .. }
        | TirExpr::ArithBinOp { left, right, .. }
        | TirExpr::In { elem: left, set: right }
        | TirExpr::Subseteq { left, right } => {
            infer_param_from_func_apply(&left.node, param_name, state_vars, var_types)
                .or_else(|| infer_param_from_func_apply(&right.node, param_name, state_vars, var_types))
        }
        TirExpr::BoolNot(inner) | TirExpr::ArithNeg(inner) => {
            infer_param_from_func_apply(&inner.node, param_name, state_vars, var_types)
        }
        TirExpr::If { cond, then_, else_ } => {
            infer_param_from_func_apply(&cond.node, param_name, state_vars, var_types)
                .or_else(|| infer_param_from_func_apply(&then_.node, param_name, state_vars, var_types))
                .or_else(|| infer_param_from_func_apply(&else_.node, param_name, state_vars, var_types))
        }
        TirExpr::Forall { vars: _, body } | TirExpr::Exists { vars: _, body } => {
            infer_param_from_func_apply(&body.node, param_name, state_vars, var_types)
        }
        TirExpr::Let { defs, body } => {
            for def in defs {
                if let Some(ty) = infer_param_from_func_apply(&def.body.node, param_name, state_vars, var_types) {
                    return Some(ty);
                }
            }
            infer_param_from_func_apply(&body.node, param_name, state_vars, var_types)
        }
        _ => None,
    }
}

/// Check if param is used as a set domain in quantifiers, set filters, or CHOOSE.
/// Returns the element type of the iteration if found.
fn param_used_as_set_domain(
    expr: &TirExpr,
    param_name: &str,
    operators: &HashMap<String, &TirOperator>,
) -> Option<TlaType> {
    param_used_as_set_domain_depth(expr, param_name, operators, 0)
}

fn param_used_as_set_domain_depth(
    expr: &TirExpr,
    param_name: &str,
    operators: &HashMap<String, &TirOperator>,
    depth: usize,
) -> Option<TlaType> {
    if depth > MAX_TYPE_INFER_DEPTH {
        return None;
    }
    match expr {
        TirExpr::Forall { vars, body } | TirExpr::Exists { vars, body } => {
            for v in vars {
                if let Some(domain) = &v.domain {
                    if matches!(&domain.node, TirExpr::Name(n) if n.name == param_name) {
                        // The param is used as domain; infer element type from the bound var's usage
                        let elem_ty = infer_bound_var_type(&v.name, &body.node, operators);
                        if !matches!(elem_ty, TlaType::Unknown) {
                            return Some(elem_ty);
                        }
                    }
                }
            }
            param_used_as_set_domain_depth(&body.node, param_name, operators, depth + 1)
        }
        TirExpr::Choose { var, body } => {
            if let Some(domain) = &var.domain {
                if matches!(&domain.node, TirExpr::Name(n) if n.name == param_name) {
                    let elem_ty = infer_bound_var_type(&var.name, &body.node, operators);
                    if !matches!(elem_ty, TlaType::Unknown) {
                        return Some(elem_ty);
                    }
                }
            }
            param_used_as_set_domain_depth(&body.node, param_name, operators, depth + 1)
        }
        TirExpr::SetFilter { var, body } => {
            // SetFilter: {x \in S : P(x)} — domain is in var.domain
            if let Some(domain) = &var.domain {
                if matches!(&domain.node, TirExpr::Name(n) if n.name == param_name) {
                    let elem_ty = infer_bound_var_type(&var.name, &body.node, operators);
                    if !matches!(elem_ty, TlaType::Unknown) {
                        return Some(elem_ty);
                    }
                }
            }
            param_used_as_set_domain_depth(&body.node, param_name, operators, depth + 1)
        }
        TirExpr::BoolBinOp { left, right, .. }
        | TirExpr::Cmp { left, right, .. }
        | TirExpr::ArithBinOp { left, right, .. }
        | TirExpr::SetBinOp { left, right, .. } => {
            param_used_as_set_domain_depth(&left.node, param_name, operators, depth + 1)
                .or_else(|| param_used_as_set_domain_depth(&right.node, param_name, operators, depth + 1))
        }
        TirExpr::BoolNot(inner)
        | TirExpr::Prime(inner)
        | TirExpr::Powerset(inner)
        | TirExpr::BigUnion(inner)
        | TirExpr::Domain(inner) => param_used_as_set_domain_depth(&inner.node, param_name, operators, depth + 1),
        TirExpr::KSubset { base, k } => {
            param_used_as_set_domain_depth(&base.node, param_name, operators, depth + 1)
                .or_else(|| param_used_as_set_domain_depth(&k.node, param_name, operators, depth + 1))
        }
        TirExpr::If { cond, then_, else_ } => {
            param_used_as_set_domain_depth(&cond.node, param_name, operators, depth + 1)
                .or_else(|| param_used_as_set_domain_depth(&then_.node, param_name, operators, depth + 1))
                .or_else(|| param_used_as_set_domain_depth(&else_.node, param_name, operators, depth + 1))
        }
        TirExpr::Let { defs, body } => {
            for d in defs {
                if let Some(t) = param_used_as_set_domain_depth(&d.body.node, param_name, operators, depth + 1) {
                    return Some(t);
                }
            }
            param_used_as_set_domain_depth(&body.node, param_name, operators, depth + 1)
        }
        TirExpr::Label { body, .. } => param_used_as_set_domain_depth(&body.node, param_name, operators, depth + 1),
        TirExpr::Apply { op, args } => {
            // Check if param is passed to another operator where the corresponding
            // param is used as a set domain
            if let TirExpr::Name(op_name) = &op.node {
                if let Some(target) = operators.get(&op_name.name) {
                    for (i, arg) in args.iter().enumerate() {
                        if matches!(&arg.node, TirExpr::Name(n) if n.name == param_name) {
                            if let Some(tp) = target.params.get(i) {
                                if let Some(elem_ty) =
                                    param_used_as_set_domain_depth(&target.body.node, tp, operators, depth + 1)
                                {
                                    return Some(elem_ty);
                                }
                            }
                        }
                    }
                }
            }
            for a in args {
                if let Some(t) = param_used_as_set_domain_depth(&a.node, param_name, operators, depth + 1) {
                    return Some(t);
                }
            }
            None
        }
        TirExpr::FuncApply { func, arg } => {
            param_used_as_set_domain_depth(&func.node, param_name, operators, depth + 1)
                .or_else(|| param_used_as_set_domain_depth(&arg.node, param_name, operators, depth + 1))
        }
        _ => None,
    }
}

/// Infer the type of a bound variable from how it's used in the body.
fn infer_bound_var_type(
    var_name: &str,
    body: &TirExpr,
    operators: &HashMap<String, &TirOperator>,
) -> TlaType {
    // Check if the variable is used in arithmetic directly or transitively
    if param_used_in_arithmetic(body, var_name) {
        return TlaType::Int;
    }
    if param_arithmetic_via_apply(body, var_name, operators) {
        return TlaType::Int;
    }
    TlaType::Unknown
}

/// Check if param is used arithmetically through an operator call.
fn param_arithmetic_via_apply(
    expr: &TirExpr,
    param_name: &str,
    operators: &HashMap<String, &TirOperator>,
) -> bool {
    param_arithmetic_via_apply_depth(expr, param_name, operators, 0)
}

fn param_arithmetic_via_apply_depth(
    expr: &TirExpr,
    param_name: &str,
    operators: &HashMap<String, &TirOperator>,
    depth: usize,
) -> bool {
    if depth > MAX_TYPE_INFER_DEPTH {
        return false;
    }
    match expr {
        TirExpr::Apply { op, args } => {
            if let TirExpr::Name(op_name) = &op.node {
                if let Some(target) = operators.get(&op_name.name) {
                    for (i, arg) in args.iter().enumerate() {
                        if matches!(&arg.node, TirExpr::Name(n) if n.name == param_name) {
                            if let Some(tp) = target.params.get(i) {
                                // Check both direct arithmetic and transitive
                                // through further operator calls (e.g. LitFalse -> Var)
                                if param_used_in_arithmetic(&target.body.node, tp)
                                    || param_arithmetic_via_apply_depth(&target.body.node, tp, operators, depth + 1)
                                {
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
            args.iter()
                .any(|a| param_arithmetic_via_apply_depth(&a.node, param_name, operators, depth + 1))
        }
        TirExpr::BoolBinOp { left, right, .. } | TirExpr::Cmp { left, right, .. } => {
            param_arithmetic_via_apply(&left.node, param_name, operators)
                || param_arithmetic_via_apply(&right.node, param_name, operators)
        }
        TirExpr::If { cond, then_, else_ } => {
            param_arithmetic_via_apply(&cond.node, param_name, operators)
                || param_arithmetic_via_apply(&then_.node, param_name, operators)
                || param_arithmetic_via_apply(&else_.node, param_name, operators)
        }
        TirExpr::Let { defs, body } => {
            defs.iter()
                .any(|d| param_arithmetic_via_apply(&d.body.node, param_name, operators))
                || param_arithmetic_via_apply(&body.node, param_name, operators)
        }
        TirExpr::Label { body, .. }
        | TirExpr::Exists { body, .. }
        | TirExpr::Forall { body, .. } => {
            param_arithmetic_via_apply(&body.node, param_name, operators)
        }
        TirExpr::BoolNot(inner) => param_arithmetic_via_apply(&inner.node, param_name, operators),
        TirExpr::FuncApply { func, arg } => {
            param_arithmetic_via_apply(&func.node, param_name, operators)
                || param_arithmetic_via_apply(&arg.node, param_name, operators)
        }
        _ => false,
    }
}

fn infer_type_from_tir_expr(expr: &TirExpr) -> TlaType {
    stack_safe(|| infer_type_from_tir_expr_inner(expr))
}

fn infer_type_from_tir_expr_inner(expr: &TirExpr) -> TlaType {
    match expr {
        TirExpr::Const { ty, .. } => tir_type_to_tla_type(ty),
        TirExpr::Name(name_ref) => {
            // Resolve operator/constant names via thread-local type map.
            let resolved = OPERATOR_RETURN_TYPES.with(|cell| {
                cell.borrow().get(&name_ref.name).cloned()
            });
            if let Some(ty) = resolved {
                return ty;
            }
            tir_type_to_tla_type(&name_ref.ty)
        }
        TirExpr::FuncDef { body, vars } => {
            // [x \in S |-> expr] => TlaFunc<domain_type, body_type>
            let key_ty = if let Some(var) = vars.first() {
                if let Some(domain) = &var.domain {
                    infer_element_type_from_tir_set(&domain.node)
                } else {
                    TlaType::Unknown
                }
            } else {
                TlaType::Unknown
            };
            let val_ty = infer_type_from_tir_expr(&body.node);
            TlaType::Func(Box::new(key_ty), Box::new(val_ty))
        }
        TirExpr::Tuple(elems) => {
            // Sequences are represented as tuples in init
            if elems.is_empty() {
                TlaType::Seq(Box::new(TlaType::Unknown))
            } else {
                let elem_types: Vec<_> = elems
                    .iter()
                    .map(|e| infer_type_from_tir_expr(&e.node))
                    .collect();
                // If all same type, it is a sequence
                if elem_types.iter().all(|t| t == &elem_types[0]) {
                    TlaType::Seq(Box::new(elem_types[0].clone()))
                } else {
                    TlaType::Tuple(elem_types)
                }
            }
        }
        TirExpr::SetEnum(elems) => {
            if elems.is_empty() {
                TlaType::Set(Box::new(TlaType::Unknown))
            } else {
                TlaType::Set(Box::new(infer_type_from_tir_expr(&elems[0].node)))
            }
        }
        TirExpr::Record(fields) => {
            // Infer record type from field name/value pairs
            let typed_fields: Vec<(String, TlaType)> = fields
                .iter()
                .map(|(f, v)| (f.name.clone(), infer_type_from_tir_expr(&v.node)))
                .collect();
            TlaType::Record(typed_fields)
        }
        TirExpr::RecordSet(_fields) => {
            // RecordSet: [field: SetOfValues, ...] -> Set<Value>
            // Records are wrapped as Value in generated code.
            TlaType::Set(Box::new(TlaType::Unknown))
        }
        TirExpr::FuncSet { domain, range } => {
            // [S -> T]: Set(Func(elem(S), elem(T)))
            let key_ty = infer_element_type_from_tir_set(&domain.node);
            let val_ty = infer_element_type_from_tir_set(&range.node);
            TlaType::Set(Box::new(TlaType::Func(Box::new(key_ty), Box::new(val_ty))))
        }
        TirExpr::BoolBinOp { .. }
        | TirExpr::BoolNot(_)
        | TirExpr::Cmp { .. }
        | TirExpr::In { .. }
        | TirExpr::Subseteq { .. } => TlaType::Bool,
        TirExpr::ArithBinOp { .. } | TirExpr::ArithNeg(_) => TlaType::Int,
        _ => {
            // Use TIR type system
            tir_type_to_tla_type(&expr.ty())
        }
    }
}

fn infer_element_type_from_tir_set(expr: &TirExpr) -> TlaType {
    match expr {
        TirExpr::Range { .. } => TlaType::Int,
        TirExpr::SetEnum(elems) => {
            if elems.is_empty() {
                TlaType::Unknown
            } else {
                infer_type_from_tir_expr(&elems[0].node)
            }
        }
        TirExpr::Name(name_ref) => {
            // Resolve operator/constant names to their return types.
            // e.g., Node == 0..N-1 => Set(Int), so element type is Int.
            let resolved = OPERATOR_RETURN_TYPES.with(|cell| {
                cell.borrow().get(&name_ref.name).cloned()
            });
            if let Some(ty) = resolved {
                match ty {
                    TlaType::Set(inner) => return *inner,
                    _ => {}
                }
            }
            // Fall through to TIR type system
            let ty = expr.ty();
            match &ty {
                TirType::Set(inner) => tir_type_to_tla_type(inner),
                _ => TlaType::Unknown,
            }
        }
        TirExpr::RecordSet(_fields) => {
            // RecordSet element type is Value (records wrapped as Value).
            TlaType::Unknown
        }
        TirExpr::FuncSet { domain, range } => {
            // [S -> T] has element type = Func(elem(S), elem(T))
            let key_ty = infer_element_type_from_tir_set(&domain.node);
            let val_ty = infer_element_type_from_tir_set(&range.node);
            TlaType::Func(Box::new(key_ty), Box::new(val_ty))
        }
        TirExpr::SetBinOp { left, .. } => {
            // Union/intersect/difference preserves element type
            infer_element_type_from_tir_set(&left.node)
        }
        TirExpr::Powerset(inner) => {
            // SUBSET S has element type = Set of inner elem type
            let inner_ty = infer_element_type_from_tir_set(&inner.node);
            TlaType::Set(Box::new(inner_ty))
        }
        TirExpr::SetFilter { var, .. } => {
            // {x \in S : P(x)} has same element type as S
            if let Some(domain) = &var.domain {
                infer_element_type_from_tir_set(&domain.node)
            } else {
                TlaType::Unknown
            }
        }
        TirExpr::SetBuilder { body, .. } => {
            // {expr : x \in S} has element type = type of expr
            infer_type_from_tir_expr(&body.node)
        }
        TirExpr::Apply { op, args } => {
            // Resolve operator application: e.g., DOMAIN(f) -> set element type
            if let TirExpr::Name(name_ref) = &op.node {
                if name_ref.name == "DOMAIN" && args.len() == 1 {
                    // DOMAIN(f) has element type = key type of f
                    let func_ty = infer_type_from_tir_expr(&args[0].node);
                    if let TlaType::Func(k, _) = func_ty {
                        return *k;
                    }
                }
            }
            // Try the TIR type system
            let ty = expr.ty();
            match &ty {
                TirType::Set(inner) => tir_type_to_tla_type(inner),
                _ => TlaType::Unknown,
            }
        }
        _ => {
            // Try the TIR type system for anything else
            let ty = expr.ty();
            match &ty {
                TirType::Set(inner) => tir_type_to_tla_type(inner),
                _ => TlaType::Unknown,
            }
        }
    }
}

fn tir_type_to_tla_type(ty: &TirType) -> TlaType {
    match ty {
        TirType::Bool => TlaType::Bool,
        TirType::Int => TlaType::Int,
        TirType::Str => TlaType::String,
        TirType::Set(inner) => TlaType::Set(Box::new(tir_type_to_tla_type(inner))),
        TirType::Seq(inner) => TlaType::Seq(Box::new(tir_type_to_tla_type(inner))),
        TirType::Func(k, v) => TlaType::Func(
            Box::new(tir_type_to_tla_type(k)),
            Box::new(tir_type_to_tla_type(v)),
        ),
        TirType::Tuple(ts) => TlaType::Tuple(ts.iter().map(tir_type_to_tla_type).collect()),
        TirType::Record(fields) => {
            // Resolve NameId -> string via the global name interner
            let resolved: Vec<(String, TlaType)> = fields
                .iter()
                .map(|(name_id, ty)| {
                    let name = tla_core::resolve_name_id(*name_id).to_string();
                    (name, tir_type_to_tla_type(ty))
                })
                .collect();
            TlaType::Record(resolved)
        }
        TirType::OpenRecord(fields, _) => {
            let resolved: Vec<(String, TlaType)> = fields
                .iter()
                .map(|(name_id, ty)| {
                    let name = tla_core::resolve_name_id(*name_id).to_string();
                    (name, tir_type_to_tla_type(ty))
                })
                .collect();
            if resolved.is_empty() {
                TlaType::Unknown
            } else {
                TlaType::Record(resolved)
            }
        }
        TirType::Var(_) | TirType::Variant(_) => TlaType::Unknown,
        TirType::Dyn => TlaType::Unknown,
    }
}

/// Infer the element type of a set constant from its .cfg string representation.
///
/// Examines the first element of the set to determine the type:
/// - `{1, 2, 3}` -> `TlaType::Int`
/// - `{"a", "b"}` -> `TlaType::String`
/// - `{TRUE, FALSE}` -> `TlaType::Bool`
/// - Empty or unparseable -> `TlaType::Int` (conservative default)
fn infer_set_element_type_from_cfg(set_str: &str) -> TlaType {
    let trimmed = set_str.trim();
    if !trimmed.starts_with('{') || !trimmed.ends_with('}') {
        return TlaType::Int;
    }
    let inner = trimmed[1..trimmed.len() - 1].trim();
    if inner.is_empty() {
        return TlaType::Int;
    }
    // Get the first element
    let elements = split_tla_elements(inner);
    if let Some(first) = elements.first() {
        let first = first.trim();
        if first.starts_with('"') {
            return TlaType::String;
        }
        if first == "TRUE" || first == "FALSE" {
            return TlaType::Bool;
        }
        if first.starts_with('{') {
            // Nested set -- element type is a set; recurse to determine inner element type
            return TlaType::Set(Box::new(infer_set_element_type_from_cfg(first)));
        }
        // Check if it's a number
        if first.parse::<i64>().is_ok() {
            return TlaType::Int;
        }
        // Bare identifier: model value -- use dynamic Value type
        if first.chars().all(|c| c.is_alphanumeric() || c == '_') && !first.is_empty() {
            return TlaType::Unknown;
        }
    }
    TlaType::Int
}

/// Translate a TLA+ constant value string from .cfg to (Rust type, Rust expression).
///
/// Handles:
/// - Simple integers: "3" -> ("i64", "3_i64")
/// - Strings: "\"hello\"" -> ("String", "\"hello\".to_string()")
/// - Sets of integers: "{1, 2, 3}" -> lazy init with tla_set!
/// - Nested sets: "{{1, 2}, {-1, 3}}" -> lazy init with nested tla_set!
/// - Model values: bare identifiers -> ("Value", "Value::ModelValue(\"name\".to_string())")
fn translate_constant_value(value: &str) -> (String, String) {
    translate_constant_value_with_name(value, None)
}

/// Translate a constant value, with optional constant name for model value detection.
///
/// When `const_name` is provided and equals the value, this is a TLC model value
/// (e.g., `a = a` in the .cfg file means "a" is a symbolic constant).
fn translate_constant_value_with_name(value: &str, const_name: Option<&str>) -> (String, String) {
    // Strip TLA+ line comments (\* ...) before processing
    let trimmed = if let Some(idx) = value.find("\\*") {
        value[..idx].trim()
    } else {
        value.trim()
    };

    // Integer
    if let Ok(_n) = trimmed.parse::<i64>() {
        return ("i64".to_string(), format!("{trimmed}_i64"));
    }

    // Boolean
    if trimmed == "TRUE" {
        return ("bool".to_string(), "true".to_string());
    }
    if trimmed == "FALSE" {
        return ("bool".to_string(), "false".to_string());
    }

    // String
    if trimmed.starts_with('"') && trimmed.ends_with('"') {
        return ("String".to_string(), format!("{trimmed}.to_string()"));
    }

    // Set literal: { ... }
    if trimmed.starts_with('{') && trimmed.ends_with('}') {
        let rust_expr = parse_tla_set_to_rust(trimmed);
        return ("set".to_string(), rust_expr);
    }

    // Model value: when value equals the constant name (e.g., `a = a` in cfg)
    // or when value is a bare identifier (not a number/bool/string/set)
    if let Some(cn) = const_name {
        if trimmed == cn {
            return (
                "Value".to_string(),
                format!("Value::ModelValue({trimmed:?}.to_string())"),
            );
        }
    }

    // Bare identifier fallback: treat as model value
    if trimmed.chars().all(|c| c.is_alphanumeric() || c == '_') && !trimmed.is_empty() {
        return (
            "Value".to_string(),
            format!("Value::ModelValue({trimmed:?}.to_string())"),
        );
    }

    // Fallback: complex TLA+ expressions can't be translated as constant literals.
    // Emit Value::Bool(false) as a safe placeholder instead of raw TLA+ text.
    (
        "Value".to_string(),
        format!(
            "Value::Bool(false) /* untranslated constant: {} */",
            trimmed.replace("*/", "* /")
        ),
    )
}

/// Parse a TLA+ set literal string into a Rust expression.
///
/// Examples:
/// - "{1, 2, 3}" -> "tla_set![1_i64, 2_i64, 3_i64]"
/// - "{{1, 2}, {-1, 3}}" -> "tla_set![tla_set![1_i64, 2_i64], tla_set![-1_i64, 3_i64]]"
fn parse_tla_set_to_rust(s: &str) -> String {
    let s = s.trim();
    if !s.starts_with('{') || !s.ends_with('}') {
        return s.to_string();
    }

    let inner = &s[1..s.len() - 1].trim();
    if inner.is_empty() {
        return "TlaSet::new()".to_string();
    }

    // Split by commas, respecting nested braces
    let elements = split_tla_elements(inner);
    let rust_elems: Vec<String> = elements
        .iter()
        .map(|elem| {
            let elem = elem.trim();
            if elem.starts_with('{') {
                // Nested set
                parse_tla_set_to_rust(elem)
            } else if let Ok(_n) = elem.parse::<i64>() {
                format!("{elem}_i64")
            } else if elem.starts_with('"') {
                format!("{elem}.to_string()")
            } else if elem == "TRUE" {
                "true".to_string()
            } else if elem == "FALSE" {
                "false".to_string()
            } else if elem.chars().all(|c| c.is_alphanumeric() || c == '_') && !elem.is_empty() {
                // Bare identifier in a set literal: treat as model value
                format!("Value::ModelValue({elem:?}.to_string())")
            } else {
                elem.to_string()
            }
        })
        .collect();

    format!("tla_set![{}]", rust_elems.join(", "))
}

/// Split a comma-separated TLA+ element list, respecting nested braces.
fn split_tla_elements(s: &str) -> Vec<String> {
    let mut result = Vec::new();
    let mut current = String::new();
    let mut depth = 0;

    for c in s.chars() {
        match c {
            '{' => {
                depth += 1;
                current.push(c);
            }
            '}' => {
                depth -= 1;
                current.push(c);
            }
            ',' if depth == 0 => {
                result.push(current.trim().to_string());
                current.clear();
            }
            _ => {
                current.push(c);
            }
        }
    }
    if !current.trim().is_empty() {
        result.push(current.trim().to_string());
    }
    result
}

/// Produce a type-appropriate default value for state variables that
/// lack an Init assignment. Uses the inferred type when available.
fn type_aware_default(ty: Option<&TlaType>) -> &'static str {
    match ty {
        Some(TlaType::Int) => "0_i64",
        Some(TlaType::Bool) => "false",
        Some(TlaType::String) => "String::new()",
        Some(TlaType::Set(_)) => "TlaSet::new()",
        Some(TlaType::Seq(_)) => "Vec::new()",
        Some(TlaType::Func(_, _)) => "TlaFunc::new()",
        Some(TlaType::Record(_)) => "TlaRecord::new()",
        Some(TlaType::Tuple(_)) => "Value::Tuple(Vec::new())",
        _ => "Value::Bool(false) /* unresolved default */",
    }
}

/// Wrap an expression with `Value::from(...)` if the target variable type is `Value`
/// (i.e., `TlaType::Unknown` or absent from the type map).
///
/// This prevents E0308 type mismatches when assigning concrete typed values
/// (e.g., `TlaFunc<i64, i64>`) to `Value`-typed state fields.
fn wrap_for_value_type(expr: &str, var_type: Option<&TlaType>) -> String {
    match var_type {
        None | Some(TlaType::Unknown) => format!("Value::from({expr})"),
        _ => expr.to_string(),
    }
}
