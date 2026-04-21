// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 slice` — specification slicing.
//!
//! Extracts the relevant portion of a TLA+ specification for a given
//! property or invariant. Computes the transitive dependency closure
//! of the target operator, identifying which variables, operators,
//! and constants are needed.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the slice command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SliceOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Run specification slicing for a target operator.
pub(crate) fn cmd_slice(
    file: &Path,
    target: &str,
    format: SliceOutputFormat,
) -> Result<()> {
    let start = Instant::now();

    // --- Parse and lower ---------------------------------------------------

    let source = read_source(file)?;
    let tree = parse_to_syntax_tree(&source);
    let lower_result = lower(FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &lower_result.errors {
            let diagnostic =
                tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "lowering failed with {} error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .context("lowering produced no module")?;

    // --- Extract operators and variables -----------------------------------

    let operators = extract_operators(&module);
    let all_vars = extract_var_names(&module);
    let all_constants = extract_constant_names(&module);

    if !operators.contains_key(target) {
        bail!(
            "target operator `{target}` not found. Available: {}",
            operators.keys().cloned().collect::<Vec<_>>().join(", ")
        );
    }

    // --- Build dependency graph --------------------------------------------

    let mut deps: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (name, op) in &operators {
        let mut refs = BTreeSet::new();
        collect_operator_refs(&op.body.node, &operators, &mut refs);
        deps.insert(name.clone(), refs);
    }

    // --- Compute transitive closure from target ----------------------------

    let mut needed_ops = BTreeSet::new();
    let mut queue = vec![target.to_string()];
    while let Some(op_name) = queue.pop() {
        if needed_ops.contains(&op_name) {
            continue;
        }
        needed_ops.insert(op_name.clone());
        if let Some(op_deps) = deps.get(&op_name) {
            for dep in op_deps {
                if !needed_ops.contains(dep) {
                    queue.push(dep.clone());
                }
            }
        }
    }

    // --- Determine needed variables and constants --------------------------

    let mut needed_vars = BTreeSet::new();
    let mut needed_constants = BTreeSet::new();

    for op_name in &needed_ops {
        if let Some(op) = operators.get(op_name.as_str()) {
            collect_var_refs(&op.body.node, &all_vars, &mut needed_vars);
            collect_constant_refs(&op.body.node, &all_constants, &mut needed_constants);
        }
    }

    let excluded_ops: BTreeSet<String> = operators
        .keys()
        .filter(|k| !needed_ops.contains(*k))
        .cloned()
        .collect();
    let excluded_vars: BTreeSet<String> = all_vars
        .iter()
        .filter(|v| !needed_vars.contains(*v))
        .cloned()
        .collect();

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        SliceOutputFormat::Human => {
            println!("slice: {} -> {target}", file.display());
            println!();
            println!("  Needed operators ({}):", needed_ops.len());
            for op in &needed_ops {
                let param_count = operators.get(op.as_str()).map_or(0, |o| o.params.len());
                if param_count > 0 {
                    println!("    {op}({param_count} params)");
                } else {
                    println!("    {op}");
                }
            }
            println!();
            println!("  Needed variables ({}):", needed_vars.len());
            for v in &needed_vars {
                println!("    {v}");
            }
            if !needed_constants.is_empty() {
                println!();
                println!("  Needed constants ({}):", needed_constants.len());
                for c in &needed_constants {
                    println!("    {c}");
                }
            }
            if !excluded_ops.is_empty() {
                println!();
                println!("  Excluded operators ({}):", excluded_ops.len());
                for op in &excluded_ops {
                    println!("    {op}");
                }
            }
            if !excluded_vars.is_empty() {
                println!();
                println!("  Excluded variables ({}):", excluded_vars.len());
                for v in &excluded_vars {
                    println!("    {v}");
                }
            }
            println!();
            println!(
                "  Slice: {}/{} operators, {}/{} variables",
                needed_ops.len(),
                operators.len(),
                needed_vars.len(),
                all_vars.len(),
            );
            println!("  elapsed: {elapsed:.2}s");
        }
        SliceOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "target": target,
                "needed_operators": needed_ops.iter().collect::<Vec<_>>(),
                "needed_variables": needed_vars.iter().collect::<Vec<_>>(),
                "needed_constants": needed_constants.iter().collect::<Vec<_>>(),
                "excluded_operators": excluded_ops.iter().collect::<Vec<_>>(),
                "excluded_variables": excluded_vars.iter().collect::<Vec<_>>(),
                "statistics": {
                    "total_operators": operators.len(),
                    "total_variables": all_vars.len(),
                    "slice_operators": needed_ops.len(),
                    "slice_variables": needed_vars.len(),
                    "elapsed_seconds": elapsed,
                },
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn extract_operators(module: &Module) -> BTreeMap<String, &OperatorDef> {
    let mut ops = BTreeMap::new();
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            ops.insert(def.name.node.clone(), def);
        }
    }
    ops
}

fn extract_var_names(module: &Module) -> BTreeSet<String> {
    let mut vars = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Variable(decls) = &unit.node {
            for decl in decls {
                vars.insert(decl.node.clone());
            }
        }
    }
    vars
}

fn extract_constant_names(module: &Module) -> BTreeSet<String> {
    let mut constants = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Constant(decls) = &unit.node {
            for decl in decls {
                constants.insert(decl.name.node.clone());
            }
        }
    }
    constants
}

/// Collect operator names referenced in an expression.
fn collect_operator_refs(
    expr: &Expr,
    known_ops: &BTreeMap<String, &OperatorDef>,
    refs: &mut BTreeSet<String>,
) {
    match expr {
        Expr::Ident(name, _) => {
            if known_ops.contains_key(name.as_str()) {
                refs.insert(name.clone());
            }
        }
        Expr::Apply(f, args) => {
            collect_operator_refs(&f.node, known_ops, refs);
            for arg in args {
                collect_operator_refs(&arg.node, known_ops, refs);
            }
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b)
        | Expr::Eq(a, b) | Expr::Neq(a, b) | Expr::Lt(a, b) | Expr::Gt(a, b)
        | Expr::Leq(a, b) | Expr::Geq(a, b) | Expr::In(a, b) => {
            collect_operator_refs(&a.node, known_ops, refs);
            collect_operator_refs(&b.node, known_ops, refs);
        }
        Expr::Not(inner) | Expr::Prime(inner) | Expr::Neg(inner) => {
            collect_operator_refs(&inner.node, known_ops, refs);
        }
        Expr::If(c, t, e) => {
            collect_operator_refs(&c.node, known_ops, refs);
            collect_operator_refs(&t.node, known_ops, refs);
            collect_operator_refs(&e.node, known_ops, refs);
        }
        _ => {}
    }
}

/// Collect variable names referenced in an expression.
fn collect_var_refs(expr: &Expr, all_vars: &BTreeSet<String>, refs: &mut BTreeSet<String>) {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            if all_vars.contains(name.as_str()) {
                refs.insert(name.clone());
            }
        }
        Expr::Apply(f, args) => {
            collect_var_refs(&f.node, all_vars, refs);
            for arg in args {
                collect_var_refs(&arg.node, all_vars, refs);
            }
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b)
        | Expr::Eq(a, b) | Expr::Neq(a, b) | Expr::Lt(a, b) | Expr::Gt(a, b)
        | Expr::Leq(a, b) | Expr::Geq(a, b) | Expr::In(a, b) => {
            collect_var_refs(&a.node, all_vars, refs);
            collect_var_refs(&b.node, all_vars, refs);
        }
        Expr::Not(inner) | Expr::Prime(inner) | Expr::Neg(inner) => {
            collect_var_refs(&inner.node, all_vars, refs);
        }
        Expr::If(c, t, e) => {
            collect_var_refs(&c.node, all_vars, refs);
            collect_var_refs(&t.node, all_vars, refs);
            collect_var_refs(&e.node, all_vars, refs);
        }
        _ => {}
    }
}

/// Collect constant names referenced in an expression.
fn collect_constant_refs(
    expr: &Expr,
    all_constants: &BTreeSet<String>,
    refs: &mut BTreeSet<String>,
) {
    match expr {
        Expr::Ident(name, _) => {
            if all_constants.contains(name.as_str()) {
                refs.insert(name.clone());
            }
        }
        Expr::Apply(f, args) => {
            collect_constant_refs(&f.node, all_constants, refs);
            for arg in args {
                collect_constant_refs(&arg.node, all_constants, refs);
            }
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b)
        | Expr::Eq(a, b) | Expr::Neq(a, b) | Expr::Lt(a, b) | Expr::Gt(a, b)
        | Expr::Leq(a, b) | Expr::Geq(a, b) | Expr::In(a, b) => {
            collect_constant_refs(&a.node, all_constants, refs);
            collect_constant_refs(&b.node, all_constants, refs);
        }
        Expr::Not(inner) | Expr::Prime(inner) | Expr::Neg(inner) => {
            collect_constant_refs(&inner.node, all_constants, refs);
        }
        Expr::If(c, t, e) => {
            collect_constant_refs(&c.node, all_constants, refs);
            collect_constant_refs(&t.node, all_constants, refs);
            collect_constant_refs(&e.node, all_constants, refs);
        }
        _ => {}
    }
}
