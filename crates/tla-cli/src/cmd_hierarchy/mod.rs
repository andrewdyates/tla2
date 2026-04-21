// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 hierarchy` — operator call hierarchy.
//!
//! Builds and displays the call graph between operators in a TLA+
//! specification, showing which operators reference which others.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the hierarchy command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HierarchyOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Display the operator call hierarchy of a TLA+ spec.
pub(crate) fn cmd_hierarchy(
    file: &Path,
    format: HierarchyOutputFormat,
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

    // --- Build call graph --------------------------------------------------

    let operators: BTreeMap<String, &OperatorDef> = module
        .units
        .iter()
        .filter_map(|u| {
            if let Unit::Operator(def) = &u.node {
                Some((def.name.node.clone(), def))
            } else {
                None
            }
        })
        .collect();

    let mut call_graph: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut reverse_graph: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

    for (name, op) in &operators {
        let callees = collect_callees(&op.body.node, &operators);
        for callee in &callees {
            reverse_graph
                .entry(callee.clone())
                .or_default()
                .insert(name.clone());
        }
        call_graph.insert(name.clone(), callees);
    }

    // Find root operators (called by no one).
    let roots: Vec<String> = operators
        .keys()
        .filter(|name| !reverse_graph.contains_key(name.as_str()))
        .cloned()
        .collect();

    // Find leaf operators (call no one).
    let leaves: Vec<String> = call_graph
        .iter()
        .filter(|(_, callees)| callees.is_empty())
        .map(|(name, _)| name.clone())
        .collect();

    let total_edges: usize = call_graph.values().map(|c| c.len()).sum();

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        HierarchyOutputFormat::Human => {
            println!("hierarchy: {}", file.display());
            println!("  operators: {}", operators.len());
            println!("  call edges: {total_edges}");
            println!("  roots (not called): {}", roots.join(", "));
            println!("  leaves (calls nothing): {}", leaves.join(", "));
            println!();
            println!("  Call graph:");
            for (name, callees) in &call_graph {
                if callees.is_empty() {
                    println!("    {name} (leaf)");
                } else {
                    let callee_list: Vec<&str> = callees.iter().map(|s| s.as_str()).collect();
                    println!("    {name} -> {}", callee_list.join(", "));
                }
            }

            // Print tree view for roots.
            if !roots.is_empty() {
                println!();
                println!("  Hierarchy tree:");
                for root in &roots {
                    print_tree(root, &call_graph, &mut BTreeSet::new(), "", true);
                }
            }

            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        HierarchyOutputFormat::Json => {
            let graph_json: BTreeMap<String, Vec<String>> = call_graph
                .iter()
                .map(|(k, v)| (k.clone(), v.iter().cloned().collect()))
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "operators": operators.len(),
                "call_edges": total_edges,
                "roots": roots,
                "leaves": leaves,
                "call_graph": graph_json,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn collect_callees(
    expr: &Expr,
    known_ops: &BTreeMap<String, &OperatorDef>,
) -> BTreeSet<String> {
    let mut callees = BTreeSet::new();
    collect_callees_inner(expr, known_ops, &mut callees);
    callees
}

fn collect_callees_inner(
    expr: &Expr,
    known_ops: &BTreeMap<String, &OperatorDef>,
    callees: &mut BTreeSet<String>,
) {
    match expr {
        Expr::Ident(name, _) => {
            if known_ops.contains_key(name.as_str()) {
                callees.insert(name.clone());
            }
        }
        Expr::Apply(f, args) => {
            collect_callees_inner(&f.node, known_ops, callees);
            for arg in args {
                collect_callees_inner(&arg.node, known_ops, callees);
            }
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b)
        | Expr::Eq(a, b) | Expr::Neq(a, b) | Expr::Lt(a, b) | Expr::Gt(a, b)
        | Expr::Leq(a, b) | Expr::Geq(a, b) | Expr::In(a, b) => {
            collect_callees_inner(&a.node, known_ops, callees);
            collect_callees_inner(&b.node, known_ops, callees);
        }
        Expr::Not(inner) | Expr::Prime(inner) | Expr::Neg(inner) => {
            collect_callees_inner(&inner.node, known_ops, callees);
        }
        Expr::If(c, t, e) => {
            collect_callees_inner(&c.node, known_ops, callees);
            collect_callees_inner(&t.node, known_ops, callees);
            collect_callees_inner(&e.node, known_ops, callees);
        }
        _ => {}
    }
}

fn print_tree(
    name: &str,
    call_graph: &BTreeMap<String, BTreeSet<String>>,
    visited: &mut BTreeSet<String>,
    prefix: &str,
    is_last: bool,
) {
    let connector = if prefix.is_empty() {
        ""
    } else if is_last {
        "└── "
    } else {
        "├── "
    };

    if visited.contains(name) {
        println!("    {prefix}{connector}{name} (cycle)");
        return;
    }

    println!("    {prefix}{connector}{name}");
    visited.insert(name.to_string());

    if let Some(callees) = call_graph.get(name) {
        let callees_vec: Vec<&String> = callees.iter().collect();
        for (i, callee) in callees_vec.iter().enumerate() {
            let new_prefix = if prefix.is_empty() {
                String::new()
            } else if is_last {
                format!("{prefix}    ")
            } else {
                format!("{prefix}│   ")
            };
            print_tree(callee, call_graph, visited, &new_prefix, i == callees_vec.len() - 1);
        }
    }

    visited.remove(name);
}
