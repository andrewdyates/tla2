// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 dep-graph` — operator dependency graph in DOT format.
//!
//! Produces a DOT-format dependency graph showing which operators
//! call which other operators.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the dep-graph command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DepgraphOutputFormat {
    Human,
    Json,
    Dot,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Generate operator dependency graph.
pub(crate) fn cmd_depgraph(
    file: &Path,
    format: DepgraphOutputFormat,
) -> Result<()> {
    let start = Instant::now();

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

    // Collect all operator names.
    let mut op_names: Vec<String> = Vec::new();
    let mut edges: Vec<(String, String)> = Vec::new();

    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            let name = def.name.node.clone();
            op_names.push(name.clone());
            let mut callees = Vec::new();
            collect_ident_refs(&def.body.node, &mut callees);
            for callee in callees {
                edges.push((name.clone(), callee));
            }
        }
    }

    // Filter edges to only reference known operators.
    let op_set: std::collections::BTreeSet<&str> =
        op_names.iter().map(|s| s.as_str()).collect();
    let edges: Vec<(String, String)> = edges
        .into_iter()
        .filter(|(_, to)| op_set.contains(to.as_str()))
        .collect();

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        DepgraphOutputFormat::Human => {
            println!("dep-graph: {}", file.display());
            println!("  operators: {}", op_names.len());
            println!("  edges: {}", edges.len());
            println!();
            for (from, to) in &edges {
                println!("  {from} -> {to}");
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        DepgraphOutputFormat::Dot => {
            println!("digraph deps {{");
            println!("  rankdir=LR;");
            for (from, to) in &edges {
                println!("  \"{from}\" -> \"{to}\";");
            }
            println!("}}");
        }
        DepgraphOutputFormat::Json => {
            let edges_json: Vec<serde_json::Value> = edges
                .iter()
                .map(|(from, to)| {
                    serde_json::json!({
                        "from": from,
                        "to": to,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "operators": op_names,
                "edges": edges_json,
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

fn collect_ident_refs(expr: &Expr, refs: &mut Vec<String>) {
    match expr {
        Expr::Ident(name, _) => {
            refs.push(name.clone());
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Eq(a, b) | Expr::Neq(a, b)
        | Expr::Lt(a, b) | Expr::Gt(a, b) | Expr::Leq(a, b) | Expr::Geq(a, b)
        | Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Div(a, b)
        | Expr::Mod(a, b) | Expr::Range(a, b) | Expr::In(a, b) | Expr::NotIn(a, b)
        | Expr::Implies(a, b) | Expr::Subseteq(a, b) => {
            collect_ident_refs(&a.node, refs);
            collect_ident_refs(&b.node, refs);
        }
        Expr::Not(inner) | Expr::Neg(inner) | Expr::Prime(inner) => {
            collect_ident_refs(&inner.node, refs);
        }
        Expr::If(cond, then, els) => {
            collect_ident_refs(&cond.node, refs);
            collect_ident_refs(&then.node, refs);
            collect_ident_refs(&els.node, refs);
        }
        Expr::SetEnum(elems) | Expr::Times(elems) => {
            for e in elems {
                collect_ident_refs(&e.node, refs);
            }
        }
        Expr::Apply(f, args) => {
            collect_ident_refs(&f.node, refs);
            for a in args {
                collect_ident_refs(&a.node, refs);
            }
        }
        Expr::Forall(_, body) | Expr::Exists(_, body) => {
            collect_ident_refs(&body.node, refs);
        }
        _ => {}
    }
}
