// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 unfold` — unfold operator definitions.
//!
//! Displays the fully unfolded body of a target operator, expanding
//! all referenced operator definitions inline. Useful for understanding
//! what a complex operator actually computes.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Module, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the unfold command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnfoldOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Unfold a target operator, showing its expanded definition.
pub(crate) fn cmd_unfold(
    file: &Path,
    target: &str,
    max_depth: usize,
    format: UnfoldOutputFormat,
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

    // --- Extract operators -------------------------------------------------

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

    let target_op = operators.get(target).ok_or_else(|| {
        anyhow::anyhow!(
            "operator `{target}` not found. Available: {}",
            operators.keys().cloned().collect::<Vec<_>>().join(", ")
        )
    })?;

    // --- Compute unfolding -------------------------------------------------

    let body_text = pretty_expr(&target_op.body.node);
    let params: Vec<String> = target_op.params.iter().map(|p| p.name.node.clone()).collect();

    // Find transitive dependencies up to max_depth.
    let mut deps_at_depth: Vec<Vec<String>> = Vec::new();
    let mut seen = BTreeSet::new();
    seen.insert(target.to_string());
    let mut frontier = vec![target.to_string()];

    for _depth in 0..max_depth {
        let mut next_frontier = Vec::new();
        for op_name in &frontier {
            if let Some(op) = operators.get(op_name.as_str()) {
                let refs = collect_refs(&op.body.node, &operators);
                for r in &refs {
                    if !seen.contains(r) {
                        seen.insert(r.clone());
                        next_frontier.push(r.clone());
                    }
                }
            }
        }
        if next_frontier.is_empty() {
            break;
        }
        deps_at_depth.push(next_frontier.clone());
        frontier = next_frontier;
    }

    let total_deps = seen.len() - 1; // exclude target itself

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        UnfoldOutputFormat::Human => {
            println!("unfold: {} -> {target}", file.display());
            if !params.is_empty() {
                println!("  parameters: {}", params.join(", "));
            }
            println!();
            println!("  Body:");
            println!("    {body_text}");
            println!();

            if total_deps > 0 {
                println!("  Dependencies ({total_deps} operators, max depth {max_depth}):");
                for (depth, deps) in deps_at_depth.iter().enumerate() {
                    for dep in deps {
                        let dep_body = operators
                            .get(dep.as_str())
                            .map(|o| pretty_expr(&o.body.node))
                            .unwrap_or_else(|| "(built-in)".to_string());
                        let truncated = if dep_body.len() > 80 {
                            format!("{}...", &dep_body[..77])
                        } else {
                            dep_body
                        };
                        println!("    [depth {}] {} == {}", depth + 1, dep, truncated);
                    }
                }
            } else {
                println!("  No operator dependencies (leaf operator).");
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        UnfoldOutputFormat::Json => {
            let ops_ref = &operators;
            let deps_json: Vec<serde_json::Value> = deps_at_depth
                .iter()
                .enumerate()
                .flat_map(|(depth, deps)| {
                    deps.iter().map(move |dep| {
                        let dep_body = ops_ref
                            .get(dep.as_str())
                            .map(|o| pretty_expr(&o.body.node))
                            .unwrap_or_default();
                        serde_json::json!({
                            "name": dep,
                            "depth": depth + 1,
                            "body": dep_body,
                        })
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "target": target,
                "parameters": params,
                "body": body_text,
                "dependencies": deps_json,
                "total_dependencies": total_deps,
                "max_depth": max_depth,
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

use tla_core::ast::Expr;

fn collect_refs(
    expr: &Expr,
    known_ops: &BTreeMap<String, &OperatorDef>,
) -> BTreeSet<String> {
    let mut refs = BTreeSet::new();
    collect_refs_inner(expr, known_ops, &mut refs);
    refs
}

fn collect_refs_inner(
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
            collect_refs_inner(&f.node, known_ops, refs);
            for arg in args {
                collect_refs_inner(&arg.node, known_ops, refs);
            }
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b)
        | Expr::Eq(a, b) | Expr::Neq(a, b) | Expr::Lt(a, b) | Expr::Gt(a, b)
        | Expr::Leq(a, b) | Expr::Geq(a, b) | Expr::In(a, b) => {
            collect_refs_inner(&a.node, known_ops, refs);
            collect_refs_inner(&b.node, known_ops, refs);
        }
        Expr::Not(inner) | Expr::Prime(inner) | Expr::Neg(inner) => {
            collect_refs_inner(&inner.node, known_ops, refs);
        }
        Expr::If(c, t, e) => {
            collect_refs_inner(&c.node, known_ops, refs);
            collect_refs_inner(&t.node, known_ops, refs);
            collect_refs_inner(&e.node, known_ops, refs);
        }
        _ => {}
    }
}
