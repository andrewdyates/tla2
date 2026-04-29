// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 metric` — specification complexity metrics.
//!
//! Computes structural complexity metrics for a TLA+ specification:
//! operator count, nesting depth, expression size, variable count, etc.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the metric command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MetricOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Compute complexity metrics for a TLA+ spec.
pub(crate) fn cmd_metric(file: &Path, format: MetricOutputFormat) -> Result<()> {
    let start = Instant::now();

    // --- Parse and lower ---------------------------------------------------

    let source = read_source(file)?;
    let tree = parse_to_syntax_tree(&source);
    let lower_result = lower(FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &lower_result.errors {
            let diagnostic = tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "lowering failed with {} error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result.module.context("lowering produced no module")?;

    // --- Compute metrics ---------------------------------------------------

    let mut var_count = 0usize;
    let mut const_count = 0usize;
    let mut op_count = 0usize;
    let mut total_expr_nodes = 0usize;
    let mut max_nesting = 0usize;
    let mut max_params = 0usize;
    let mut quantifier_count = 0usize;
    let mut prime_count = 0usize;

    let mut per_op: Vec<OpMetric> = Vec::new();

    for unit in &module.units {
        match &unit.node {
            Unit::Variable(decls) => var_count += decls.len(),
            Unit::Constant(decls) => const_count += decls.len(),
            Unit::Operator(def) => {
                op_count += 1;
                let param_count = def.params.len();
                if param_count > max_params {
                    max_params = param_count;
                }

                let mut nodes = 0;
                let mut depth = 0;
                let mut quants = 0;
                let mut primes = 0;
                count_expr_metrics(
                    &def.body.node,
                    0,
                    &mut nodes,
                    &mut depth,
                    &mut quants,
                    &mut primes,
                );

                total_expr_nodes += nodes;
                if depth > max_nesting {
                    max_nesting = depth;
                }
                quantifier_count += quants;
                prime_count += primes;

                per_op.push(OpMetric {
                    name: def.name.node.clone(),
                    params: param_count,
                    nodes,
                    depth,
                    quantifiers: quants,
                    primes,
                });
            }
            _ => {}
        }
    }

    let source_lines = source.lines().count();
    let avg_op_size = if op_count > 0 {
        total_expr_nodes as f64 / op_count as f64
    } else {
        0.0
    };

    // Sort by node count descending for the "hotspot" report.
    per_op.sort_by(|a, b| b.nodes.cmp(&a.nodes));

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        MetricOutputFormat::Human => {
            println!("metric: {}", file.display());
            println!();
            println!("  Source lines:       {source_lines}");
            println!("  Variables:          {var_count}");
            println!("  Constants:          {const_count}");
            println!("  Operators:          {op_count}");
            println!("  Total expr nodes:   {total_expr_nodes}");
            println!("  Max nesting depth:  {max_nesting}");
            println!("  Max params:         {max_params}");
            println!("  Quantifiers:        {quantifier_count}");
            println!("  Prime expressions:  {prime_count}");
            println!("  Avg op size:        {avg_op_size:.1} nodes");
            println!();

            // Top 10 largest operators.
            let top = per_op.iter().take(10);
            println!("  Largest operators:");
            for (i, om) in top.enumerate() {
                println!(
                    "    [{i}] {} ({} nodes, depth {}, {} quantifiers)",
                    om.name, om.nodes, om.depth, om.quantifiers
                );
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        MetricOutputFormat::Json => {
            let ops_json: Vec<serde_json::Value> = per_op
                .iter()
                .map(|om| {
                    serde_json::json!({
                        "name": om.name,
                        "params": om.params,
                        "nodes": om.nodes,
                        "depth": om.depth,
                        "quantifiers": om.quantifiers,
                        "primes": om.primes,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "metrics": {
                    "source_lines": source_lines,
                    "variables": var_count,
                    "constants": const_count,
                    "operators": op_count,
                    "total_expr_nodes": total_expr_nodes,
                    "max_nesting_depth": max_nesting,
                    "max_params": max_params,
                    "quantifiers": quantifier_count,
                    "primes": prime_count,
                    "avg_op_size": avg_op_size,
                },
                "operators": ops_json,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Internal types
// ---------------------------------------------------------------------------

struct OpMetric {
    name: String,
    params: usize,
    nodes: usize,
    depth: usize,
    quantifiers: usize,
    primes: usize,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn count_expr_metrics(
    expr: &Expr,
    current_depth: usize,
    nodes: &mut usize,
    max_depth: &mut usize,
    quantifiers: &mut usize,
    primes: &mut usize,
) {
    *nodes += 1;
    if current_depth > *max_depth {
        *max_depth = current_depth;
    }

    match expr {
        Expr::Prime(_) => *primes += 1,
        Expr::Forall(_, _) | Expr::Exists(_, _) => *quantifiers += 1,
        _ => {}
    }

    let next = current_depth + 1;
    match expr {
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::Lt(a, b)
        | Expr::Gt(a, b)
        | Expr::Leq(a, b)
        | Expr::Geq(a, b)
        | Expr::In(a, b) => {
            count_expr_metrics(&a.node, next, nodes, max_depth, quantifiers, primes);
            count_expr_metrics(&b.node, next, nodes, max_depth, quantifiers, primes);
        }
        Expr::Not(inner) | Expr::Prime(inner) | Expr::Neg(inner) => {
            count_expr_metrics(&inner.node, next, nodes, max_depth, quantifiers, primes);
        }
        Expr::If(c, t, e) => {
            count_expr_metrics(&c.node, next, nodes, max_depth, quantifiers, primes);
            count_expr_metrics(&t.node, next, nodes, max_depth, quantifiers, primes);
            count_expr_metrics(&e.node, next, nodes, max_depth, quantifiers, primes);
        }
        Expr::Apply(f, args) => {
            count_expr_metrics(&f.node, next, nodes, max_depth, quantifiers, primes);
            for arg in args {
                count_expr_metrics(&arg.node, next, nodes, max_depth, quantifiers, primes);
            }
        }
        _ => {}
    }
}
