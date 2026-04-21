// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 weight` — action weight computation for guided search.
//!
//! Computes weights for each action in the Next-state relation based
//! on structural complexity, variable coverage, and branching patterns.
//! These weights can guide search heuristics.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::Config;
use tla_core::ast::{Expr, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the weight command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WeightOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Compute action weights for a TLA+ spec.
pub(crate) fn cmd_weight(
    file: &Path,
    config: Option<&Path>,
    format: WeightOutputFormat,
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

    let config_path_buf = match config {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            cfg
        }
    };

    let parsed_config = if config_path_buf.exists() {
        let cfg_source = std::fs::read_to_string(&config_path_buf)
            .with_context(|| format!("read config {}", config_path_buf.display()))?;
        Config::parse(&cfg_source).map_err(|errors| {
            for err in &errors {
                eprintln!("{}:{}: {}", config_path_buf.display(), err.line(), err);
            }
            anyhow::anyhow!("config parse failed with {} error(s)", errors.len())
        })?
    } else {
        Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        }
    };

    let var_names: Vec<String> = module
        .units
        .iter()
        .filter_map(|u| {
            if let Unit::Variable(decls) = &u.node {
                Some(decls.iter().map(|d| d.node.clone()))
            } else {
                None
            }
        })
        .flatten()
        .collect();

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

    // --- Extract actions and compute weights -------------------------------

    let next_name = parsed_config.next.as_deref().unwrap_or("Next");
    let mut action_weights: Vec<ActionWeight> = Vec::new();

    if let Some(next_op) = operators.get(next_name) {
        collect_action_weights(
            &next_op.body.node,
            &operators,
            &var_names,
            &mut action_weights,
            0,
        );
    }

    // Normalize weights.
    let total: f64 = action_weights.iter().map(|a| a.raw_weight).sum();
    for aw in &mut action_weights {
        aw.normalized = if total > 0.0 {
            aw.raw_weight / total
        } else {
            0.0
        };
    }

    // Sort by weight descending.
    action_weights.sort_by(|a, b| b.raw_weight.partial_cmp(&a.raw_weight).unwrap_or(std::cmp::Ordering::Equal));

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        WeightOutputFormat::Human => {
            println!("weight: {}", file.display());
            println!("  actions: {}", action_weights.len());
            println!();
            for aw in &action_weights {
                println!(
                    "    {:20} weight={:.1}  normalized={:.3}  vars_touched={} nodes={}",
                    aw.name, aw.raw_weight, aw.normalized, aw.vars_touched, aw.node_count
                );
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        WeightOutputFormat::Json => {
            let weights_json: Vec<serde_json::Value> = action_weights
                .iter()
                .map(|aw| {
                    serde_json::json!({
                        "name": aw.name,
                        "raw_weight": aw.raw_weight,
                        "normalized": aw.normalized,
                        "vars_touched": aw.vars_touched,
                        "node_count": aw.node_count,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "total_weight": total,
                "actions": weights_json,
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

struct ActionWeight {
    name: String,
    raw_weight: f64,
    normalized: f64,
    vars_touched: usize,
    node_count: usize,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn collect_action_weights(
    expr: &Expr,
    operators: &BTreeMap<String, &OperatorDef>,
    var_names: &[String],
    weights: &mut Vec<ActionWeight>,
    depth: usize,
) {
    if depth > 10 {
        return;
    }
    match expr {
        Expr::Or(a, b) => {
            collect_action_weights(&a.node, operators, var_names, weights, depth);
            collect_action_weights(&b.node, operators, var_names, weights, depth);
        }
        Expr::Ident(name, _) => {
            if let Some(op) = operators.get(name.as_str()) {
                if matches!(&op.body.node, Expr::Or(_, _)) {
                    collect_action_weights(&op.body.node, operators, var_names, weights, depth + 1);
                } else {
                    let nodes = count_nodes(&op.body.node);
                    let mut primed = BTreeSet::new();
                    collect_primed(&op.body.node, &mut primed);
                    let vars_touched = primed.len();
                    // Weight = nodes * (1 + vars_touched), favoring complex actions that modify many variables.
                    let raw = nodes as f64 * (1.0 + vars_touched as f64);
                    weights.push(ActionWeight {
                        name: name.clone(),
                        raw_weight: raw,
                        normalized: 0.0,
                        vars_touched,
                        node_count: nodes,
                    });
                }
            }
        }
        _ => {}
    }
}

fn count_nodes(expr: &Expr) -> usize {
    let mut count = 1;
    match expr {
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b)
        | Expr::Eq(a, b) | Expr::Neq(a, b) | Expr::Lt(a, b) | Expr::Gt(a, b)
        | Expr::Leq(a, b) | Expr::Geq(a, b) | Expr::In(a, b) => {
            count += count_nodes(&a.node) + count_nodes(&b.node);
        }
        Expr::Not(inner) | Expr::Prime(inner) | Expr::Neg(inner) => {
            count += count_nodes(&inner.node);
        }
        Expr::If(c, t, e) => {
            count += count_nodes(&c.node) + count_nodes(&t.node) + count_nodes(&e.node);
        }
        Expr::Apply(f, args) => {
            count += count_nodes(&f.node);
            for arg in args {
                count += count_nodes(&arg.node);
            }
        }
        _ => {}
    }
    count
}

fn collect_primed(expr: &Expr, primed: &mut BTreeSet<String>) {
    match expr {
        Expr::Prime(inner) => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &inner.node {
                primed.insert(name.clone());
            }
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b)
        | Expr::Eq(a, b) | Expr::Neq(a, b) | Expr::In(a, b)
        | Expr::Lt(a, b) | Expr::Gt(a, b) | Expr::Leq(a, b) | Expr::Geq(a, b) => {
            collect_primed(&a.node, primed);
            collect_primed(&b.node, primed);
        }
        Expr::Not(inner) | Expr::Neg(inner) => {
            collect_primed(&inner.node, primed);
        }
        Expr::If(c, t, e) => {
            collect_primed(&c.node, primed);
            collect_primed(&t.node, primed);
            collect_primed(&e.node, primed);
        }
        Expr::Apply(f, args) => {
            collect_primed(&f.node, primed);
            for arg in args {
                collect_primed(&arg.node, primed);
            }
        }
        _ => {}
    }
}
