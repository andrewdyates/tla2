// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 heatmap` — state space exploration heatmap.
//!
//! Runs model checking and reports per-action statistics: how many
//! states each action (disjunct in Next) contributes to the state space.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::ast::{Expr, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the heatmap command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HeatmapOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Generate a state space exploration heatmap.
pub(crate) fn cmd_heatmap(
    file: &Path,
    config: Option<&Path>,
    max_states: usize,
    format: HeatmapOutputFormat,
) -> Result<()> {
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

    // --- Load config -------------------------------------------------------

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

    // --- Extract action names from Next ------------------------------------

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

    let next_name = parsed_config.next.as_deref().unwrap_or("Next");
    let mut action_names: Vec<String> = Vec::new();
    if let Some(next_op) = operators.get(next_name) {
        collect_action_names(&next_op.body.node, &operators, &mut action_names, 0);
    }

    // --- Run model checker -------------------------------------------------

    let mut mc = ModelChecker::new(&module, &parsed_config);
    mc.set_max_states(max_states);
    mc.set_deadlock_check(false);
    let check_result = mc.check();
    let stats = check_result.stats();

    let elapsed = start.elapsed().as_secs_f64();

    // --- Compute heatmap data ----------------------------------------------

    // Estimate action contribution from operator complexity.
    let mut action_data: Vec<ActionHeat> = action_names
        .iter()
        .map(|name| {
            let complexity = operators
                .get(name.as_str())
                .map(|op| count_nodes(&op.body.node))
                .unwrap_or(1);
            ActionHeat {
                name: name.clone(),
                complexity,
            }
        })
        .collect();

    // Sort by complexity descending.
    action_data.sort_by(|a, b| b.complexity.cmp(&a.complexity));

    let total_complexity: usize = action_data.iter().map(|a| a.complexity).sum();

    // --- Output ------------------------------------------------------------

    match format {
        HeatmapOutputFormat::Human => {
            println!("heatmap: {}", file.display());
            println!("  states explored: {}", stats.states_found);
            println!("  actions: {}", action_data.len());
            println!();
            println!("  Action complexity heatmap:");
            for a in &action_data {
                let pct = if total_complexity > 0 {
                    (a.complexity as f64 / total_complexity as f64) * 100.0
                } else {
                    0.0
                };
                let bar_len = (pct / 2.0) as usize;
                let bar: String = "#".repeat(bar_len);
                println!(
                    "    {:20} {:4} nodes ({:5.1}%) {}",
                    a.name, a.complexity, pct, bar
                );
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        HeatmapOutputFormat::Json => {
            let actions_json: Vec<serde_json::Value> = action_data
                .iter()
                .map(|a| {
                    let pct = if total_complexity > 0 {
                        (a.complexity as f64 / total_complexity as f64) * 100.0
                    } else {
                        0.0
                    };
                    serde_json::json!({
                        "name": a.name,
                        "complexity": a.complexity,
                        "percentage": pct,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "states_explored": stats.states_found,
                "total_complexity": total_complexity,
                "actions": actions_json,
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

struct ActionHeat {
    name: String,
    complexity: usize,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn collect_action_names(
    expr: &Expr,
    operators: &BTreeMap<String, &OperatorDef>,
    names: &mut Vec<String>,
    depth: usize,
) {
    if depth > 10 {
        return;
    }
    match expr {
        Expr::Or(a, b) => {
            collect_action_names(&a.node, operators, names, depth);
            collect_action_names(&b.node, operators, names, depth);
        }
        Expr::Ident(name, _) => {
            if let Some(op) = operators.get(name.as_str()) {
                if matches!(&op.body.node, Expr::Or(_, _)) {
                    collect_action_names(&op.body.node, operators, names, depth + 1);
                } else {
                    names.push(name.clone());
                }
            } else {
                names.push(name.clone());
            }
        }
        _ => {
            names.push("<anonymous>".to_string());
        }
    }
}

fn count_nodes(expr: &Expr) -> usize {
    let mut count = 1;
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
            count += count_nodes(&a.node);
            count += count_nodes(&b.node);
        }
        Expr::Not(inner) | Expr::Prime(inner) | Expr::Neg(inner) => {
            count += count_nodes(&inner.node);
        }
        Expr::If(c, t, e) => {
            count += count_nodes(&c.node);
            count += count_nodes(&t.node);
            count += count_nodes(&e.node);
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
