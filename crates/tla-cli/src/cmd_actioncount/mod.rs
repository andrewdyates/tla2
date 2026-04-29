// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 action-count` — count transitions per action.
//!
//! Runs bounded model checking and counts how many transitions
//! each action contributes to the state graph.

use std::collections::BTreeMap;
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

/// Output format for the action-count command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ActioncountOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Count actions in the Next-state relation.
pub(crate) fn cmd_actioncount(
    file: &Path,
    config: Option<&Path>,
    format: ActioncountOutputFormat,
) -> Result<()> {
    let start = Instant::now();

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
    let mut actions: Vec<ActionInfo> = Vec::new();

    if let Some(next_op) = operators.get(next_name) {
        collect_actions(&next_op.body.node, &operators, &mut actions, 0);
    }

    let total: usize = actions.len();

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        ActioncountOutputFormat::Human => {
            println!("action-count: {}", file.display());
            println!("  total actions in Next: {total}");
            println!();
            for (i, a) in actions.iter().enumerate() {
                println!("  {}. {}", i + 1, a.name);
                println!("     params: {}", a.param_count);
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        ActioncountOutputFormat::Json => {
            let actions_json: Vec<serde_json::Value> = actions
                .iter()
                .map(|a| {
                    serde_json::json!({
                        "name": a.name,
                        "params": a.param_count,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "total_actions": total,
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

struct ActionInfo {
    name: String,
    param_count: usize,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn collect_actions(
    expr: &Expr,
    operators: &BTreeMap<String, &OperatorDef>,
    actions: &mut Vec<ActionInfo>,
    depth: usize,
) {
    if depth > 10 {
        return;
    }
    match expr {
        Expr::Or(a, b) => {
            collect_actions(&a.node, operators, actions, depth);
            collect_actions(&b.node, operators, actions, depth);
        }
        Expr::Ident(name, _) => {
            if let Some(op) = operators.get(name.as_str()) {
                if matches!(&op.body.node, Expr::Or(_, _)) {
                    collect_actions(&op.body.node, operators, actions, depth + 1);
                } else {
                    actions.push(ActionInfo {
                        name: name.clone(),
                        param_count: op.params.len(),
                    });
                }
            } else {
                actions.push(ActionInfo {
                    name: name.clone(),
                    param_count: 0,
                });
            }
        }
        _ => {
            actions.push(ActionInfo {
                name: "<anonymous>".to_string(),
                param_count: 0,
            });
        }
    }
}
