// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 alphabet` — action alphabet extraction.
//!
//! Extracts the complete set of distinct actions from the Next-state
//! relation, including parameterized actions, and reports action
//! signatures.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::Config;
use tla_core::ast::{Expr, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the alphabet command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AlphabetOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Extract the action alphabet from a TLA+ spec.
pub(crate) fn cmd_alphabet(
    file: &Path,
    config: Option<&Path>,
    format: AlphabetOutputFormat,
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

    // --- Extract actions from Next -----------------------------------------

    let next_name = parsed_config.next.as_deref().unwrap_or("Next");
    let mut actions: Vec<ActionEntry> = Vec::new();

    if let Some(next_op) = operators.get(next_name) {
        extract_actions(&next_op.body.node, &operators, &mut actions, 0);
    }

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        AlphabetOutputFormat::Human => {
            println!("alphabet: {}", file.display());
            println!("  actions: {}", actions.len());
            println!();
            for (i, action) in actions.iter().enumerate() {
                if action.params == 0 {
                    println!("    [{i}] {}", action.name);
                } else {
                    println!("    [{i}] {}({} params)", action.name, action.params);
                }
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        AlphabetOutputFormat::Json => {
            let actions_json: Vec<serde_json::Value> = actions
                .iter()
                .map(|a| {
                    serde_json::json!({
                        "name": a.name,
                        "params": a.params,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "action_count": actions.len(),
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

struct ActionEntry {
    name: String,
    params: usize,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn extract_actions(
    expr: &Expr,
    operators: &BTreeMap<String, &OperatorDef>,
    actions: &mut Vec<ActionEntry>,
    depth: usize,
) {
    if depth > 10 {
        return;
    }
    match expr {
        Expr::Or(a, b) => {
            extract_actions(&a.node, operators, actions, depth);
            extract_actions(&b.node, operators, actions, depth);
        }
        Expr::Ident(name, _) => {
            if let Some(op) = operators.get(name.as_str()) {
                if matches!(&op.body.node, Expr::Or(_, _)) {
                    extract_actions(&op.body.node, operators, actions, depth + 1);
                } else {
                    actions.push(ActionEntry {
                        name: name.clone(),
                        params: op.params.len(),
                    });
                }
            } else {
                actions.push(ActionEntry {
                    name: name.clone(),
                    params: 0,
                });
            }
        }
        Expr::Apply(f, args) => {
            if let Expr::Ident(name, _) = &f.node {
                actions.push(ActionEntry {
                    name: name.clone(),
                    params: args.len(),
                });
            }
        }
        Expr::Exists(_, body) => {
            extract_actions(&body.node, operators, actions, depth + 1);
        }
        _ => {
            actions.push(ActionEntry {
                name: "<anonymous>".to_string(),
                params: 0,
            });
        }
    }
}
