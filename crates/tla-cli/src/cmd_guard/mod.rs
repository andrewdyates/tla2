// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 guard` — extract enabling conditions (guards) from actions.
//!
//! Analyzes each action in the Next-state relation to identify the
//! enabling condition (guard) — the unprimed conjuncts that must
//! hold for the action to fire.

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

/// Output format for the guard command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GuardOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Extract guards from actions in a TLA+ spec.
pub(crate) fn cmd_guard(
    file: &Path,
    config: Option<&Path>,
    format: GuardOutputFormat,
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

    let next_name = parsed_config.next.as_deref().unwrap_or("Next");
    let mut guards: Vec<ActionGuard> = Vec::new();

    if let Some(next_op) = operators.get(next_name) {
        extract_guards(&next_op.body.node, &operators, &mut guards, 0);
    }

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        GuardOutputFormat::Human => {
            println!("guard: {}", file.display());
            println!("  actions: {}", guards.len());
            println!();
            for g in &guards {
                println!("  {} :", g.action);
                if g.guard_conjuncts.is_empty() {
                    println!("    guard: TRUE (always enabled)");
                } else {
                    for (i, conj) in g.guard_conjuncts.iter().enumerate() {
                        if i == 0 {
                            println!("    guard: {conj}");
                        } else {
                            println!("       /\\ {conj}");
                        }
                    }
                }
                println!();
            }
            println!("  elapsed: {elapsed:.2}s");
        }
        GuardOutputFormat::Json => {
            let guards_json: Vec<serde_json::Value> = guards
                .iter()
                .map(|g| {
                    serde_json::json!({
                        "action": g.action,
                        "guard_conjuncts": g.guard_conjuncts,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "guards": guards_json,
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

struct ActionGuard {
    action: String,
    guard_conjuncts: Vec<String>,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn extract_guards(
    expr: &Expr,
    operators: &BTreeMap<String, &OperatorDef>,
    guards: &mut Vec<ActionGuard>,
    depth: usize,
) {
    if depth > 10 {
        return;
    }
    match expr {
        Expr::Or(a, b) => {
            extract_guards(&a.node, operators, guards, depth);
            extract_guards(&b.node, operators, guards, depth);
        }
        Expr::Ident(name, _) => {
            if let Some(op) = operators.get(name.as_str()) {
                if matches!(&op.body.node, Expr::Or(_, _)) {
                    extract_guards(&op.body.node, operators, guards, depth + 1);
                } else {
                    let conjuncts = extract_unprimed_conjuncts(&op.body.node);
                    guards.push(ActionGuard {
                        action: name.clone(),
                        guard_conjuncts: conjuncts,
                    });
                }
            }
        }
        _ => {
            let conjuncts = extract_unprimed_conjuncts(expr);
            guards.push(ActionGuard {
                action: "<anonymous>".to_string(),
                guard_conjuncts: conjuncts,
            });
        }
    }
}

/// Extract unprimed conjuncts as guard conditions.
fn extract_unprimed_conjuncts(expr: &Expr) -> Vec<String> {
    let mut conjuncts = Vec::new();
    collect_conjuncts(expr, &mut conjuncts);
    // Filter to only unprimed conditions.
    conjuncts
        .into_iter()
        .filter(|c| !c.contains("'"))
        .collect()
}

fn collect_conjuncts(expr: &Expr, conjuncts: &mut Vec<String>) {
    match expr {
        Expr::And(a, b) => {
            collect_conjuncts(&a.node, conjuncts);
            collect_conjuncts(&b.node, conjuncts);
        }
        _ => {
            let text = pretty_expr(expr);
            let truncated = if text.len() > 80 {
                format!("{}...", &text[..77])
            } else {
                text
            };
            conjuncts.push(truncated);
        }
    }
}
