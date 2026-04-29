// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 stutter` — stuttering and UNCHANGED analysis.
//!
//! Analyzes a TLA+ specification's Next-state relation to detect
//! which variables are changed by each action, identify stuttering
//! steps, and report UNCHANGED coverage.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::Config;
use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the stutter command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StutterOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Analyze stuttering and UNCHANGED patterns in a TLA+ spec.
pub(crate) fn cmd_stutter(
    file: &Path,
    config: Option<&Path>,
    format: StutterOutputFormat,
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

    // --- Extract info ------------------------------------------------------

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

    // --- Analyze each action for primed variables --------------------------

    let next_name = parsed_config.next.as_deref().unwrap_or("Next");
    let mut actions: Vec<ActionChanges> = Vec::new();

    if let Some(next_op) = operators.get(next_name) {
        extract_action_changes(&next_op.body.node, &operators, &var_names, &mut actions, 0);
    }

    // Compute which variables are never primed across all actions.
    let all_primed: BTreeSet<String> = actions
        .iter()
        .flat_map(|a| a.primed_vars.iter().cloned())
        .collect();
    let never_primed: Vec<String> = var_names
        .iter()
        .filter(|v| !all_primed.contains(v.as_str()))
        .cloned()
        .collect();

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        StutterOutputFormat::Human => {
            println!("stutter: {}", file.display());
            println!("  variables: {}", var_names.join(", "));
            println!();
            println!("  Actions ({}):", actions.len());
            for action in &actions {
                let primed_str = if action.primed_vars.is_empty() {
                    "(none — stuttering step)".to_string()
                } else {
                    action
                        .primed_vars
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>()
                        .join(", ")
                };
                let unchanged_str = if action.unchanged_vars.is_empty() {
                    String::new()
                } else {
                    format!(
                        " | UNCHANGED: {}",
                        action
                            .unchanged_vars
                            .iter()
                            .cloned()
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                println!(
                    "    {} — primed: {}{}",
                    action.name, primed_str, unchanged_str
                );
            }
            if !never_primed.is_empty() {
                println!();
                println!(
                    "  WARNING: Variables never primed in any action: {}",
                    never_primed.join(", ")
                );
                println!("  These variables can never change — possible spec bug.");
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        StutterOutputFormat::Json => {
            let actions_json: Vec<serde_json::Value> = actions
                .iter()
                .map(|a| {
                    serde_json::json!({
                        "name": a.name,
                        "primed_vars": a.primed_vars.iter().cloned().collect::<Vec<_>>(),
                        "unchanged_vars": a.unchanged_vars.iter().cloned().collect::<Vec<_>>(),
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "variables": var_names,
                "actions": actions_json,
                "never_primed": never_primed,
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

struct ActionChanges {
    name: String,
    primed_vars: BTreeSet<String>,
    unchanged_vars: BTreeSet<String>,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn extract_action_changes(
    expr: &Expr,
    operators: &BTreeMap<String, &OperatorDef>,
    var_names: &[String],
    actions: &mut Vec<ActionChanges>,
    depth: usize,
) {
    if depth > 10 {
        return;
    }
    match expr {
        Expr::Or(a, b) => {
            extract_action_changes(&a.node, operators, var_names, actions, depth);
            extract_action_changes(&b.node, operators, var_names, actions, depth);
        }
        Expr::Ident(name, _) => {
            if let Some(op) = operators.get(name.as_str()) {
                if matches!(&op.body.node, Expr::Or(_, _)) {
                    extract_action_changes(&op.body.node, operators, var_names, actions, depth + 1);
                } else {
                    let mut primed = BTreeSet::new();
                    let mut unchanged = BTreeSet::new();
                    collect_primed_vars(&op.body.node, operators, &mut primed, &mut unchanged, 0);
                    actions.push(ActionChanges {
                        name: name.clone(),
                        primed_vars: primed,
                        unchanged_vars: unchanged,
                    });
                }
            } else {
                actions.push(ActionChanges {
                    name: name.clone(),
                    primed_vars: BTreeSet::new(),
                    unchanged_vars: BTreeSet::new(),
                });
            }
        }
        _ => {
            let mut primed = BTreeSet::new();
            let mut unchanged = BTreeSet::new();
            collect_primed_vars(expr, operators, &mut primed, &mut unchanged, 0);
            actions.push(ActionChanges {
                name: "<anonymous>".to_string(),
                primed_vars: primed,
                unchanged_vars: unchanged,
            });
        }
    }
}

fn collect_primed_vars(
    expr: &Expr,
    operators: &BTreeMap<String, &OperatorDef>,
    primed: &mut BTreeSet<String>,
    unchanged: &mut BTreeSet<String>,
    depth: usize,
) {
    if depth > 20 {
        return;
    }
    match expr {
        Expr::Prime(inner) => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &inner.node {
                primed.insert(name.clone());
            }
        }
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b)
        | Expr::In(a, b)
        | Expr::Lt(a, b)
        | Expr::Gt(a, b)
        | Expr::Leq(a, b)
        | Expr::Geq(a, b) => {
            collect_primed_vars(&a.node, operators, primed, unchanged, depth + 1);
            collect_primed_vars(&b.node, operators, primed, unchanged, depth + 1);
        }
        Expr::Not(inner) | Expr::Neg(inner) => {
            collect_primed_vars(&inner.node, operators, primed, unchanged, depth + 1);
        }
        Expr::If(c, t, e) => {
            collect_primed_vars(&c.node, operators, primed, unchanged, depth + 1);
            collect_primed_vars(&t.node, operators, primed, unchanged, depth + 1);
            collect_primed_vars(&e.node, operators, primed, unchanged, depth + 1);
        }
        Expr::Apply(f, args) => {
            // Detect UNCHANGED <<var1, var2>>
            if let Expr::Ident(name, _) = &f.node {
                if name == "UNCHANGED" {
                    for arg in args {
                        if let Expr::Ident(v, _) | Expr::StateVar(v, _, _) = &arg.node {
                            unchanged.insert(v.clone());
                        }
                    }
                    return;
                }
                // Recurse into referenced operators.
                if let Some(op) = operators.get(name.as_str()) {
                    collect_primed_vars(&op.body.node, operators, primed, unchanged, depth + 1);
                    return;
                }
            }
            collect_primed_vars(&f.node, operators, primed, unchanged, depth + 1);
            for arg in args {
                collect_primed_vars(&arg.node, operators, primed, unchanged, depth + 1);
            }
        }
        Expr::Ident(name, _) => {
            // If referencing another operator, recurse.
            if let Some(op) = operators.get(name.as_str()) {
                if op.params.is_empty() {
                    collect_primed_vars(&op.body.node, operators, primed, unchanged, depth + 1);
                }
            }
        }
        _ => {}
    }
}
