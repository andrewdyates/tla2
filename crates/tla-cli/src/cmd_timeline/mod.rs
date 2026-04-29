// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 timeline` — temporal behavior timeline analysis.
//!
//! Analyzes a TLA+ specification's temporal properties and action structure
//! to produce a timeline of possible behaviors: which actions can fire in
//! what order, and how temporal properties constrain behavior.

use std::collections::BTreeMap;
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

/// Output format for the timeline command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TimelineOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Run timeline analysis on a TLA+ spec.
pub(crate) fn cmd_timeline(
    file: &Path,
    config: Option<&Path>,
    format: TimelineOutputFormat,
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

    // --- Analyze actions from Next -----------------------------------------

    let next_name = parsed_config.next.as_deref().unwrap_or("Next");
    let mut actions: Vec<ActionInfo> = Vec::new();

    if let Some(next_op) = operators.get(next_name) {
        extract_actions(&next_op.body.node, &operators, &mut actions, 0);
    }

    // --- Analyze temporal properties ---------------------------------------

    let properties: Vec<String> = parsed_config.properties.clone();
    let invariants: Vec<String> = parsed_config.invariants.clone();

    // Detect fairness constraints by looking for WF_/SF_ patterns.
    let mut fairness: Vec<FairnessInfo> = Vec::new();
    for prop_name in &properties {
        if let Some(op) = operators.get(prop_name.as_str()) {
            let prop_text = pretty_expr(&op.body.node);
            if prop_text.contains("WF_") {
                fairness.push(FairnessInfo {
                    kind: "weak".to_string(),
                    property: prop_name.clone(),
                });
            } else if prop_text.contains("SF_") {
                fairness.push(FairnessInfo {
                    kind: "strong".to_string(),
                    property: prop_name.clone(),
                });
            }
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        TimelineOutputFormat::Human => {
            println!("timeline: {}", file.display());
            println!();
            println!("  Actions ({}):", actions.len());
            for (i, action) in actions.iter().enumerate() {
                println!("    [{i}] {}", action.name);
                if !action.summary.is_empty() {
                    println!("        {}", action.summary);
                }
            }
            println!();
            println!("  Temporal properties ({}):", properties.len());
            if properties.is_empty() {
                println!("    (none)");
            }
            for p in &properties {
                println!("    {p}");
            }
            println!();
            println!("  Invariants ({}):", invariants.len());
            if invariants.is_empty() {
                println!("    (none)");
            }
            for inv in &invariants {
                println!("    {inv}");
            }
            if !fairness.is_empty() {
                println!();
                println!("  Fairness constraints ({}):", fairness.len());
                for f in &fairness {
                    println!("    {} fairness: {}", f.kind, f.property);
                }
            }
            println!();
            println!(
                "  Timeline: {} actions, {} properties, {} invariants",
                actions.len(),
                properties.len(),
                invariants.len()
            );
            println!("  elapsed: {elapsed:.2}s");
        }
        TimelineOutputFormat::Json => {
            let actions_json: Vec<serde_json::Value> = actions
                .iter()
                .map(|a| {
                    serde_json::json!({
                        "name": a.name,
                        "summary": a.summary,
                    })
                })
                .collect();
            let fairness_json: Vec<serde_json::Value> = fairness
                .iter()
                .map(|f| {
                    serde_json::json!({
                        "kind": f.kind,
                        "property": f.property,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "actions": actions_json,
                "properties": properties,
                "invariants": invariants,
                "fairness": fairness_json,
                "statistics": {
                    "action_count": actions.len(),
                    "property_count": properties.len(),
                    "invariant_count": invariants.len(),
                    "fairness_count": fairness.len(),
                    "elapsed_seconds": elapsed,
                },
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
    summary: String,
}

struct FairnessInfo {
    kind: String,
    property: String,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn extract_actions(
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
            extract_actions(&a.node, operators, actions, depth);
            extract_actions(&b.node, operators, actions, depth);
        }
        Expr::Ident(name, _) => {
            if let Some(op) = operators.get(name.as_str()) {
                if op.params.is_empty() {
                    // Check if this is a disjunction; if so, recurse
                    if matches!(&op.body.node, Expr::Or(_, _)) {
                        extract_actions(&op.body.node, operators, actions, depth + 1);
                    } else {
                        let summary = pretty_expr(&op.body.node);
                        let truncated = if summary.len() > 60 {
                            format!("{}...", &summary[..57])
                        } else {
                            summary
                        };
                        actions.push(ActionInfo {
                            name: name.clone(),
                            summary: truncated,
                        });
                    }
                } else {
                    actions.push(ActionInfo {
                        name: name.clone(),
                        summary: format!("({} params)", op.params.len()),
                    });
                }
            } else {
                actions.push(ActionInfo {
                    name: name.clone(),
                    summary: String::new(),
                });
            }
        }
        Expr::Apply(f, _args) => {
            if let Expr::Ident(name, _) = &f.node {
                actions.push(ActionInfo {
                    name: name.clone(),
                    summary: "(parameterized)".to_string(),
                });
            }
        }
        _ => {
            let summary = pretty_expr(expr);
            let truncated = if summary.len() > 60 {
                format!("{}...", &summary[..57])
            } else {
                summary
            };
            actions.push(ActionInfo {
                name: "<anonymous>".to_string(),
                summary: truncated,
            });
        }
    }
}
