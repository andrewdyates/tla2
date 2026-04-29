// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 tableau` — liveness tableau construction display.
//!
//! Analyzes the temporal properties in a specification and displays
//! the tableau structure that would be used for liveness checking.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::Config;
use tla_core::ast::{OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the tableau command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TableauOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Display the liveness tableau for a TLA+ spec.
pub(crate) fn cmd_tableau(
    file: &Path,
    config: Option<&Path>,
    format: TableauOutputFormat,
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

    // --- Build tableau info ------------------------------------------------

    let mut tableau_nodes: Vec<TableauNode> = Vec::new();
    let properties = &parsed_config.properties;

    for prop_name in properties {
        if let Some(op) = operators.get(prop_name.as_str()) {
            let body_text = pretty_expr(&op.body.node);
            let has_fairness = body_text.contains("WF_") || body_text.contains("SF_");
            let has_eventually = body_text.contains("<>") || body_text.contains("Eventually");
            let has_always = body_text.contains("[]") || body_text.contains("Always");

            tableau_nodes.push(TableauNode {
                property: prop_name.clone(),
                formula: truncate(&body_text, 80),
                has_fairness,
                has_eventually,
                has_always,
                tableau_states: if has_eventually { 2 } else { 1 },
            });
        }
    }

    let total_tableau_states: usize = tableau_nodes.iter().map(|n| n.tableau_states).sum();
    let needs_scc = tableau_nodes
        .iter()
        .any(|n| n.has_eventually || n.has_fairness);

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        TableauOutputFormat::Human => {
            println!("tableau: {}", file.display());
            println!("  temporal properties: {}", properties.len());
            println!("  tableau states: {total_tableau_states}");
            println!(
                "  needs SCC detection: {}",
                if needs_scc { "yes" } else { "no" }
            );
            println!();
            for node in &tableau_nodes {
                println!(
                    "  {} ({} tableau states)",
                    node.property, node.tableau_states
                );
                println!("    formula: {}", node.formula);
                println!(
                    "    fairness: {}, eventually: {}, always: {}",
                    node.has_fairness, node.has_eventually, node.has_always
                );
            }
            if tableau_nodes.is_empty() {
                println!("  No temporal properties — no tableau needed.");
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        TableauOutputFormat::Json => {
            let nodes_json: Vec<serde_json::Value> = tableau_nodes
                .iter()
                .map(|n| {
                    serde_json::json!({
                        "property": n.property,
                        "formula": n.formula,
                        "has_fairness": n.has_fairness,
                        "has_eventually": n.has_eventually,
                        "has_always": n.has_always,
                        "tableau_states": n.tableau_states,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "properties_count": properties.len(),
                "total_tableau_states": total_tableau_states,
                "needs_scc": needs_scc,
                "nodes": nodes_json,
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

struct TableauNode {
    property: String,
    formula: String,
    has_fairness: bool,
    has_eventually: bool,
    has_always: bool,
    tableau_states: usize,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn truncate(s: &str, max: usize) -> String {
    if s.len() > max {
        format!("{}...", &s[..max.saturating_sub(3)])
    } else {
        s.to_string()
    }
}
