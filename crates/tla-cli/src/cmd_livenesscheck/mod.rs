// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 liveness-check` — focused liveness property analysis.
//!
//! Analyzes temporal properties defined in the configuration without
//! full model checking. Reports fairness constraints, leads-to
//! properties, and eventual consistency patterns.

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

/// Output format for the liveness-check command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LivenesscheckOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Analyze liveness properties in a TLA+ spec.
pub(crate) fn cmd_livenesscheck(
    file: &Path,
    config: Option<&Path>,
    format: LivenesscheckOutputFormat,
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

    // --- Extract liveness info ---------------------------------------------

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

    let config_properties: Vec<String> = parsed_config.properties.clone();

    let mut property_analyses: Vec<PropertyAnalysis> = Vec::new();

    for prop_name in &config_properties {
        if let Some(op) = operators.get(prop_name.as_str()) {
            let body_text = pretty_expr(&op.body.node);
            let kind = classify_temporal_property(&body_text);
            property_analyses.push(PropertyAnalysis {
                name: prop_name.clone(),
                kind,
                body: truncate(&body_text, 100),
            });
        } else {
            property_analyses.push(PropertyAnalysis {
                name: prop_name.clone(),
                kind: "unknown".to_string(),
                body: "(not found in spec)".to_string(),
            });
        }
    }

    // Detect fairness from Spec operator.
    let mut fairness_info: Vec<String> = Vec::new();
    if let Some(spec_op) = operators.get("Spec") {
        let spec_text = pretty_expr(&spec_op.body.node);
        if spec_text.contains("WF_") {
            fairness_info.push("weak fairness (WF)".to_string());
        }
        if spec_text.contains("SF_") {
            fairness_info.push("strong fairness (SF)".to_string());
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        LivenesscheckOutputFormat::Human => {
            println!("liveness-check: {}", file.display());
            println!("  temporal properties: {}", config_properties.len());
            let fairness_display = if fairness_info.is_empty() { "none".to_string() } else { fairness_info.join(", ") };
            println!("  fairness: {fairness_display}");
            println!();
            if property_analyses.is_empty() {
                println!("  No temporal properties configured.");
            } else {
                println!("  Property analysis:");
                for pa in &property_analyses {
                    println!("    {} ({})", pa.name, pa.kind);
                    println!("      {}", pa.body);
                }
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        LivenesscheckOutputFormat::Json => {
            let props_json: Vec<serde_json::Value> = property_analyses
                .iter()
                .map(|pa| {
                    serde_json::json!({
                        "name": pa.name,
                        "kind": pa.kind,
                        "body": pa.body,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "properties": props_json,
                "fairness": fairness_info,
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

struct PropertyAnalysis {
    name: String,
    kind: String,
    body: String,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn classify_temporal_property(text: &str) -> String {
    if text.contains("~>") || text.contains("LeadsTo") {
        "leads_to".to_string()
    } else if text.contains("[]<>") || text.contains("Always Eventually") {
        "recurrence".to_string()
    } else if text.contains("<>[]") || text.contains("Eventually Always") {
        "stability".to_string()
    } else if text.contains("WF_") || text.contains("SF_") {
        "fairness".to_string()
    } else if text.contains("[]") || text.contains("Always") {
        "safety_temporal".to_string()
    } else if text.contains("<>") || text.contains("Eventually") {
        "reachability".to_string()
    } else {
        "general_temporal".to_string()
    }
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() > max {
        format!("{}...", &s[..max.saturating_sub(3)])
    } else {
        s.to_string()
    }
}
