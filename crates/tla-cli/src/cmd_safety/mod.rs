// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 safety` — safety property analysis.
//!
//! Analyzes a TLA+ specification's safety properties: which invariants
//! are defined, what they protect against, and their relationship to
//! the state transitions.

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

/// Output format for the safety command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SafetyOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Analyze safety properties in a TLA+ spec.
pub(crate) fn cmd_safety(
    file: &Path,
    config: Option<&Path>,
    format: SafetyOutputFormat,
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

    // --- Extract safety info -----------------------------------------------

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

    // Configured invariants.
    let config_invariants: Vec<String> = parsed_config.invariants.clone();

    // Analyze each invariant.
    let mut invariant_analyses: Vec<InvariantAnalysis> = Vec::new();

    for inv_name in &config_invariants {
        if let Some(op) = operators.get(inv_name.as_str()) {
            let body_text = pretty_expr(&op.body.node);
            let kind = classify_invariant(&op.body.node);
            let referenced_vars = count_referenced_vars(&op.body.node);
            invariant_analyses.push(InvariantAnalysis {
                name: inv_name.clone(),
                kind,
                body: truncate(&body_text, 80),
                referenced_vars,
            });
        } else {
            invariant_analyses.push(InvariantAnalysis {
                name: inv_name.clone(),
                kind: "unknown".to_string(),
                body: "(not found in spec)".to_string(),
                referenced_vars: 0,
            });
        }
    }

    // Detect additional invariant candidates from the spec.
    let mut additional_candidates: Vec<String> = Vec::new();
    for (name, _op) in &operators {
        if !config_invariants.contains(name) {
            let lower = name.to_lowercase();
            if lower.contains("inv") || lower.contains("safe") || lower == "typeok" {
                additional_candidates.push(name.clone());
            }
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        SafetyOutputFormat::Human => {
            println!("safety: {}", file.display());
            println!("  configured invariants: {}", config_invariants.len());
            println!();
            if invariant_analyses.is_empty() {
                println!("  No invariants configured.");
            } else {
                println!("  Invariant analysis:");
                for ia in &invariant_analyses {
                    println!("    {} ({})", ia.name, ia.kind);
                    println!("      body: {}", ia.body);
                    println!("      references {} variable(s)", ia.referenced_vars);
                }
            }
            if !additional_candidates.is_empty() {
                println!();
                println!("  Additional invariant candidates (not in config): {}", additional_candidates.join(", "));
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        SafetyOutputFormat::Json => {
            let analyses_json: Vec<serde_json::Value> = invariant_analyses
                .iter()
                .map(|ia| {
                    serde_json::json!({
                        "name": ia.name,
                        "kind": ia.kind,
                        "body": ia.body,
                        "referenced_vars": ia.referenced_vars,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "invariants": analyses_json,
                "additional_candidates": additional_candidates,
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

struct InvariantAnalysis {
    name: String,
    kind: String,
    body: String,
    referenced_vars: usize,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn classify_invariant(expr: &Expr) -> String {
    // Simple heuristic classification.
    let text = pretty_expr(expr);
    if text.contains("\\in") {
        "type_invariant".to_string()
    } else if text.contains("/=") || text.contains("#") {
        "exclusion_invariant".to_string()
    } else if text.contains(">=") || text.contains("<=") || text.contains(">") || text.contains("<") {
        "bound_invariant".to_string()
    } else if text.contains("=>") || text.contains("~") {
        "implication_invariant".to_string()
    } else {
        "general".to_string()
    }
}

fn count_referenced_vars(expr: &Expr) -> usize {
    let mut vars = std::collections::BTreeSet::new();
    collect_var_refs(expr, &mut vars);
    vars.len()
}

fn collect_var_refs(expr: &Expr, vars: &mut std::collections::BTreeSet<String>) {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            vars.insert(name.clone());
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b)
        | Expr::Eq(a, b) | Expr::Neq(a, b) | Expr::Lt(a, b) | Expr::Gt(a, b)
        | Expr::Leq(a, b) | Expr::Geq(a, b) | Expr::In(a, b) => {
            collect_var_refs(&a.node, vars);
            collect_var_refs(&b.node, vars);
        }
        Expr::Not(inner) | Expr::Prime(inner) | Expr::Neg(inner) => {
            collect_var_refs(&inner.node, vars);
        }
        Expr::If(c, t, e) => {
            collect_var_refs(&c.node, vars);
            collect_var_refs(&t.node, vars);
            collect_var_refs(&e.node, vars);
        }
        Expr::Apply(f, args) => {
            collect_var_refs(&f.node, vars);
            for arg in args {
                collect_var_refs(&arg.node, vars);
            }
        }
        _ => {}
    }
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() > max {
        format!("{}...", &s[..max.saturating_sub(3)])
    } else {
        s.to_string()
    }
}
