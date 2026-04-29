// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 invariantgen` — automatic invariant candidate generation.
//!
//! Analyzes a TLA+ specification to generate invariant candidates
//! based on variable types, Init constraints, domain ranges, and
//! common patterns.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the invariantgen command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InvariantgenOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Generate invariant candidates for a TLA+ spec.
pub(crate) fn cmd_invariantgen(file: &Path, format: InvariantgenOutputFormat) -> Result<()> {
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

    // --- Extract spec info -------------------------------------------------

    let mut var_names: Vec<String> = Vec::new();
    let mut operators: BTreeMap<String, &OperatorDef> = BTreeMap::new();

    for unit in &module.units {
        match &unit.node {
            Unit::Variable(decls) => {
                for d in decls {
                    var_names.push(d.node.clone());
                }
            }
            Unit::Operator(def) => {
                operators.insert(def.name.node.clone(), def);
            }
            _ => {}
        }
    }

    // --- Generate candidates from Init -------------------------------------

    let mut candidates: Vec<InvariantCandidate> = Vec::new();

    if let Some(init_op) = operators.get("Init") {
        let memberships = extract_memberships(&init_op.body.node);
        for (var, domain) in &memberships {
            let domain_text = pretty_expr(domain);
            candidates.push(InvariantCandidate {
                expression: format!("{var} \\in {domain_text}"),
                source: "Init membership".to_string(),
                confidence: "high".to_string(),
            });
        }
    }

    // --- Generate type invariant from variable analysis ---------------------

    if var_names.len() >= 2 {
        // Suggest a TypeOK that checks all variables are in their initial domains.
        if !candidates.is_empty() {
            let type_inv_parts: Vec<String> = candidates
                .iter()
                .filter(|c| c.source == "Init membership")
                .map(|c| c.expression.clone())
                .collect();
            if type_inv_parts.len() >= 2 {
                candidates.push(InvariantCandidate {
                    expression: type_inv_parts.join(" /\\ "),
                    source: "TypeOK (combined Init domains)".to_string(),
                    confidence: "high".to_string(),
                });
            }
        }
    }

    // --- Generate mutual exclusion candidates ------------------------------

    // If there are variables that look like process states, suggest exclusion.
    for var in &var_names {
        let lower = var.to_lowercase();
        if lower == "pc" || lower.contains("state") || lower.contains("phase") {
            candidates.push(InvariantCandidate {
                expression: format!(
                    "\\A p1, p2 \\in DOMAIN {var} : p1 /= p2 => ~({var}[p1] = \"critical\" /\\ {var}[p2] = \"critical\")"
                ),
                source: "mutual exclusion pattern".to_string(),
                confidence: "low".to_string(),
            });
            break;
        }
    }

    // --- Generate non-negative candidates for numeric variables ------------

    for var in &var_names {
        let lower = var.to_lowercase();
        if lower.contains("count")
            || lower.contains("num")
            || lower.contains("size")
            || lower.contains("len")
        {
            candidates.push(InvariantCandidate {
                expression: format!("{var} >= 0"),
                source: "numeric non-negativity".to_string(),
                confidence: "medium".to_string(),
            });
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        InvariantgenOutputFormat::Human => {
            println!("invariantgen: {}", file.display());
            println!("  variables: {}", var_names.len());
            println!("  candidates generated: {}", candidates.len());
            println!();
            for (i, c) in candidates.iter().enumerate() {
                println!(
                    "  [{i}] {} (confidence: {}, source: {})",
                    c.expression, c.confidence, c.source
                );
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        InvariantgenOutputFormat::Json => {
            let candidates_json: Vec<serde_json::Value> = candidates
                .iter()
                .map(|c| {
                    serde_json::json!({
                        "expression": c.expression,
                        "source": c.source,
                        "confidence": c.confidence,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "variables": var_names,
                "candidates": candidates_json,
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

struct InvariantCandidate {
    expression: String,
    source: String,
    confidence: String,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn extract_memberships<'a>(expr: &'a Expr) -> BTreeMap<&'a str, &'a Expr> {
    let mut map = BTreeMap::new();
    extract_memberships_inner(expr, &mut map);
    map
}

fn extract_memberships_inner<'a>(expr: &'a Expr, map: &mut BTreeMap<&'a str, &'a Expr>) {
    match expr {
        Expr::And(a, b) => {
            extract_memberships_inner(&a.node, map);
            extract_memberships_inner(&b.node, map);
        }
        Expr::In(lhs, rhs) => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &lhs.node {
                map.insert(name.as_str(), &rhs.node);
            }
        }
        _ => {}
    }
}
