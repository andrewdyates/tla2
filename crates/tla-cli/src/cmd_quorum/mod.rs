// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 quorum` — quorum and majority pattern detection.
//!
//! Analyzes a TLA+ specification to detect quorum-related patterns
//! common in distributed systems: Cardinality comparisons, subset
//! counting, majority thresholds, and voting patterns.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the quorum command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum QuorumOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Detect quorum patterns in a TLA+ spec.
pub(crate) fn cmd_quorum(file: &Path, format: QuorumOutputFormat) -> Result<()> {
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

    // --- Scan for quorum patterns ------------------------------------------

    let mut patterns: Vec<QuorumPattern> = Vec::new();

    for (name, op) in &operators {
        scan_quorum_patterns(&op.body.node, name, &mut patterns, 0);
    }

    // Detect quorum-related constants.
    let mut quorum_constants: Vec<String> = Vec::new();
    for unit in &module.units {
        if let Unit::Constant(decls) = &unit.node {
            for decl in decls {
                let lower = decl.name.node.to_lowercase();
                if lower.contains("quorum")
                    || lower.contains("majority")
                    || lower.contains("threshold")
                    || lower.contains("acceptor")
                    || lower.contains("voter")
                {
                    quorum_constants.push(decl.name.node.clone());
                }
            }
        }
    }

    // Detect quorum-related variables.
    let mut quorum_variables: Vec<String> = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(decls) = &unit.node {
            for decl in decls {
                let lower = decl.node.to_lowercase();
                if lower.contains("vote")
                    || lower.contains("ballot")
                    || lower.contains("accept")
                    || lower.contains("quorum")
                    || lower.contains("ack")
                {
                    quorum_variables.push(decl.node.clone());
                }
            }
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        QuorumOutputFormat::Human => {
            println!("quorum: {}", file.display());
            println!();
            if patterns.is_empty() && quorum_constants.is_empty() && quorum_variables.is_empty() {
                println!("  No quorum patterns detected.");
            } else {
                if !quorum_constants.is_empty() {
                    println!(
                        "  Quorum-related constants: {}",
                        quorum_constants.join(", ")
                    );
                }
                if !quorum_variables.is_empty() {
                    println!(
                        "  Quorum-related variables: {}",
                        quorum_variables.join(", ")
                    );
                }
                if !patterns.is_empty() {
                    println!();
                    println!("  Quorum patterns ({}):", patterns.len());
                    for (i, p) in patterns.iter().enumerate() {
                        println!("    [{i}] {} in operator `{}`", p.kind, p.in_operator);
                        println!("        {}", p.description);
                    }
                }
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        QuorumOutputFormat::Json => {
            let patterns_json: Vec<serde_json::Value> = patterns
                .iter()
                .map(|p| {
                    serde_json::json!({
                        "kind": p.kind,
                        "in_operator": p.in_operator,
                        "description": p.description,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "quorum_constants": quorum_constants,
                "quorum_variables": quorum_variables,
                "patterns": patterns_json,
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

struct QuorumPattern {
    kind: String,
    in_operator: String,
    description: String,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn scan_quorum_patterns(
    expr: &Expr,
    op_name: &str,
    patterns: &mut Vec<QuorumPattern>,
    depth: usize,
) {
    if depth > 20 {
        return;
    }
    match expr {
        // Detect Cardinality(S) > N or Cardinality(S) >= N patterns.
        Expr::Gt(a, b) | Expr::Geq(a, b) => {
            if is_cardinality_call(&a.node) {
                let expr_text = pretty_expr(expr);
                let truncated = if expr_text.len() > 80 {
                    format!("{}...", &expr_text[..77])
                } else {
                    expr_text
                };
                patterns.push(QuorumPattern {
                    kind: "cardinality_threshold".to_string(),
                    in_operator: op_name.to_string(),
                    description: truncated,
                });
            }
            scan_quorum_patterns(&a.node, op_name, patterns, depth + 1);
            scan_quorum_patterns(&b.node, op_name, patterns, depth + 1);
        }
        // Detect 2 * Cardinality(S) > Cardinality(T) (majority pattern).
        Expr::Lt(a, b) | Expr::Leq(a, b) => {
            if is_cardinality_call(&b.node) {
                let expr_text = pretty_expr(expr);
                let truncated = if expr_text.len() > 80 {
                    format!("{}...", &expr_text[..77])
                } else {
                    expr_text
                };
                patterns.push(QuorumPattern {
                    kind: "cardinality_threshold".to_string(),
                    in_operator: op_name.to_string(),
                    description: truncated,
                });
            }
            scan_quorum_patterns(&a.node, op_name, patterns, depth + 1);
            scan_quorum_patterns(&b.node, op_name, patterns, depth + 1);
        }
        // Detect \in SUBSET S patterns (subset membership = quorum selection).
        Expr::In(lhs, rhs) => {
            if is_subset_call(&rhs.node) {
                patterns.push(QuorumPattern {
                    kind: "subset_selection".to_string(),
                    in_operator: op_name.to_string(),
                    description: format!("{} \\in SUBSET ...", pretty_expr(&lhs.node)),
                });
            }
            scan_quorum_patterns(&lhs.node, op_name, patterns, depth + 1);
            scan_quorum_patterns(&rhs.node, op_name, patterns, depth + 1);
        }
        // Recurse into binary operators.
        Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Implies(a, b)
        | Expr::Eq(a, b)
        | Expr::Neq(a, b) => {
            scan_quorum_patterns(&a.node, op_name, patterns, depth + 1);
            scan_quorum_patterns(&b.node, op_name, patterns, depth + 1);
        }
        Expr::Not(inner) | Expr::Prime(inner) | Expr::Neg(inner) => {
            scan_quorum_patterns(&inner.node, op_name, patterns, depth + 1);
        }
        Expr::If(c, t, e) => {
            scan_quorum_patterns(&c.node, op_name, patterns, depth + 1);
            scan_quorum_patterns(&t.node, op_name, patterns, depth + 1);
            scan_quorum_patterns(&e.node, op_name, patterns, depth + 1);
        }
        Expr::Apply(f, args) => {
            // Detect Quorum-named function calls.
            if let Expr::Ident(name, _) = &f.node {
                let lower = name.to_lowercase();
                if lower.contains("quorum") || lower.contains("majority") {
                    patterns.push(QuorumPattern {
                        kind: "quorum_operator".to_string(),
                        in_operator: op_name.to_string(),
                        description: format!("calls {name}(...)"),
                    });
                }
            }
            scan_quorum_patterns(&f.node, op_name, patterns, depth + 1);
            for arg in args {
                scan_quorum_patterns(&arg.node, op_name, patterns, depth + 1);
            }
        }
        _ => {}
    }
}

fn is_cardinality_call(expr: &Expr) -> bool {
    if let Expr::Apply(f, _) = expr {
        if let Expr::Ident(name, _) = &f.node {
            return name == "Cardinality";
        }
    }
    false
}

fn is_subset_call(expr: &Expr) -> bool {
    if let Expr::Apply(f, _) = expr {
        if let Expr::Ident(name, _) = &f.node {
            return name == "SUBSET";
        }
    }
    false
}
