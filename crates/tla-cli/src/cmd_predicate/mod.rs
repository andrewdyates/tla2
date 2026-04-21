// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 predicate` — extract and classify predicates.
//!
//! Identifies predicate expressions (boolean-valued operators) in the
//! spec and classifies them by type: state predicate, action predicate,
//! or temporal formula.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the predicate command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PredicateOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Extract and classify predicates from the spec.
pub(crate) fn cmd_predicate(
    file: &Path,
    format: PredicateOutputFormat,
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

    let mut predicates: Vec<PredicateInfo> = Vec::new();

    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            if def.params.is_empty() {
                let kind = classify_predicate(&def.body.node);
                if kind != PredicateKind::NonPredicate {
                    let body_text = pretty_expr(&def.body.node);
                    let truncated = if body_text.len() > 100 {
                        format!("{}...", &body_text[..97])
                    } else {
                        body_text
                    };
                    predicates.push(PredicateInfo {
                        name: def.name.node.clone(),
                        kind,
                        body_preview: truncated,
                    });
                }
            }
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        PredicateOutputFormat::Human => {
            println!("predicate: {}", file.display());
            println!("  predicates found: {}", predicates.len());
            println!();
            for p in &predicates {
                let kind_str = match p.kind {
                    PredicateKind::State => "state",
                    PredicateKind::Action => "action",
                    PredicateKind::Temporal => "temporal",
                    PredicateKind::NonPredicate => "non-predicate",
                };
                println!("  {} [{}]", p.name, kind_str);
                println!("    {}", p.body_preview);
                println!();
            }
            println!("  elapsed: {elapsed:.2}s");
        }
        PredicateOutputFormat::Json => {
            let preds_json: Vec<serde_json::Value> = predicates
                .iter()
                .map(|p| {
                    let kind_str = match p.kind {
                        PredicateKind::State => "state",
                        PredicateKind::Action => "action",
                        PredicateKind::Temporal => "temporal",
                        PredicateKind::NonPredicate => "non-predicate",
                    };
                    serde_json::json!({
                        "name": p.name,
                        "kind": kind_str,
                        "body_preview": p.body_preview,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "predicates": preds_json,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PredicateKind {
    State,
    Action,
    Temporal,
    NonPredicate,
}

struct PredicateInfo {
    name: String,
    kind: PredicateKind,
    body_preview: String,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn classify_predicate(expr: &Expr) -> PredicateKind {
    if has_temporal(expr) {
        PredicateKind::Temporal
    } else if has_prime(expr) {
        PredicateKind::Action
    } else if is_boolean_expr(expr) {
        PredicateKind::State
    } else {
        PredicateKind::NonPredicate
    }
}

fn has_temporal(expr: &Expr) -> bool {
    match expr {
        Expr::Always(_) | Expr::Eventually(_) | Expr::LeadsTo(_, _)
        | Expr::WeakFair(_, _) | Expr::StrongFair(_, _) => true,
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b) => {
            has_temporal(&a.node) || has_temporal(&b.node)
        }
        Expr::Not(inner) => has_temporal(&inner.node),
        _ => false,
    }
}

fn has_prime(expr: &Expr) -> bool {
    match expr {
        Expr::Prime(_) => true,
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Eq(a, b) | Expr::Neq(a, b)
        | Expr::In(a, b) | Expr::NotIn(a, b) | Expr::Implies(a, b) => {
            has_prime(&a.node) || has_prime(&b.node)
        }
        Expr::Not(inner) | Expr::Neg(inner) => has_prime(&inner.node),
        Expr::If(c, t, e) => has_prime(&c.node) || has_prime(&t.node) || has_prime(&e.node),
        _ => false,
    }
}

fn is_boolean_expr(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::And(_, _)
            | Expr::Or(_, _)
            | Expr::Not(_)
            | Expr::Eq(_, _)
            | Expr::Neq(_, _)
            | Expr::Lt(_, _)
            | Expr::Gt(_, _)
            | Expr::Leq(_, _)
            | Expr::Geq(_, _)
            | Expr::In(_, _)
            | Expr::NotIn(_, _)
            | Expr::Implies(_, _)
            | Expr::Forall(_, _)
            | Expr::Exists(_, _)
            | Expr::Bool(_)
    )
}
