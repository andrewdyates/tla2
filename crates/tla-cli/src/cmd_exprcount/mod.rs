// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 expr-count` — count expression nodes by type.
//!
//! Walks the AST and counts how many nodes of each expression
//! type appear, providing a structural complexity profile.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the expr-count command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ExprcountOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Count expression nodes by type.
pub(crate) fn cmd_exprcount(
    file: &Path,
    format: ExprcountOutputFormat,
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

    let mut counts: BTreeMap<String, usize> = BTreeMap::new();

    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            count_exprs(&def.body.node, &mut counts);
        }
    }

    let total: usize = counts.values().sum();

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        ExprcountOutputFormat::Human => {
            println!("expr-count: {}", file.display());
            println!("  total nodes: {total}");
            println!();
            let mut sorted: Vec<_> = counts.iter().collect();
            sorted.sort_by(|a, b| b.1.cmp(a.1));
            for (kind, count) in &sorted {
                let pct = (**count as f64 / total as f64) * 100.0;
                println!("  {kind:20} {count:6} ({pct:.1}%)");
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        ExprcountOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "total_nodes": total,
                "counts": counts,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn expr_kind(expr: &Expr) -> &'static str {
    match expr {
        Expr::Ident(_, _) => "Ident",
        Expr::StateVar(_, _, _) => "StateVar",
        Expr::Int(_) => "Int",
        Expr::String(_) => "String",
        Expr::Bool(_) => "Bool",
        Expr::And(_, _) => "And",
        Expr::Or(_, _) => "Or",
        Expr::Not(_) => "Not",
        Expr::Eq(_, _) => "Eq",
        Expr::Neq(_, _) => "Neq",
        Expr::Lt(_, _) => "Lt",
        Expr::Gt(_, _) => "Gt",
        Expr::Leq(_, _) => "Leq",
        Expr::Geq(_, _) => "Geq",
        Expr::In(_, _) => "In",
        Expr::NotIn(_, _) => "NotIn",
        Expr::Add(_, _) => "Add",
        Expr::Sub(_, _) => "Sub",
        Expr::Div(_, _) => "Div",
        Expr::Mod(_, _) => "Mod",
        Expr::Neg(_) => "Neg",
        Expr::Prime(_) => "Prime",
        Expr::If(_, _, _) => "If",
        Expr::SetEnum(_) => "SetEnum",
        Expr::Range(_, _) => "Range",
        Expr::Apply(_, _) => "Apply",
        Expr::Forall(_, _) => "Forall",
        Expr::Exists(_, _) => "Exists",
        Expr::Implies(_, _) => "Implies",
        Expr::Times(_) => "Times",
        _ => "Other",
    }
}

fn count_exprs(expr: &Expr, counts: &mut BTreeMap<String, usize>) {
    *counts.entry(expr_kind(expr).to_string()).or_insert(0) += 1;

    match expr {
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Eq(a, b) | Expr::Neq(a, b)
        | Expr::Lt(a, b) | Expr::Gt(a, b) | Expr::Leq(a, b) | Expr::Geq(a, b)
        | Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Div(a, b)
        | Expr::Mod(a, b) | Expr::Range(a, b) | Expr::In(a, b) | Expr::NotIn(a, b)
        | Expr::Implies(a, b) | Expr::Subseteq(a, b) => {
            count_exprs(&a.node, counts);
            count_exprs(&b.node, counts);
        }
        Expr::Not(inner) | Expr::Neg(inner) | Expr::Prime(inner) => {
            count_exprs(&inner.node, counts);
        }
        Expr::If(c, t, e) => {
            count_exprs(&c.node, counts);
            count_exprs(&t.node, counts);
            count_exprs(&e.node, counts);
        }
        Expr::SetEnum(elems) | Expr::Times(elems) => {
            for e in elems {
                count_exprs(&e.node, counts);
            }
        }
        Expr::Apply(f, args) => {
            count_exprs(&f.node, counts);
            for a in args {
                count_exprs(&a.node, counts);
            }
        }
        Expr::Forall(_, body) | Expr::Exists(_, body) => {
            count_exprs(&body.node, counts);
        }
        _ => {}
    }
}
