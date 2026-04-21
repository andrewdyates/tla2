// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 set-ops` — count set operation usage.
//!
//! Counts how many times various set operations (\\in, \\union,
//! \\subseteq, SUBSET, etc.) appear in the spec.

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

/// Output format for the set-ops command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SetopsOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Count set operation usage.
pub(crate) fn cmd_setops(
    file: &Path,
    format: SetopsOutputFormat,
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

    let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();

    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            count_set_ops(&def.body.node, &mut counts);
        }
    }

    let total: usize = counts.values().sum();

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        SetopsOutputFormat::Human => {
            println!("set-ops: {}", file.display());
            println!("  total set operations: {total}");
            println!();
            let mut sorted: Vec<_> = counts.iter().collect();
            sorted.sort_by(|a, b| b.1.cmp(a.1));
            for (op, count) in &sorted {
                println!("  {op:20} {count}");
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        SetopsOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "total": total,
                "operations": counts,
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

fn count_set_ops(expr: &Expr, counts: &mut BTreeMap<&'static str, usize>) {
    match expr {
        Expr::In(a, b) => {
            *counts.entry("\\in").or_insert(0) += 1;
            count_set_ops(&a.node, counts);
            count_set_ops(&b.node, counts);
        }
        Expr::NotIn(a, b) => {
            *counts.entry("\\notin").or_insert(0) += 1;
            count_set_ops(&a.node, counts);
            count_set_ops(&b.node, counts);
        }
        Expr::Subseteq(a, b) => {
            *counts.entry("\\subseteq").or_insert(0) += 1;
            count_set_ops(&a.node, counts);
            count_set_ops(&b.node, counts);
        }
        Expr::SetEnum(elems) => {
            *counts.entry("SetEnum").or_insert(0) += 1;
            for e in elems {
                count_set_ops(&e.node, counts);
            }
        }
        Expr::Range(a, b) => {
            *counts.entry("Range(..)").or_insert(0) += 1;
            count_set_ops(&a.node, counts);
            count_set_ops(&b.node, counts);
        }
        Expr::Times(elems) => {
            *counts.entry("\\X").or_insert(0) += 1;
            for e in elems {
                count_set_ops(&e.node, counts);
            }
        }
        // Recurse through non-set expressions.
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Eq(a, b) | Expr::Neq(a, b)
        | Expr::Lt(a, b) | Expr::Gt(a, b) | Expr::Leq(a, b) | Expr::Geq(a, b)
        | Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Div(a, b)
        | Expr::Mod(a, b) | Expr::Implies(a, b) => {
            count_set_ops(&a.node, counts);
            count_set_ops(&b.node, counts);
        }
        Expr::Not(inner) | Expr::Neg(inner) | Expr::Prime(inner) => {
            count_set_ops(&inner.node, counts);
        }
        Expr::If(c, t, e) => {
            count_set_ops(&c.node, counts);
            count_set_ops(&t.node, counts);
            count_set_ops(&e.node, counts);
        }
        Expr::Apply(f, args) => {
            count_set_ops(&f.node, counts);
            for a in args {
                count_set_ops(&a.node, counts);
            }
        }
        Expr::Forall(_, body) | Expr::Exists(_, body) => {
            count_set_ops(&body.node, counts);
        }
        _ => {}
    }
}
