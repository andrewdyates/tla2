// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 quant-count` — count quantifier usage.
//!
//! Counts how many \\A (forall) and \\E (exists) quantifiers
//! appear in each operator.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the quant-count command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum QuantcountOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Count quantifier usage per operator.
pub(crate) fn cmd_quantcount(
    file: &Path,
    format: QuantcountOutputFormat,
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

    let mut total_forall = 0usize;
    let mut total_exists = 0usize;
    let mut ops: Vec<(String, usize, usize)> = Vec::new();

    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            let mut forall = 0;
            let mut exists = 0;
            count_quants(&def.body.node, &mut forall, &mut exists);
            total_forall += forall;
            total_exists += exists;
            if forall > 0 || exists > 0 {
                ops.push((def.name.node.clone(), forall, exists));
            }
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        QuantcountOutputFormat::Human => {
            println!("quant-count: {}", file.display());
            println!("  total \\A (forall): {total_forall}");
            println!("  total \\E (exists): {total_exists}");
            println!("  operators with quantifiers: {}", ops.len());
            println!();
            for (name, fa, ex) in &ops {
                println!("  {name}: \\A={fa} \\E={ex}");
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        QuantcountOutputFormat::Json => {
            let ops_json: Vec<serde_json::Value> = ops
                .iter()
                .map(|(name, fa, ex)| {
                    serde_json::json!({
                        "name": name,
                        "forall": fa,
                        "exists": ex,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "total_forall": total_forall,
                "total_exists": total_exists,
                "operators": ops_json,
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

fn count_quants(expr: &Expr, forall: &mut usize, exists: &mut usize) {
    match expr {
        Expr::Forall(_, body) => {
            *forall += 1;
            count_quants(&body.node, forall, exists);
        }
        Expr::Exists(_, body) => {
            *exists += 1;
            count_quants(&body.node, forall, exists);
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Eq(a, b) | Expr::Neq(a, b)
        | Expr::Lt(a, b) | Expr::Gt(a, b) | Expr::Leq(a, b) | Expr::Geq(a, b)
        | Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Div(a, b)
        | Expr::Mod(a, b) | Expr::Range(a, b) | Expr::In(a, b) | Expr::NotIn(a, b)
        | Expr::Implies(a, b) | Expr::Subseteq(a, b) => {
            count_quants(&a.node, forall, exists);
            count_quants(&b.node, forall, exists);
        }
        Expr::Not(inner) | Expr::Neg(inner) | Expr::Prime(inner) => {
            count_quants(&inner.node, forall, exists);
        }
        Expr::If(c, t, e) => {
            count_quants(&c.node, forall, exists);
            count_quants(&t.node, forall, exists);
            count_quants(&e.node, forall, exists);
        }
        Expr::SetEnum(elems) | Expr::Times(elems) => {
            for e in elems {
                count_quants(&e.node, forall, exists);
            }
        }
        Expr::Apply(f, args) => {
            count_quants(&f.node, forall, exists);
            for a in args {
                count_quants(&a.node, forall, exists);
            }
        }
        _ => {}
    }
}
