// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 ast-depth` — compute maximum AST depth.
//!
//! Walks the AST and computes the maximum nesting depth for each
//! operator, useful for identifying deeply nested expressions.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the ast-depth command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AstdepthOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Compute maximum AST depth per operator.
pub(crate) fn cmd_astdepth(
    file: &Path,
    format: AstdepthOutputFormat,
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

    let mut ops: Vec<(String, usize)> = Vec::new();
    let mut max_overall = 0usize;

    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            let depth = ast_depth(&def.body.node, 0);
            if depth > max_overall {
                max_overall = depth;
            }
            ops.push((def.name.node.clone(), depth));
        }
    }

    ops.sort_by(|a, b| b.1.cmp(&a.1));

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        AstdepthOutputFormat::Human => {
            println!("ast-depth: {}", file.display());
            println!("  max depth: {max_overall}");
            println!("  operators: {}", ops.len());
            println!();
            for (name, depth) in &ops {
                println!("  {depth:3}  {name}");
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        AstdepthOutputFormat::Json => {
            let ops_json: Vec<serde_json::Value> = ops
                .iter()
                .map(|(name, depth)| {
                    serde_json::json!({
                        "name": name,
                        "depth": depth,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "max_depth": max_overall,
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

fn ast_depth(expr: &Expr, current: usize) -> usize {
    let next = current + 1;
    match expr {
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Eq(a, b) | Expr::Neq(a, b)
        | Expr::Lt(a, b) | Expr::Gt(a, b) | Expr::Leq(a, b) | Expr::Geq(a, b)
        | Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Div(a, b)
        | Expr::Mod(a, b) | Expr::Range(a, b) | Expr::In(a, b) | Expr::NotIn(a, b)
        | Expr::Implies(a, b) | Expr::Subseteq(a, b) => {
            let da = ast_depth(&a.node, next);
            let db = ast_depth(&b.node, next);
            da.max(db)
        }
        Expr::Not(inner) | Expr::Neg(inner) | Expr::Prime(inner) => {
            ast_depth(&inner.node, next)
        }
        Expr::If(c, t, e) => {
            let dc = ast_depth(&c.node, next);
            let dt = ast_depth(&t.node, next);
            let de = ast_depth(&e.node, next);
            dc.max(dt).max(de)
        }
        Expr::SetEnum(elems) | Expr::Times(elems) => {
            elems.iter().map(|e| ast_depth(&e.node, next)).max().unwrap_or(next)
        }
        Expr::Apply(f, args) => {
            let df = ast_depth(&f.node, next);
            let da = args.iter().map(|a| ast_depth(&a.node, next)).max().unwrap_or(next);
            df.max(da)
        }
        Expr::Forall(_, body) | Expr::Exists(_, body) => {
            ast_depth(&body.node, next)
        }
        _ => next,
    }
}
