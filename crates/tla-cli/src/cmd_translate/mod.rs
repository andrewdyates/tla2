// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 translate` — translate spec to pseudocode.
//!
//! Converts a TLA+ specification into a readable pseudocode
//! representation that's closer to PlusCal or traditional
//! programming language syntax.

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

/// Output format for the translate command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TranslateOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Translate a TLA+ spec to pseudocode.
pub(crate) fn cmd_translate(
    file: &Path,
    format: TranslateOutputFormat,
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

    // --- Extract spec structure --------------------------------------------

    let mut var_names: Vec<String> = Vec::new();
    let mut const_names: Vec<String> = Vec::new();
    let mut operators: Vec<(&str, Vec<String>, String)> = Vec::new(); // (name, params, pseudocode)

    for unit in &module.units {
        match &unit.node {
            Unit::Variable(decls) => {
                for d in decls {
                    var_names.push(d.node.clone());
                }
            }
            Unit::Constant(decls) => {
                for d in decls {
                    const_names.push(d.name.node.clone());
                }
            }
            Unit::Operator(def) => {
                let params: Vec<String> = def.params.iter().map(|p| p.name.node.clone()).collect();
                let pseudo = expr_to_pseudo(&def.body.node, 0);
                operators.push((&def.name.node, params, pseudo));
            }
            _ => {}
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    // --- Build pseudocode output -------------------------------------------

    let mut pseudocode = String::new();
    pseudocode.push_str(&format!("// Module: {}\n", module.name.node));
    pseudocode.push('\n');

    if !const_names.is_empty() {
        pseudocode.push_str(&format!("constants: {}\n", const_names.join(", ")));
    }
    if !var_names.is_empty() {
        pseudocode.push_str(&format!("variables: {}\n", var_names.join(", ")));
    }
    pseudocode.push('\n');

    for (name, params, body) in &operators {
        if params.is_empty() {
            pseudocode.push_str(&format!("procedure {name}():\n"));
        } else {
            pseudocode.push_str(&format!("procedure {}({}):\n", name, params.join(", ")));
        }
        for line in body.lines() {
            pseudocode.push_str(&format!("    {line}\n"));
        }
        pseudocode.push('\n');
    }

    // --- Output ------------------------------------------------------------

    match format {
        TranslateOutputFormat::Human => {
            println!("translate: {}", file.display());
            println!();
            print!("{pseudocode}");
            println!("  elapsed: {elapsed:.2}s");
        }
        TranslateOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "module_name": module.name.node,
                "pseudocode": pseudocode,
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

fn expr_to_pseudo(expr: &Expr, indent: usize) -> String {
    let pad = "  ".repeat(indent);
    match expr {
        Expr::And(a, b) => {
            format!("{}\n{}AND\n{}", expr_to_pseudo(&a.node, indent), pad, expr_to_pseudo(&b.node, indent))
        }
        Expr::Or(a, b) => {
            format!("{}\n{}OR\n{}", expr_to_pseudo(&a.node, indent), pad, expr_to_pseudo(&b.node, indent))
        }
        Expr::Implies(a, b) => {
            format!("{}if {} then\n{}", pad, pretty_expr(&a.node), expr_to_pseudo(&b.node, indent + 1))
        }
        Expr::If(c, t, e) => {
            format!(
                "{}if {} then\n{}\n{}else\n{}",
                pad,
                pretty_expr(&c.node),
                expr_to_pseudo(&t.node, indent + 1),
                pad,
                expr_to_pseudo(&e.node, indent + 1)
            )
        }
        Expr::Eq(a, b) => {
            let lhs = pretty_expr(&a.node);
            let rhs = pretty_expr(&b.node);
            // Detect primed variable assignment.
            if let Expr::Prime(inner) = &a.node {
                let var = pretty_expr(&inner.node);
                format!("{pad}{var} := {rhs}")
            } else {
                format!("{pad}assert {lhs} == {rhs}")
            }
        }
        Expr::In(a, b) => {
            format!("{pad}{} in {}", pretty_expr(&a.node), pretty_expr(&b.node))
        }
        Expr::Forall(_, _) => {
            format!("{pad}for all: {}", pretty_expr(expr))
        }
        Expr::Exists(_, _) => {
            format!("{pad}exists: {}", pretty_expr(expr))
        }
        _ => {
            format!("{pad}{}", pretty_expr(expr))
        }
    }
}
