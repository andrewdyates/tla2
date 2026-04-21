// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 unused-var` — detect unused variables.
//!
//! Identifies variables declared in VARIABLE that are never
//! referenced (read or written) in any operator body.

use std::collections::BTreeSet;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the unused-var command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnusedvarOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Detect unused variables.
pub(crate) fn cmd_unusedvar(
    file: &Path,
    format: UnusedvarOutputFormat,
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

    // Collect declared variables.
    let mut declared: BTreeSet<String> = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Variable(decls) = &unit.node {
            for d in decls {
                declared.insert(d.node.clone());
            }
        }
    }

    // Collect referenced variables.
    let mut referenced: BTreeSet<String> = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            collect_refs(&def.body.node, &declared, &mut referenced);
        }
    }

    let unused: Vec<&String> = declared.difference(&referenced).collect();

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        UnusedvarOutputFormat::Human => {
            println!("unused-var: {}", file.display());
            println!("  declared: {}", declared.len());
            println!("  referenced: {}", referenced.len());
            println!("  unused: {}", unused.len());
            if !unused.is_empty() {
                println!();
                for v in &unused {
                    println!("  - {v}");
                }
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        UnusedvarOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "declared": declared.len(),
                "referenced": referenced.len(),
                "unused": unused,
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

fn collect_refs(expr: &Expr, vars: &BTreeSet<String>, refs: &mut BTreeSet<String>) {
    match expr {
        Expr::StateVar(name, _, _) => {
            refs.insert(name.clone());
        }
        Expr::Ident(name, _) => {
            if vars.contains(name) {
                refs.insert(name.clone());
            }
        }
        Expr::Prime(inner) => {
            if let Expr::StateVar(name, _, _) = &inner.node {
                refs.insert(name.clone());
            } else {
                collect_refs(&inner.node, vars, refs);
            }
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Eq(a, b) | Expr::Neq(a, b)
        | Expr::Lt(a, b) | Expr::Gt(a, b) | Expr::Leq(a, b) | Expr::Geq(a, b)
        | Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Div(a, b)
        | Expr::Mod(a, b) | Expr::Range(a, b) | Expr::In(a, b) | Expr::NotIn(a, b)
        | Expr::Implies(a, b) | Expr::Subseteq(a, b) => {
            collect_refs(&a.node, vars, refs);
            collect_refs(&b.node, vars, refs);
        }
        Expr::Not(inner) | Expr::Neg(inner) => {
            collect_refs(&inner.node, vars, refs);
        }
        Expr::If(c, t, e) => {
            collect_refs(&c.node, vars, refs);
            collect_refs(&t.node, vars, refs);
            collect_refs(&e.node, vars, refs);
        }
        Expr::SetEnum(elems) | Expr::Times(elems) => {
            for e in elems {
                collect_refs(&e.node, vars, refs);
            }
        }
        Expr::Apply(f, args) => {
            collect_refs(&f.node, vars, refs);
            for a in args {
                collect_refs(&a.node, vars, refs);
            }
        }
        Expr::Forall(_, body) | Expr::Exists(_, body) => {
            collect_refs(&body.node, vars, refs);
        }
        _ => {}
    }
}
