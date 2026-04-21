// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 unused-const` — detect unused constants.
//!
//! Identifies constants declared in CONSTANT that are never
//! referenced in any operator body.

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

/// Output format for the unused-const command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnusedconstOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Detect unused constants.
pub(crate) fn cmd_unusedconst(
    file: &Path,
    format: UnusedconstOutputFormat,
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

    let mut declared: BTreeSet<String> = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Constant(decls) = &unit.node {
            for d in decls {
                declared.insert(d.name.node.clone());
            }
        }
    }

    let mut referenced: BTreeSet<String> = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            collect_ident_refs(&def.body.node, &declared, &mut referenced);
        }
    }

    let unused: Vec<&String> = declared.difference(&referenced).collect();

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        UnusedconstOutputFormat::Human => {
            println!("unused-const: {}", file.display());
            println!("  declared: {}", declared.len());
            println!("  referenced: {}", referenced.len());
            println!("  unused: {}", unused.len());
            if !unused.is_empty() {
                println!();
                for c in &unused {
                    println!("  - {c}");
                }
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        UnusedconstOutputFormat::Json => {
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

fn collect_ident_refs(expr: &Expr, consts: &BTreeSet<String>, refs: &mut BTreeSet<String>) {
    match expr {
        Expr::Ident(name, _) => {
            if consts.contains(name) {
                refs.insert(name.clone());
            }
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Eq(a, b) | Expr::Neq(a, b)
        | Expr::Lt(a, b) | Expr::Gt(a, b) | Expr::Leq(a, b) | Expr::Geq(a, b)
        | Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Div(a, b)
        | Expr::Mod(a, b) | Expr::Range(a, b) | Expr::In(a, b) | Expr::NotIn(a, b)
        | Expr::Implies(a, b) | Expr::Subseteq(a, b) => {
            collect_ident_refs(&a.node, consts, refs);
            collect_ident_refs(&b.node, consts, refs);
        }
        Expr::Not(inner) | Expr::Neg(inner) | Expr::Prime(inner) => {
            collect_ident_refs(&inner.node, consts, refs);
        }
        Expr::If(c, t, e) => {
            collect_ident_refs(&c.node, consts, refs);
            collect_ident_refs(&t.node, consts, refs);
            collect_ident_refs(&e.node, consts, refs);
        }
        Expr::SetEnum(elems) | Expr::Times(elems) => {
            for e in elems {
                collect_ident_refs(&e.node, consts, refs);
            }
        }
        Expr::Apply(f, args) => {
            collect_ident_refs(&f.node, consts, refs);
            for a in args {
                collect_ident_refs(&a.node, consts, refs);
            }
        }
        Expr::Forall(_, body) | Expr::Exists(_, body) => {
            collect_ident_refs(&body.node, consts, refs);
        }
        _ => {}
    }
}
