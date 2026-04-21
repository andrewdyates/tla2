// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 crossref` — cross-reference index.
//!
//! Builds a cross-reference index showing where each operator, variable,
//! and constant is defined and used throughout the specification.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the crossref command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CrossrefOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Build a cross-reference index for a TLA+ spec.
pub(crate) fn cmd_crossref(
    file: &Path,
    format: CrossrefOutputFormat,
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

    // --- Build index -------------------------------------------------------

    let mut definitions: BTreeMap<String, &str> = BTreeMap::new(); // name -> kind
    let mut usages: BTreeMap<String, BTreeSet<String>> = BTreeMap::new(); // name -> set of using operators

    for unit in &module.units {
        match &unit.node {
            Unit::Variable(decls) => {
                for d in decls {
                    definitions.insert(d.node.clone(), "variable");
                }
            }
            Unit::Constant(decls) => {
                for d in decls {
                    definitions.insert(d.name.node.clone(), "constant");
                }
            }
            Unit::Operator(def) => {
                definitions.insert(def.name.node.clone(), "operator");
            }
            _ => {}
        }
    }

    // Scan each operator body for references.
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            let mut refs = BTreeSet::new();
            collect_references(&def.body.node, &mut refs);
            for r in refs {
                usages.entry(r).or_default().insert(def.name.node.clone());
            }
        }
    }

    // Unused definitions.
    let unused: Vec<String> = definitions
        .keys()
        .filter(|name| {
            !usages.contains_key(name.as_str())
                && *name != "Init"
                && *name != "Next"
                && *name != "Spec"
        })
        .cloned()
        .collect();

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        CrossrefOutputFormat::Human => {
            println!("crossref: {}", file.display());
            println!("  definitions: {}", definitions.len());
            println!();
            for (name, kind) in &definitions {
                let used_by = usages
                    .get(name.as_str())
                    .map(|s| {
                        s.iter()
                            .cloned()
                            .collect::<Vec<_>>()
                            .join(", ")
                    })
                    .unwrap_or_else(|| "(unused)".to_string());
                println!("    {name} ({kind}) — used by: {used_by}");
            }
            if !unused.is_empty() {
                println!();
                println!("  Unused definitions: {}", unused.join(", "));
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        CrossrefOutputFormat::Json => {
            let entries: Vec<serde_json::Value> = definitions
                .iter()
                .map(|(name, kind)| {
                    let used_by: Vec<String> = usages
                        .get(name.as_str())
                        .map(|s| s.iter().cloned().collect())
                        .unwrap_or_default();
                    serde_json::json!({
                        "name": name,
                        "kind": kind,
                        "used_by": used_by,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "definitions": entries,
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

fn collect_references(expr: &Expr, refs: &mut BTreeSet<String>) {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            refs.insert(name.clone());
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b)
        | Expr::Eq(a, b) | Expr::Neq(a, b) | Expr::Lt(a, b) | Expr::Gt(a, b)
        | Expr::Leq(a, b) | Expr::Geq(a, b) | Expr::In(a, b) => {
            collect_references(&a.node, refs);
            collect_references(&b.node, refs);
        }
        Expr::Not(inner) | Expr::Prime(inner) | Expr::Neg(inner) => {
            collect_references(&inner.node, refs);
        }
        Expr::If(c, t, e) => {
            collect_references(&c.node, refs);
            collect_references(&t.node, refs);
            collect_references(&e.node, refs);
        }
        Expr::Apply(f, args) => {
            collect_references(&f.node, refs);
            for arg in args {
                collect_references(&arg.node, refs);
            }
        }
        _ => {}
    }
}
