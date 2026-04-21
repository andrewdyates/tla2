// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 var-track` — track variable usage across operators.
//!
//! For each variable, identifies which operators read it (unprimed)
//! and which operators write it (primed).

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the var-track command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum VartrackOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Track variable read/write usage across operators.
pub(crate) fn cmd_vartrack(
    file: &Path,
    format: VartrackOutputFormat,
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

    // Collect variable names.
    let mut var_names: BTreeSet<String> = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Variable(decls) = &unit.node {
            for d in decls {
                var_names.insert(d.node.clone());
            }
        }
    }

    // For each operator, track which variables are read/written.
    let mut reads: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut writes: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

    for v in &var_names {
        reads.insert(v.clone(), BTreeSet::new());
        writes.insert(v.clone(), BTreeSet::new());
    }

    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            let op_name = &def.name.node;
            let mut read_vars = BTreeSet::new();
            let mut write_vars = BTreeSet::new();
            collect_var_refs(&def.body.node, &var_names, &mut read_vars, &mut write_vars);
            for v in &read_vars {
                reads.entry(v.clone()).or_default().insert(op_name.clone());
            }
            for v in &write_vars {
                writes.entry(v.clone()).or_default().insert(op_name.clone());
            }
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        VartrackOutputFormat::Human => {
            println!("var-track: {}", file.display());
            println!("  variables: {}", var_names.len());
            println!();
            for v in &var_names {
                let r = reads.get(v).map(|s| s.len()).unwrap_or(0);
                let w = writes.get(v).map(|s| s.len()).unwrap_or(0);
                println!("  {v} ({r} readers, {w} writers):");
                if let Some(rs) = reads.get(v) {
                    if !rs.is_empty() {
                        println!("    read by: {}", rs.iter().cloned().collect::<Vec<_>>().join(", "));
                    }
                }
                if let Some(ws) = writes.get(v) {
                    if !ws.is_empty() {
                        println!("    written by: {}", ws.iter().cloned().collect::<Vec<_>>().join(", "));
                    }
                }
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        VartrackOutputFormat::Json => {
            let vars_json: Vec<serde_json::Value> = var_names
                .iter()
                .map(|v| {
                    serde_json::json!({
                        "variable": v,
                        "readers": reads.get(v).map(|s| s.iter().cloned().collect::<Vec<_>>()).unwrap_or_default(),
                        "writers": writes.get(v).map(|s| s.iter().cloned().collect::<Vec<_>>()).unwrap_or_default(),
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "variables": vars_json,
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

fn collect_var_refs(
    expr: &Expr,
    var_names: &BTreeSet<String>,
    reads: &mut BTreeSet<String>,
    writes: &mut BTreeSet<String>,
) {
    match expr {
        Expr::StateVar(name, _, _) => {
            reads.insert(name.clone());
        }
        Expr::Prime(inner) => {
            // Primed variable = write.
            if let Expr::StateVar(name, _, _) = &inner.node {
                writes.insert(name.clone());
            } else {
                collect_var_refs(&inner.node, var_names, reads, writes);
            }
        }
        Expr::Ident(name, _) => {
            if var_names.contains(name) {
                reads.insert(name.clone());
            }
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Eq(a, b) | Expr::Neq(a, b)
        | Expr::Lt(a, b) | Expr::Gt(a, b) | Expr::Leq(a, b) | Expr::Geq(a, b)
        | Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Div(a, b)
        | Expr::Mod(a, b) | Expr::Range(a, b) | Expr::In(a, b) | Expr::NotIn(a, b)
        | Expr::Implies(a, b) | Expr::Subseteq(a, b) => {
            collect_var_refs(&a.node, var_names, reads, writes);
            collect_var_refs(&b.node, var_names, reads, writes);
        }
        Expr::Times(elems) => {
            for e in elems {
                collect_var_refs(&e.node, var_names, reads, writes);
            }
        }
        Expr::Not(inner) | Expr::Neg(inner) => {
            collect_var_refs(&inner.node, var_names, reads, writes);
        }
        Expr::If(cond, then, els) => {
            collect_var_refs(&cond.node, var_names, reads, writes);
            collect_var_refs(&then.node, var_names, reads, writes);
            collect_var_refs(&els.node, var_names, reads, writes);
        }
        Expr::SetEnum(elems) => {
            for e in elems {
                collect_var_refs(&e.node, var_names, reads, writes);
            }
        }
        Expr::Apply(f, args) => {
            collect_var_refs(&f.node, var_names, reads, writes);
            for a in args {
                collect_var_refs(&a.node, var_names, reads, writes);
            }
        }
        Expr::Forall(_, body) | Expr::Exists(_, body) => {
            collect_var_refs(&body.node, var_names, reads, writes);
        }
        _ => {}
    }
}
