// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 cluster` — cluster operators by variable affinity.
//!
//! Groups operators based on which variables they reference,
//! identifying natural clusters of related functionality.

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

/// Output format for the cluster command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ClusterOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Cluster operators by variable affinity.
pub(crate) fn cmd_cluster(
    file: &Path,
    format: ClusterOutputFormat,
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

    // --- Extract variable references per operator --------------------------

    let mut var_names: BTreeSet<String> = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Variable(decls) = &unit.node {
            for d in decls {
                var_names.insert(d.node.clone());
            }
        }
    }

    let mut op_vars: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            let mut refs = BTreeSet::new();
            collect_var_refs(&def.body.node, &var_names, &mut refs);
            if !refs.is_empty() {
                op_vars.insert(def.name.node.clone(), refs);
            }
        }
    }

    // --- Build clusters using shared-variable affinity ---------------------

    // Simple clustering: group operators that share at least one variable.
    let mut clusters: Vec<Cluster> = Vec::new();

    let mut unclustered: BTreeSet<String> = op_vars.keys().cloned().collect();

    while !unclustered.is_empty() {
        let seed = unclustered.iter().next().unwrap().clone();
        unclustered.remove(&seed);

        let mut cluster_ops: BTreeSet<String> = BTreeSet::new();
        let mut cluster_vars: BTreeSet<String> = BTreeSet::new();
        cluster_ops.insert(seed.clone());
        if let Some(vars) = op_vars.get(&seed) {
            cluster_vars.extend(vars.iter().cloned());
        }

        // Expand: add any unclustered operator that shares a variable.
        let mut changed = true;
        while changed {
            changed = false;
            let candidates: Vec<String> = unclustered.iter().cloned().collect();
            for op in candidates {
                if let Some(vars) = op_vars.get(&op) {
                    if vars.iter().any(|v| cluster_vars.contains(v)) {
                        unclustered.remove(&op);
                        cluster_ops.insert(op);
                        cluster_vars.extend(vars.iter().cloned());
                        changed = true;
                    }
                }
            }
        }

        clusters.push(Cluster {
            operators: cluster_ops.into_iter().collect(),
            variables: cluster_vars.into_iter().collect(),
        });
    }

    // Sort clusters by size descending.
    clusters.sort_by(|a, b| b.operators.len().cmp(&a.operators.len()));

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        ClusterOutputFormat::Human => {
            println!("cluster: {}", file.display());
            println!("  clusters: {}", clusters.len());
            println!();
            for (i, c) in clusters.iter().enumerate() {
                println!("  Cluster {i} ({} operators, {} variables):", c.operators.len(), c.variables.len());
                println!("    operators: {}", c.operators.join(", "));
                println!("    variables: {}", c.variables.join(", "));
                println!();
            }
            println!("  elapsed: {elapsed:.2}s");
        }
        ClusterOutputFormat::Json => {
            let clusters_json: Vec<serde_json::Value> = clusters
                .iter()
                .map(|c| {
                    serde_json::json!({
                        "operators": c.operators,
                        "variables": c.variables,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "cluster_count": clusters.len(),
                "clusters": clusters_json,
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

struct Cluster {
    operators: Vec<String>,
    variables: Vec<String>,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn collect_var_refs(expr: &Expr, var_names: &BTreeSet<String>, refs: &mut BTreeSet<String>) {
    match expr {
        Expr::Ident(name, _) | Expr::StateVar(name, _, _) => {
            if var_names.contains(name.as_str()) {
                refs.insert(name.clone());
            }
        }
        Expr::And(a, b) | Expr::Or(a, b) | Expr::Implies(a, b)
        | Expr::Eq(a, b) | Expr::Neq(a, b) | Expr::Lt(a, b) | Expr::Gt(a, b)
        | Expr::Leq(a, b) | Expr::Geq(a, b) | Expr::In(a, b) => {
            collect_var_refs(&a.node, var_names, refs);
            collect_var_refs(&b.node, var_names, refs);
        }
        Expr::Not(inner) | Expr::Prime(inner) | Expr::Neg(inner) => {
            collect_var_refs(&inner.node, var_names, refs);
        }
        Expr::If(c, t, e) => {
            collect_var_refs(&c.node, var_names, refs);
            collect_var_refs(&t.node, var_names, refs);
            collect_var_refs(&e.node, var_names, refs);
        }
        Expr::Apply(f, args) => {
            collect_var_refs(&f.node, var_names, refs);
            for arg in args {
                collect_var_refs(&arg.node, var_names, refs);
            }
        }
        _ => {}
    }
}
