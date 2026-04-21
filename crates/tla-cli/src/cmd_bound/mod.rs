// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 bound` — state space bound estimation.
//!
//! Analyzes the specification and configuration to estimate an upper
//! bound on the state space size from type information, constant values,
//! and Init predicate structure.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::Config;
use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the bound command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BoundOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Estimate state space bounds for a TLA+ spec.
pub(crate) fn cmd_bound(
    file: &Path,
    config: Option<&Path>,
    format: BoundOutputFormat,
) -> Result<()> {
    let start = Instant::now();

    // --- Parse and lower ---------------------------------------------------

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

    // --- Load config -------------------------------------------------------

    let config_path_buf = match config {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            cfg
        }
    };

    let parsed_config = if config_path_buf.exists() {
        let cfg_source = std::fs::read_to_string(&config_path_buf)
            .with_context(|| format!("read config {}", config_path_buf.display()))?;
        Config::parse(&cfg_source).map_err(|errors| {
            for err in &errors {
                eprintln!("{}:{}: {}", config_path_buf.display(), err.line(), err);
            }
            anyhow::anyhow!("config parse failed with {} error(s)", errors.len())
        })?
    } else {
        Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        }
    };

    // --- Extract info ------------------------------------------------------

    let var_names = extract_var_names(&module);
    let operators = extract_operators(&module);

    // --- Analyze Init for variable domains ---------------------------------

    let init_name = parsed_config.init.as_deref().unwrap_or("Init");
    let mut var_bounds: Vec<VarBound> = Vec::new();

    if let Some(init_op) = operators.get(init_name) {
        let memberships = extract_memberships(&init_op.body.node);
        for var in &var_names {
            if let Some(domain_expr) = memberships.get(var.as_str()) {
                let domain_text = pretty_expr(domain_expr);
                let estimated_size = estimate_domain_size(domain_expr, &parsed_config);
                var_bounds.push(VarBound {
                    name: var.clone(),
                    domain: domain_text,
                    estimated_size,
                });
            } else {
                var_bounds.push(VarBound {
                    name: var.clone(),
                    domain: "unknown".to_string(),
                    estimated_size: None,
                });
            }
        }
    } else {
        for var in &var_names {
            var_bounds.push(VarBound {
                name: var.clone(),
                domain: "unknown".to_string(),
                estimated_size: None,
            });
        }
    }

    // --- Compute bounds ----------------------------------------------------

    let all_known = var_bounds.iter().all(|b| b.estimated_size.is_some());
    let total_bound: Option<u64> = if all_known && !var_bounds.is_empty() {
        var_bounds.iter().try_fold(1u64, |acc, b| {
            b.estimated_size.and_then(|s| acc.checked_mul(s))
        })
    } else {
        None
    };

    let known_count = var_bounds.iter().filter(|b| b.estimated_size.is_some()).count();

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        BoundOutputFormat::Human => {
            println!("bound: {}", file.display());
            println!("  variables: {}", var_names.len());
            println!();
            println!("  Variable domains (from Init):");
            for vb in &var_bounds {
                let size_str = vb
                    .estimated_size
                    .map(|s| s.to_string())
                    .unwrap_or_else(|| "?".to_string());
                println!("    {} \\in {} (|domain| = {})", vb.name, vb.domain, size_str);
            }
            println!();
            if let Some(bound) = total_bound {
                println!("  Upper bound: {} states", bound);
                println!("  (product of all variable domain sizes)");
            } else {
                println!(
                    "  Upper bound: unknown ({}/{} variable domains resolved)",
                    known_count,
                    var_bounds.len()
                );
            }
            println!("  elapsed: {elapsed:.2}s");
        }
        BoundOutputFormat::Json => {
            let vars_json: Vec<serde_json::Value> = var_bounds
                .iter()
                .map(|vb| {
                    serde_json::json!({
                        "name": vb.name,
                        "domain": vb.domain,
                        "estimated_size": vb.estimated_size,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "variables": vars_json,
                "total_bound": total_bound,
                "known_domains": known_count,
                "total_variables": var_bounds.len(),
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

struct VarBound {
    name: String,
    domain: String,
    estimated_size: Option<u64>,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn extract_var_names(module: &Module) -> Vec<String> {
    let mut vars = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(decls) = &unit.node {
            for decl in decls {
                vars.push(decl.node.clone());
            }
        }
    }
    vars
}

fn extract_operators(module: &Module) -> BTreeMap<String, &OperatorDef> {
    let mut ops = BTreeMap::new();
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            ops.insert(def.name.node.clone(), def);
        }
    }
    ops
}

/// Extract `var \in domain` memberships from Init conjuncts.
fn extract_memberships<'a>(expr: &'a Expr) -> BTreeMap<&'a str, &'a Expr> {
    let mut map = BTreeMap::new();
    extract_memberships_inner(expr, &mut map);
    map
}

fn extract_memberships_inner<'a>(expr: &'a Expr, map: &mut BTreeMap<&'a str, &'a Expr>) {
    match expr {
        Expr::And(a, b) => {
            extract_memberships_inner(&a.node, map);
            extract_memberships_inner(&b.node, map);
        }
        Expr::In(lhs, rhs) => {
            if let Expr::Ident(name, _) | Expr::StateVar(name, _, _) = &lhs.node {
                map.insert(name.as_str(), &rhs.node);
            }
        }
        _ => {}
    }
}

/// Estimate the size of a domain expression.
fn estimate_domain_size(expr: &Expr, _config: &Config) -> Option<u64> {
    match expr {
        // BOOLEAN has 2 elements
        Expr::Ident(name, _) if name == "BOOLEAN" => Some(2),
        // {a, b, c} set enumeration
        Expr::SetEnum(elems) => Some(elems.len() as u64),
        // a..b integer range
        Expr::Range(a, b) => {
            if let (Expr::Int(lo), Expr::Int(hi)) = (&a.node, &b.node) {
                if hi >= lo {
                    let size = hi - lo + 1i64;
                    size.to_string().parse::<u64>().ok()
                } else {
                    Some(0)
                }
            } else {
                None
            }
        }
        _ => None,
    }
}
