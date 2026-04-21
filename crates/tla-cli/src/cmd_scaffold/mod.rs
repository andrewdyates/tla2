// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 scaffold` — generate a configuration file from a specification.
//!
//! Analyzes a TLA+ specification to automatically generate a `.cfg`
//! configuration file with Init/Next, detected invariants, and
//! constant assignments based on heuristics.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Expr, Module, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the scaffold command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ScaffoldOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Generate a configuration scaffold for a TLA+ spec.
pub(crate) fn cmd_scaffold(
    file: &Path,
    format: ScaffoldOutputFormat,
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

    // --- Analyze spec ------------------------------------------------------

    let mut var_names: Vec<String> = Vec::new();
    let mut const_names: Vec<String> = Vec::new();
    let mut op_names: Vec<String> = Vec::new();
    let mut has_init = false;
    let mut has_next = false;
    let mut candidate_invariants: Vec<String> = Vec::new();
    let mut candidate_properties: Vec<String> = Vec::new();

    for unit in &module.units {
        match &unit.node {
            Unit::Variable(decls) => {
                for decl in decls {
                    var_names.push(decl.node.clone());
                }
            }
            Unit::Constant(decls) => {
                for decl in decls {
                    const_names.push(decl.name.node.clone());
                }
            }
            Unit::Operator(def) => {
                let name = &def.name.node;
                op_names.push(name.clone());
                if name == "Init" {
                    has_init = true;
                }
                if name == "Next" {
                    has_next = true;
                }
                // Heuristic: operators named TypeOK, TypeInv, *Inv, *Safe* are invariant candidates.
                if def.params.is_empty() {
                    if name == "TypeOK"
                        || name == "TypeInv"
                        || name.ends_with("Inv")
                        || name.ends_with("Invariant")
                        || name.contains("Safe")
                    {
                        candidate_invariants.push(name.clone());
                    }
                    // Heuristic: operators named *Spec, *Liveness, *Fair* are property candidates.
                    if name.ends_with("Spec")
                        || name.ends_with("Liveness")
                        || name.contains("Fair")
                    {
                        candidate_properties.push(name.clone());
                    }
                }
            }
            _ => {}
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    // --- Build cfg text ----------------------------------------------------

    let mut cfg_lines: Vec<String> = Vec::new();
    cfg_lines.push(format!("\\* Auto-generated config for {}", file.display()));
    cfg_lines.push(String::new());

    if has_init {
        cfg_lines.push("INIT Init".to_string());
    }
    if has_next {
        cfg_lines.push("NEXT Next".to_string());
    }
    cfg_lines.push(String::new());

    if !const_names.is_empty() {
        cfg_lines.push("CONSTANTS".to_string());
        for c in &const_names {
            cfg_lines.push(format!("    {} = {}", c, suggest_constant_value(c)));
        }
        cfg_lines.push(String::new());
    }

    if !candidate_invariants.is_empty() {
        for inv in &candidate_invariants {
            cfg_lines.push(format!("INVARIANT {inv}"));
        }
        cfg_lines.push(String::new());
    }

    if !candidate_properties.is_empty() {
        for prop in &candidate_properties {
            cfg_lines.push(format!("PROPERTY {prop}"));
        }
        cfg_lines.push(String::new());
    }

    let cfg_text = cfg_lines.join("\n");

    // --- Output ------------------------------------------------------------

    match format {
        ScaffoldOutputFormat::Human => {
            println!("scaffold: {}", file.display());
            println!();
            println!("  Variables ({}): {}", var_names.len(), var_names.join(", "));
            println!("  Constants ({}): {}", const_names.len(), const_names.join(", "));
            println!("  Operators ({}): {}", op_names.len(), op_names.join(", "));
            println!("  Init: {}", if has_init { "found" } else { "NOT FOUND" });
            println!("  Next: {}", if has_next { "found" } else { "NOT FOUND" });
            println!("  Invariant candidates: {}", candidate_invariants.join(", "));
            println!("  Property candidates: {}", candidate_properties.join(", "));
            println!();
            println!("--- Generated .cfg ---");
            println!("{cfg_text}");
            println!("--- end ---");
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        ScaffoldOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "analysis": {
                    "variables": var_names,
                    "constants": const_names,
                    "operators": op_names,
                    "has_init": has_init,
                    "has_next": has_next,
                    "candidate_invariants": candidate_invariants,
                    "candidate_properties": candidate_properties,
                },
                "generated_cfg": cfg_text,
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

/// Suggest a default constant value based on naming conventions.
fn suggest_constant_value(name: &str) -> String {
    let lower = name.to_lowercase();
    if lower.contains("node") || lower.contains("proc") || lower.contains("server") {
        "{n1, n2, n3}".to_string()
    } else if lower == "n" || lower == "m" || lower == "k" {
        "3".to_string()
    } else if lower.contains("max") || lower.contains("limit") || lower.contains("size") {
        "4".to_string()
    } else if lower.contains("null") || lower.contains("nil") || lower.contains("none") {
        "\"null\"".to_string()
    } else {
        format!("\"{}\"", name)
    }
}
