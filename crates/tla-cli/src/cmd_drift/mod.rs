// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 drift` — specification drift detection.
//!
//! Compares two versions of a TLA+ specification and reports structural
//! differences: added/removed/changed operators, variables, and constants.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Module, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the drift command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DriftOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Detect drift between two versions of a TLA+ spec.
pub(crate) fn cmd_drift(
    file_a: &Path,
    file_b: &Path,
    format: DriftOutputFormat,
) -> Result<()> {
    let start = Instant::now();

    let module_a = parse_module(file_a)?;
    let module_b = parse_module(file_b)?;

    // --- Extract declarations from both ------------------------------------

    let info_a = extract_info(&module_a);
    let info_b = extract_info(&module_b);

    // --- Compute diffs -----------------------------------------------------

    let mut diffs: Vec<DriftEntry> = Vec::new();

    // Variables.
    for v in &info_a.variables {
        if !info_b.variables.contains(v) {
            diffs.push(DriftEntry {
                kind: "variable".to_string(),
                name: v.clone(),
                change: "removed".to_string(),
                detail: String::new(),
            });
        }
    }
    for v in &info_b.variables {
        if !info_a.variables.contains(v) {
            diffs.push(DriftEntry {
                kind: "variable".to_string(),
                name: v.clone(),
                change: "added".to_string(),
                detail: String::new(),
            });
        }
    }

    // Constants.
    for c in &info_a.constants {
        if !info_b.constants.contains(c) {
            diffs.push(DriftEntry {
                kind: "constant".to_string(),
                name: c.clone(),
                change: "removed".to_string(),
                detail: String::new(),
            });
        }
    }
    for c in &info_b.constants {
        if !info_a.constants.contains(c) {
            diffs.push(DriftEntry {
                kind: "constant".to_string(),
                name: c.clone(),
                change: "added".to_string(),
                detail: String::new(),
            });
        }
    }

    // Operators.
    for (name, body_a) in &info_a.operators {
        if let Some(body_b) = info_b.operators.get(name) {
            if body_a != body_b {
                diffs.push(DriftEntry {
                    kind: "operator".to_string(),
                    name: name.clone(),
                    change: "modified".to_string(),
                    detail: format!("was: {}", truncate(body_a, 60)),
                });
            }
        } else {
            diffs.push(DriftEntry {
                kind: "operator".to_string(),
                name: name.clone(),
                change: "removed".to_string(),
                detail: String::new(),
            });
        }
    }
    for name in info_b.operators.keys() {
        if !info_a.operators.contains_key(name) {
            diffs.push(DriftEntry {
                kind: "operator".to_string(),
                name: name.clone(),
                change: "added".to_string(),
                detail: String::new(),
            });
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        DriftOutputFormat::Human => {
            println!("drift: {} -> {}", file_a.display(), file_b.display());
            println!("  differences: {}", diffs.len());
            println!();
            if diffs.is_empty() {
                println!("  No structural differences detected.");
            } else {
                for d in &diffs {
                    if d.detail.is_empty() {
                        println!("    {} {} {}", d.change, d.kind, d.name);
                    } else {
                        println!("    {} {} {} — {}", d.change, d.kind, d.name, d.detail);
                    }
                }
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        DriftOutputFormat::Json => {
            let diffs_json: Vec<serde_json::Value> = diffs
                .iter()
                .map(|d| {
                    serde_json::json!({
                        "kind": d.kind,
                        "name": d.name,
                        "change": d.change,
                        "detail": d.detail,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file_a": file_a.display().to_string(),
                "file_b": file_b.display().to_string(),
                "differences": diffs_json,
                "total_differences": diffs.len(),
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

struct DriftEntry {
    kind: String,
    name: String,
    change: String,
    detail: String,
}

struct SpecInfo {
    variables: BTreeSet<String>,
    constants: BTreeSet<String>,
    operators: BTreeMap<String, String>, // name -> pretty-printed body
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn parse_module(file: &Path) -> Result<Module> {
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
            "{}: lowering failed with {} error(s)",
            file.display(),
            lower_result.errors.len()
        );
    }
    lower_result
        .module
        .context(format!("{}: lowering produced no module", file.display()))
}

fn extract_info(module: &Module) -> SpecInfo {
    let mut info = SpecInfo {
        variables: BTreeSet::new(),
        constants: BTreeSet::new(),
        operators: BTreeMap::new(),
    };

    for unit in &module.units {
        match &unit.node {
            Unit::Variable(decls) => {
                for d in decls {
                    info.variables.insert(d.node.clone());
                }
            }
            Unit::Constant(decls) => {
                for d in decls {
                    info.constants.insert(d.name.node.clone());
                }
            }
            Unit::Operator(def) => {
                info.operators
                    .insert(def.name.node.clone(), pretty_expr(&def.body.node));
            }
            _ => {}
        }
    }

    info
}

fn truncate(s: &str, max: usize) -> String {
    if s.len() > max {
        format!("{}...", &s[..max.saturating_sub(3)])
    } else {
        s.to_string()
    }
}
