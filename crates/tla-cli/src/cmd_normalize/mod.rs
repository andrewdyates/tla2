// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 normalize` — normalize a specification to canonical form.
//!
//! Parses a TLA+ specification and outputs a normalized version with
//! operators sorted alphabetically, consistent formatting, and
//! canonical ordering of declarations.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::{Module, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the normalize command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NormalizeOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Normalize a TLA+ spec to canonical form.
pub(crate) fn cmd_normalize(
    file: &Path,
    format: NormalizeOutputFormat,
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

    // --- Extract declarations in canonical order ---------------------------

    let mut constants: Vec<String> = Vec::new();
    let mut variables: Vec<String> = Vec::new();
    let mut operators: Vec<(String, Vec<String>, String)> = Vec::new(); // (name, params, body)

    for unit in &module.units {
        match &unit.node {
            Unit::Constant(decls) => {
                for decl in decls {
                    constants.push(decl.name.node.clone());
                }
            }
            Unit::Variable(decls) => {
                for decl in decls {
                    variables.push(decl.node.clone());
                }
            }
            Unit::Operator(def) => {
                let params: Vec<String> = def.params.iter().map(|p| p.name.node.clone()).collect();
                let body = pretty_expr(&def.body.node);
                operators.push((def.name.node.clone(), params, body));
            }
            _ => {}
        }
    }

    // Sort constants and variables alphabetically.
    constants.sort();
    variables.sort();

    // Sort operators: Init first, Next second, then alphabetical.
    operators.sort_by(|a, b| {
        let priority = |name: &str| -> u8 {
            if name == "Init" {
                0
            } else if name == "Next" {
                1
            } else if name == "Spec" {
                2
            } else {
                3
            }
        };
        let pa = priority(&a.0);
        let pb = priority(&b.0);
        if pa != pb {
            pa.cmp(&pb)
        } else {
            a.0.cmp(&b.0)
        }
    });

    let elapsed = start.elapsed().as_secs_f64();

    // --- Build normalized output -------------------------------------------

    let mut normalized = String::new();
    normalized.push_str(&format!("---- MODULE {} ----\n", module.name.node));

    if !constants.is_empty() {
        normalized.push_str(&format!("CONSTANTS {}\n", constants.join(", ")));
    }
    if !variables.is_empty() {
        normalized.push_str(&format!("VARIABLES {}\n", variables.join(", ")));
    }
    normalized.push('\n');

    for (name, params, body) in &operators {
        if params.is_empty() {
            normalized.push_str(&format!("{name} == {body}\n\n"));
        } else {
            normalized.push_str(&format!("{}({}) == {}\n\n", name, params.join(", "), body));
        }
    }

    normalized.push_str("====\n");

    // --- Output ------------------------------------------------------------

    match format {
        NormalizeOutputFormat::Human => {
            println!("normalize: {}", file.display());
            println!("  constants: {}", constants.len());
            println!("  variables: {}", variables.len());
            println!("  operators: {}", operators.len());
            println!();
            println!("--- Normalized ---");
            print!("{normalized}");
            println!("--- end ---");
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        NormalizeOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "module_name": module.name.node,
                "constants": constants,
                "variables": variables,
                "operators": operators.iter().map(|(n, p, b)| {
                    serde_json::json!({
                        "name": n,
                        "params": p,
                        "body": b,
                    })
                }).collect::<Vec<_>>(),
                "normalized_text": normalized,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
