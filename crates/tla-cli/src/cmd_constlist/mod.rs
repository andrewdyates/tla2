// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 const-list` — list all CONSTANT declarations.
//!
//! Extracts and displays all CONSTANT declarations from the spec,
//! including their arity (for operator constants).

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::Unit;
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the const-list command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ConstlistOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// List all CONSTANT declarations.
pub(crate) fn cmd_constlist(
    file: &Path,
    format: ConstlistOutputFormat,
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

    let mut constants: Vec<(String, usize)> = Vec::new();
    for unit in &module.units {
        if let Unit::Constant(decls) = &unit.node {
            for d in decls {
                constants.push((d.name.node.clone(), d.arity.unwrap_or(0)));
            }
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        ConstlistOutputFormat::Human => {
            println!("const-list: {}", file.display());
            println!("  constants: {}", constants.len());
            println!();
            for (name, arity) in &constants {
                if *arity > 0 {
                    println!("  {name}(_)  arity={arity}");
                } else {
                    println!("  {name}");
                }
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        ConstlistOutputFormat::Json => {
            let consts_json: Vec<serde_json::Value> = constants
                .iter()
                .map(|(name, arity)| {
                    serde_json::json!({
                        "name": name,
                        "arity": arity,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "constants": consts_json,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
