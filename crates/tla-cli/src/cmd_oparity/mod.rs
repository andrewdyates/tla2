// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 op-arity` — list operators with their arities.
//!
//! Extracts all operator definitions and displays their names
//! and parameter counts.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::Unit;
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the op-arity command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OparityOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// List operators with their arities.
pub(crate) fn cmd_oparity(
    file: &Path,
    format: OparityOutputFormat,
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

    let mut ops: Vec<(String, usize, Vec<String>)> = Vec::new();

    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            let params: Vec<String> = def.params.iter().map(|p| p.name.node.clone()).collect();
            ops.push((def.name.node.clone(), def.params.len(), params));
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        OparityOutputFormat::Human => {
            println!("op-arity: {}", file.display());
            println!("  operators: {}", ops.len());
            println!();
            for (name, arity, params) in &ops {
                if *arity == 0 {
                    println!("  {name}  (nullary)");
                } else {
                    println!("  {name}({})  arity={arity}", params.join(", "));
                }
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        OparityOutputFormat::Json => {
            let ops_json: Vec<serde_json::Value> = ops
                .iter()
                .map(|(name, arity, params)| {
                    serde_json::json!({
                        "name": name,
                        "arity": arity,
                        "params": params,
                    })
                })
                .collect();

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "operators": ops_json,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
