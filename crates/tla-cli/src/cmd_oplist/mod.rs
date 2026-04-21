// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 op-list` — list all operator definitions.
//!
//! Extracts and displays all operator names in declaration order.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::Unit;
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the op-list command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OplistOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// List all operator definitions.
pub(crate) fn cmd_oplist(
    file: &Path,
    format: OplistOutputFormat,
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

    let mut operators: Vec<String> = Vec::new();
    for unit in &module.units {
        if let Unit::Operator(def) = &unit.node {
            operators.push(def.name.node.clone());
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        OplistOutputFormat::Human => {
            println!("op-list: {}", file.display());
            println!("  operators: {}", operators.len());
            println!();
            for (i, name) in operators.iter().enumerate() {
                println!("  {}. {name}", i + 1);
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        OplistOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "operators": operators,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
