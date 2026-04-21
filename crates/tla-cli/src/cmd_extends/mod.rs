// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 extends` — list EXTENDS dependencies.
//!
//! Shows which standard modules the spec extends.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the extends command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ExtendsOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// List EXTENDS dependencies.
pub(crate) fn cmd_extends(
    file: &Path,
    format: ExtendsOutputFormat,
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

    let extends: Vec<String> = module.extends.iter().map(|e| e.node.clone()).collect();

    let standard_modules = ["Integers", "Naturals", "Reals", "Sequences", "FiniteSets",
        "TLC", "Bags", "TLCExt", "Apalache", "Json"];
    let standard: Vec<&String> = extends.iter().filter(|e| standard_modules.contains(&e.as_str())).collect();
    let custom: Vec<&String> = extends.iter().filter(|e| !standard_modules.contains(&e.as_str())).collect();

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        ExtendsOutputFormat::Human => {
            println!("extends: {}", file.display());
            println!("  module: {}", module.name.node);
            println!("  total extends: {}", extends.len());
            if !standard.is_empty() {
                println!("  standard: {}", standard.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", "));
            }
            if !custom.is_empty() {
                println!("  custom: {}", custom.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", "));
            }
            if extends.is_empty() {
                println!("  (no EXTENDS)");
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        ExtendsOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "module": module.name.node,
                "extends": extends,
                "standard": standard,
                "custom": custom,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
