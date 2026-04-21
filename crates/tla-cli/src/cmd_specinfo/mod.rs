// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 spec-info` — comprehensive specification information summary.
//!
//! Displays module name, EXTENDS, constants, variables, operators,
//! and structural statistics for a TLA+ specification.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::Unit;
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the spec-info command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SpecinfoOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Display comprehensive specification information.
pub(crate) fn cmd_specinfo(
    file: &Path,
    format: SpecinfoOutputFormat,
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

    let mut constants: Vec<String> = Vec::new();
    let mut variables: Vec<String> = Vec::new();
    let mut operators: Vec<(String, usize)> = Vec::new();
    let mut extends: Vec<String> = Vec::new();

    for ext in &module.extends {
        extends.push(ext.node.clone());
    }

    for unit in &module.units {
        match &unit.node {
            Unit::Constant(decls) => {
                for d in decls {
                    constants.push(d.name.node.clone());
                }
            }
            Unit::Variable(decls) => {
                for d in decls {
                    variables.push(d.node.clone());
                }
            }
            Unit::Operator(def) => {
                operators.push((def.name.node.clone(), def.params.len()));
            }
            _ => {}
        }
    }

    let line_count = source.lines().count();
    let elapsed = start.elapsed().as_secs_f64();

    match format {
        SpecinfoOutputFormat::Human => {
            println!("spec-info: {}", file.display());
            println!("  module: {}", module.name.node);
            if !extends.is_empty() {
                println!("  extends: {}", extends.join(", "));
            }
            println!("  lines: {line_count}");
            println!("  constants ({}): {}", constants.len(), constants.join(", "));
            println!("  variables ({}): {}", variables.len(), variables.join(", "));
            println!("  operators: {}", operators.len());
            for (name, arity) in &operators {
                if *arity > 0 {
                    println!("    {name}({arity})");
                } else {
                    println!("    {name}");
                }
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        SpecinfoOutputFormat::Json => {
            let ops_json: Vec<serde_json::Value> = operators
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
                "module": module.name.node,
                "extends": extends,
                "lines": line_count,
                "constants": constants,
                "variables": variables,
                "operators": ops_json,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
