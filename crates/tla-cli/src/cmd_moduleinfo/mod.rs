// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 module-info` — display module structure and metadata.
//!
//! Shows module name, EXTENDS list, unit counts by type,
//! and structural overview.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::Unit;
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the module-info command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ModuleinfoOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Display module structure and metadata.
pub(crate) fn cmd_moduleinfo(file: &Path, format: ModuleinfoOutputFormat) -> Result<()> {
    let start = Instant::now();

    let source = read_source(file)?;
    let tree = parse_to_syntax_tree(&source);
    let lower_result = lower(FileId(0), &tree);
    if !lower_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &lower_result.errors {
            let diagnostic = tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "lowering failed with {} error(s)",
            lower_result.errors.len()
        );
    }
    let module = lower_result.module.context("lowering produced no module")?;

    let mut constant_count = 0usize;
    let mut variable_count = 0usize;
    let mut operator_count = 0usize;
    let mut instance_count = 0usize;
    let mut assumption_count = 0usize;
    let mut other_count = 0usize;

    for unit in &module.units {
        match &unit.node {
            Unit::Constant(decls) => constant_count += decls.len(),
            Unit::Variable(decls) => variable_count += decls.len(),
            Unit::Operator(_) => operator_count += 1,
            Unit::Instance(_) => instance_count += 1,
            Unit::Assume(_) => assumption_count += 1,
            _ => other_count += 1,
        }
    }

    let extends: Vec<String> = module.extends.iter().map(|e| e.node.clone()).collect();
    let total_units = module.units.len();
    let line_count = source.lines().count();

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        ModuleinfoOutputFormat::Human => {
            println!("module-info: {}", file.display());
            println!("  module: {}", module.name.node);
            if !extends.is_empty() {
                println!("  extends: {}", extends.join(", "));
            }
            println!("  lines: {line_count}");
            println!("  total units: {total_units}");
            println!("    constants: {constant_count}");
            println!("    variables: {variable_count}");
            println!("    operators: {operator_count}");
            println!("    instances: {instance_count}");
            println!("    assumptions: {assumption_count}");
            if other_count > 0 {
                println!("    other: {other_count}");
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        ModuleinfoOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "module": module.name.node,
                "extends": extends,
                "lines": line_count,
                "total_units": total_units,
                "constants": constant_count,
                "variables": variable_count,
                "operators": operator_count,
                "instances": instance_count,
                "assumptions": assumption_count,
                "other": other_count,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
