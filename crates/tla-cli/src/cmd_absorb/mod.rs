// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 absorb` — absorb constant values from configuration.
//!
//! Reads constant assignments from the .cfg file and displays
//! the specification with constants replaced by their assigned values.

use std::collections::BTreeMap;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::Config;
use tla_core::ast::{OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, pretty_expr, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the absorb command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AbsorbOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Absorb constant values from config into spec display.
pub(crate) fn cmd_absorb(
    file: &Path,
    config: Option<&Path>,
    format: AbsorbOutputFormat,
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
        Config::default()
    };

    // --- Collect constant assignments from config --------------------------

    let const_assignments: BTreeMap<String, String> = parsed_config
        .constants
        .iter()
        .map(|(k, v)| (k.clone(), format!("{v}")))
        .collect();

    // --- Display spec with absorbed constants ------------------------------

    let mut const_decls: Vec<String> = Vec::new();
    let mut var_decls: Vec<String> = Vec::new();
    let mut ops: Vec<(String, String)> = Vec::new();

    for unit in &module.units {
        match &unit.node {
            Unit::Constant(decls) => {
                for d in decls {
                    let name = &d.name.node;
                    if let Some(val) = const_assignments.get(name.as_str()) {
                        const_decls.push(format!("{name} = {val} (from config)"));
                    } else {
                        const_decls.push(format!("{name} (unassigned)"));
                    }
                }
            }
            Unit::Variable(decls) => {
                for d in decls {
                    var_decls.push(d.node.clone());
                }
            }
            Unit::Operator(def) => {
                let body_text = pretty_expr(&def.body.node);
                // Simple text-level substitution of constant names with values.
                let mut absorbed = body_text.clone();
                for (name, val) in &const_assignments {
                    absorbed = absorbed.replace(name.as_str(), val.as_str());
                }
                ops.push((def.name.node.clone(), absorbed));
            }
            _ => {}
        }
    }

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        AbsorbOutputFormat::Human => {
            println!("absorb: {}", file.display());
            println!("  config: {}", config_path_buf.display());
            println!("  constants absorbed: {}", const_assignments.len());
            println!();
            for c in &const_decls {
                println!("  CONSTANT {c}");
            }
            println!();
            for (name, body) in &ops {
                let truncated = if body.len() > 100 {
                    format!("{}...", &body[..97])
                } else {
                    body.clone()
                };
                println!("  {name} == {truncated}");
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        AbsorbOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "config": config_path_buf.display().to_string(),
                "constant_assignments": const_assignments,
                "operators": ops.iter().map(|(n, b)| {
                    serde_json::json!({"name": n, "body_absorbed": b})
                }).collect::<Vec<_>>(),
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
