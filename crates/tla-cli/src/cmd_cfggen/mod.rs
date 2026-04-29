// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 cfg-gen` — generate a .cfg file from spec analysis.
//!
//! Produces a TLC configuration file with Init/Next from operator
//! analysis, constant declarations, and invariant candidates.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_core::ast::Unit;
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the cfg-gen command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CfggenOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Generate a .cfg configuration file from spec analysis.
pub(crate) fn cmd_cfggen(file: &Path, format: CfggenOutputFormat) -> Result<()> {
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

    let mut constants: Vec<String> = Vec::new();
    let mut has_init = false;
    let mut has_next = false;
    let mut invariant_candidates: Vec<String> = Vec::new();
    let mut operator_names: Vec<String> = Vec::new();

    for unit in &module.units {
        match &unit.node {
            Unit::Constant(decls) => {
                for d in decls {
                    constants.push(d.name.node.clone());
                }
            }
            Unit::Operator(def) => {
                let name = &def.name.node;
                operator_names.push(name.clone());
                if name == "Init" {
                    has_init = true;
                }
                if name == "Next" {
                    has_next = true;
                }
                // Heuristic: operators starting with "TypeOK", "Inv", or "Safety" are invariants.
                if name.starts_with("TypeOK")
                    || name.starts_with("Inv")
                    || name.starts_with("Safety")
                {
                    if def.params.is_empty() {
                        invariant_candidates.push(name.clone());
                    }
                }
            }
            _ => {}
        }
    }

    let mut cfg_lines: Vec<String> = Vec::new();
    cfg_lines.push(format!(
        "\\* Auto-generated config for {}",
        module.name.node
    ));

    if has_init {
        cfg_lines.push("INIT Init".to_string());
    }
    if has_next {
        cfg_lines.push("NEXT Next".to_string());
    }

    if !constants.is_empty() {
        cfg_lines.push(String::new());
        cfg_lines.push("CONSTANTS".to_string());
        for c in &constants {
            cfg_lines.push(format!("  {c} = {c}"));
        }
    }

    if !invariant_candidates.is_empty() {
        cfg_lines.push(String::new());
        for inv in &invariant_candidates {
            cfg_lines.push(format!("INVARIANT {inv}"));
        }
    }

    let cfg_text = cfg_lines.join("\n");
    let elapsed = start.elapsed().as_secs_f64();

    match format {
        CfggenOutputFormat::Human => {
            println!("cfg-gen: {}", file.display());
            println!("  init: {}", if has_init { "Init" } else { "(not found)" });
            println!("  next: {}", if has_next { "Next" } else { "(not found)" });
            println!("  constants: {}", constants.len());
            println!("  invariant candidates: {}", invariant_candidates.len());
            println!();
            println!("--- generated .cfg ---");
            println!("{cfg_text}");
            println!("--- end ---");
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        CfggenOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "has_init": has_init,
                "has_next": has_next,
                "constants": constants,
                "invariant_candidates": invariant_candidates,
                "generated_cfg": cfg_text,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
