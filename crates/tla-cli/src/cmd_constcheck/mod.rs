// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 const-check` — validate constant assignments in config.
//!
//! Verifies that all CONSTANT declarations in the spec have
//! corresponding assignments in the .cfg file, and that no
//! config assignments reference non-existent constants.

use std::collections::BTreeSet;
use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::Config;
use tla_core::ast::Unit;
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the const-check command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ConstcheckOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Validate constant assignments between spec and config.
pub(crate) fn cmd_constcheck(
    file: &Path,
    config: Option<&Path>,
    format: ConstcheckOutputFormat,
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

    let has_config = config_path_buf.exists();
    let parsed_config = if has_config {
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

    // Collect declared constants from spec.
    let mut declared: BTreeSet<String> = BTreeSet::new();
    for unit in &module.units {
        if let Unit::Constant(decls) = &unit.node {
            for d in decls {
                declared.insert(d.name.node.clone());
            }
        }
    }

    // Collect assigned constants from config.
    let mut assigned: BTreeSet<String> = BTreeSet::new();
    for (name, _) in &parsed_config.constants {
        assigned.insert(name.clone());
    }

    let missing: Vec<&String> = declared.difference(&assigned).collect();
    let extra: Vec<&String> = assigned.difference(&declared).collect();
    let matched: Vec<&String> = declared.intersection(&assigned).collect();
    let ok = missing.is_empty() && extra.is_empty();

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        ConstcheckOutputFormat::Human => {
            println!("const-check: {}", file.display());
            println!("  config: {}", if has_config { config_path_buf.display().to_string() } else { "(none)".to_string() });
            println!("  declared constants: {}", declared.len());
            println!("  assigned constants: {}", assigned.len());
            println!("  status: {}", if ok { "OK" } else { "ISSUES FOUND" });
            println!();
            if !missing.is_empty() {
                println!("  Missing assignments (declared but not in config):");
                for name in &missing {
                    println!("    - {name}");
                }
                println!();
            }
            if !extra.is_empty() {
                println!("  Extra assignments (in config but not declared):");
                for name in &extra {
                    println!("    - {name}");
                }
                println!();
            }
            if !matched.is_empty() {
                println!("  Matched ({}):", matched.len());
                for name in &matched {
                    println!("    - {name}");
                }
                println!();
            }
            println!("  elapsed: {elapsed:.2}s");
        }
        ConstcheckOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "config": if has_config { config_path_buf.display().to_string() } else { "(none)".to_string() },
                "declared_count": declared.len(),
                "assigned_count": assigned.len(),
                "ok": ok,
                "missing": missing,
                "extra": extra,
                "matched": matched,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
