// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 project` — project state space onto a variable subset.
//!
//! Explores the state space and reports statistics projected onto
//! a user-specified subset of variables. This helps estimate the
//! effective state space contribution of each variable subset.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::ast::{Module, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the project command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ProjectOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Run projection analysis on a TLA+ spec.
pub(crate) fn cmd_project(
    file: &Path,
    config: Option<&Path>,
    variables: &[String],
    max_states: usize,
    format: ProjectOutputFormat,
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

    // --- Validate variables ------------------------------------------------

    let all_vars = extract_var_names(&module);
    let mut missing: Vec<String> = Vec::new();
    for v in variables {
        if !all_vars.iter().any(|av| av == v) {
            missing.push(v.clone());
        }
    }
    if !missing.is_empty() {
        bail!(
            "variables not found in spec: {}. Available: {}",
            missing.join(", "),
            all_vars.join(", ")
        );
    }

    let excluded: Vec<String> = all_vars
        .iter()
        .filter(|v| !variables.contains(v))
        .cloned()
        .collect();

    // --- Load config -------------------------------------------------------

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
        Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        }
    };

    // --- Run model check ---------------------------------------------------

    let mut mc = ModelChecker::new(&module, &parsed_config);
    mc.set_max_states(max_states);
    mc.set_deadlock_check(false);
    let check_result = mc.check();
    let stats = check_result.stats();
    let is_success = matches!(check_result, CheckResult::Success(_));

    let elapsed = start.elapsed().as_secs_f64();

    // --- Compute projection metrics ----------------------------------------

    let projection_ratio = variables.len() as f64 / all_vars.len().max(1) as f64;

    // Upper bound on projected states: full state count (projection can only reduce)
    let projected_upper = stats.states_found;

    // --- Output ------------------------------------------------------------

    match format {
        ProjectOutputFormat::Human => {
            println!("project: {}", file.display());
            println!("  projection: [{}]", variables.join(", "));
            println!("  excluded:   [{}]", excluded.join(", "));
            println!();
            println!("  Full state space:");
            println!("    variables:      {}", all_vars.len());
            println!("    states:         {}", stats.states_found);
            println!("    max depth:      {}", stats.max_depth);
            println!();
            println!("  Projection ({}/{} variables):", variables.len(), all_vars.len());
            println!("    projected states (upper bound): {projected_upper}");
            println!("    projection ratio: {projection_ratio:.1}");
            println!();
            println!("  Note: exact projected state count requires per-state");
            println!("  variable extraction (future work). Upper bound = full count.");
            println!("  elapsed: {elapsed:.2}s");
        }
        ProjectOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "projection_variables": variables,
                "excluded_variables": excluded,
                "statistics": {
                    "total_variables": all_vars.len(),
                    "projected_variables": variables.len(),
                    "total_states": stats.states_found,
                    "projected_states_upper_bound": projected_upper,
                    "max_depth": stats.max_depth,
                    "projection_ratio": projection_ratio,
                    "elapsed_seconds": elapsed,
                },
                "model_check_passed": is_success,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn extract_var_names(module: &Module) -> Vec<String> {
    let mut vars = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(decls) = &unit.node {
            for decl in decls {
                vars.push(decl.node.clone());
            }
        }
    }
    vars
}
