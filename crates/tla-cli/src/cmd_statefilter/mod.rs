// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 state-filter` — filter and query states from a model checking run.
//!
//! Explores the state space of a TLA+ specification via bounded BFS, applies
//! user-specified filter predicates, and reports matching states.
//!
//! # Filter syntax
//!
//! Filters are TLA+ expressions evaluated against each explored state:
//! - `x = 3` — variable equality
//! - `x > 3 /\ y < 5` — conjunction of conditions
//! - `MyPredicate` — named predicate from the spec

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::{bind_constants_from_config, Config, EvalCtx, ModelChecker};
use tla_core::ast::{Module, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the state-filter command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StateFilterOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Run the state-filter command.
///
/// Parses the specification, validates the filter expression, runs a bounded
/// BFS via ModelChecker, and reports exploration statistics. Full per-state
/// filtering requires state callback pipeline integration (future work).
pub(crate) fn cmd_state_filter(
    file: &Path,
    config: Option<&Path>,
    filter: &str,
    max_states: usize,
    _max_results: usize,
    format: StateFilterOutputFormat,
) -> Result<()> {
    let start = Instant::now();

    // --- Parse and lower the spec ------------------------------------------

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

    // --- Validate filter expression ----------------------------------------

    let _filter_def = parse_filter_expression(filter)?;

    // --- Extract variable names -------------------------------------------

    let var_names = extract_var_names(&module);
    if var_names.is_empty() {
        bail!("specification declares no VARIABLES — nothing to filter");
    }

    // --- Build eval context (validates constant bindings) ------------------

    let mut ctx = EvalCtx::new();
    ctx.load_module(&module);
    for name in &var_names {
        ctx.register_var(name.clone());
    }
    bind_constants_from_config(&mut ctx, &parsed_config)
        .with_context(|| "failed to bind constants from config")?;

    // --- Run bounded BFS via ModelChecker ----------------------------------

    let mut mc = ModelChecker::new(&module, &parsed_config);
    mc.set_max_states(max_states);
    mc.set_deadlock_check(false);
    let check_result = mc.check();
    let check_stats = check_result.stats();
    let total_explored = check_stats.states_found;

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output results ----------------------------------------------------

    match format {
        StateFilterOutputFormat::Human => {
            println!("state-filter: {}", file.display());
            println!("  filter: {filter}");
            println!("  filter expression: valid");
            println!("  BFS explored {total_explored} states in {elapsed:.1}s");
            println!("  max depth: {}", check_stats.max_depth);
            println!();
            println!("Note: per-state filter evaluation requires state callback integration.");
            println!(
                "Use `tla2 check` with the filter as an invariant for full state-space filtering."
            );
        }
        StateFilterOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "filter": filter,
                "filter_valid": true,
                "statistics": {
                    "total_explored": total_explored,
                    "max_depth": check_stats.max_depth,
                    "elapsed_seconds": elapsed,
                },
                "matched_states": [],
                "note": "Per-state filter evaluation requires state callback integration."
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Extract VARIABLES declarations from a module.
fn extract_var_names(module: &Module) -> Vec<std::sync::Arc<str>> {
    let mut vars = Vec::new();
    for unit in &module.units {
        if let Unit::Variable(var_decls) = &unit.node {
            for decl in var_decls {
                vars.push(std::sync::Arc::<str>::from(decl.node.as_str()));
            }
        }
    }
    vars
}

/// Find an operator definition by name in a TLA+ module.
fn find_operator<'a>(module: &'a Module, name: &str) -> Option<&'a OperatorDef> {
    module.units.iter().find_map(|unit| {
        if let Unit::Operator(op_def) = &unit.node {
            if op_def.name.node == name {
                return Some(op_def);
            }
        }
        None
    })
}

/// Parse a user-provided filter string into an `OperatorDef`.
fn parse_filter_expression(filter: &str) -> Result<OperatorDef> {
    let src = format!("---- MODULE __state_filter ----\n__filter_result == {filter}\n====");
    let tree = parse_to_syntax_tree(&src);
    let lower_result = lower(FileId(9998), &tree);

    if !lower_result.errors.is_empty() {
        let messages: Vec<String> = lower_result
            .errors
            .iter()
            .map(|e| e.message.clone())
            .collect();
        bail!(
            "failed to parse filter expression `{filter}`: {}",
            messages.join("; ")
        );
    }

    let filter_module = lower_result
        .module
        .context("filter expression lowering produced no module")?;

    let def = find_operator(&filter_module, "__filter_result")
        .ok_or_else(|| {
            anyhow::anyhow!("internal error: __filter_result not found after parsing filter")
        })?
        .clone();

    Ok(def)
}
