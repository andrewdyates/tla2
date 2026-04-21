// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 countex` — counterexample analysis and classification.
//!
//! Runs model checking and, if a violation is found, classifies the
//! counterexample by type (invariant, deadlock, liveness), length,
//! and involved variables. Provides a structured summary for debugging.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the countex command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CountexOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Run model checking and analyze any counterexample found.
pub(crate) fn cmd_countex(
    file: &Path,
    config: Option<&Path>,
    max_states: usize,
    format: CountexOutputFormat,
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

    // --- Run model checker -------------------------------------------------

    let mut mc = ModelChecker::new(&module, &parsed_config);
    mc.set_max_states(max_states);
    let check_result = mc.check();
    let stats = check_result.stats();

    let elapsed = start.elapsed().as_secs_f64();

    // --- Classify result ---------------------------------------------------

    match format {
        CountexOutputFormat::Human => {
            println!("countex: {}", file.display());
            println!("  states explored: {}", stats.states_found);
            println!();

            match &check_result {
                CheckResult::Success(_) => {
                    println!("  result: NO VIOLATION FOUND");
                    println!("  The specification passed all checks within the explored state space.");
                }
                CheckResult::InvariantViolation { invariant, trace, stats: _ } => {
                    println!("  result: INVARIANT VIOLATION");
                    println!("  invariant: {invariant}");
                    println!("  trace length: {} states", trace.states.len());
                    println!();
                    println!("  Counterexample trace:");
                    for (i, state) in trace.states.iter().enumerate() {
                        println!("    State {i}:");
                        for (var, val) in state.vars() {
                            println!("      {var} = {val}");
                        }
                    }
                }
                CheckResult::Deadlock { trace, stats: _ } => {
                    println!("  result: DEADLOCK");
                    println!("  trace length: {} states", trace.states.len());
                    println!();
                    println!("  Deadlock trace:");
                    for (i, state) in trace.states.iter().enumerate() {
                        println!("    State {i}:");
                        for (var, val) in state.vars() {
                            println!("      {var} = {val}");
                        }
                    }
                }
                CheckResult::LivenessViolation { property, prefix, cycle, stats: _ } => {
                    println!("  result: LIVENESS VIOLATION");
                    println!("  property: {property}");
                    println!("  prefix length: {} states", prefix.states.len());
                    println!("  cycle length:  {} states", cycle.states.len());
                }
                CheckResult::LimitReached { limit_type, stats: _ } => {
                    println!("  result: LIMIT REACHED ({limit_type:?})");
                    println!("  No violation found within the explored limit.");
                }
                CheckResult::Error { error, .. } => {
                    println!("  result: ERROR");
                    println!("  {error}");
                }
                _ => {
                    println!("  result: UNKNOWN");
                }
            }

            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        CountexOutputFormat::Json => {
            let (result_type, trace_len) = match &check_result {
                CheckResult::Success(_) => ("pass", 0),
                CheckResult::InvariantViolation { trace, .. } => ("invariant_violation", trace.states.len()),
                CheckResult::Deadlock { trace, .. } => ("deadlock", trace.states.len()),
                CheckResult::LivenessViolation { prefix, cycle, .. } => {
                    ("liveness_violation", prefix.states.len() + cycle.states.len())
                }
                CheckResult::LimitReached { .. } => ("limit_reached", 0),
                CheckResult::Error { .. } => ("error", 0),
                _ => ("unknown", 0),
            };

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "result": result_type,
                "trace_length": trace_len,
                "states_explored": stats.states_found,
                "max_depth": stats.max_depth,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
