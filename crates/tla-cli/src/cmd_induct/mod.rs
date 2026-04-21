// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 induct` — inductive invariant checking.
//!
//! Verifies whether a candidate invariant holds over all reachable states
//! by running the model checker with the invariant added. Reports whether
//! the invariant is maintained (a necessary condition for inductiveness).
//!
//! # Limitations
//!
//! True inductiveness requires checking that Inv /\ Next => Inv' holds for
//! ALL states (including unreachable ones). This command approximates that
//! by checking reachable states only via BFS model checking.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::ast::{Module, OperatorDef, Unit};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the induct command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InductOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Run inductive invariant checking.
pub(crate) fn cmd_induct(
    file: &Path,
    config: Option<&Path>,
    invariant: &str,
    max_states: usize,
    format: InductOutputFormat,
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

    // --- Verify invariant exists -------------------------------------------

    let inv_exists = find_operator(&module, invariant).is_some();
    if !inv_exists {
        bail!(
            "operator `{invariant}` not found in module `{}`. \
             Available operators: {}",
            module.name.node,
            list_operators(&module).join(", ")
        );
    }

    // --- Load config -------------------------------------------------------

    let config_path_buf = match config {
        Some(p) => p.to_path_buf(),
        None => {
            let mut cfg = file.to_path_buf();
            cfg.set_extension("cfg");
            cfg
        }
    };

    let mut parsed_config = if config_path_buf.exists() {
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

    // Add the candidate invariant to the config.
    if !parsed_config.invariants.iter().any(|i| i == invariant) {
        parsed_config.invariants.push(invariant.to_string());
    }

    // --- Run model check with invariant ------------------------------------

    let mut mc = ModelChecker::new(&module, &parsed_config);
    mc.set_max_states(max_states);
    mc.set_deadlock_check(false);
    let check_result = mc.check();
    let stats = check_result.stats();

    let inv_holds = matches!(check_result, CheckResult::Success(_));
    let hit_limit = matches!(check_result, CheckResult::LimitReached { .. });

    // Extract violation info if invariant was violated.
    let violation_info = match &check_result {
        CheckResult::InvariantViolation {
            invariant: inv_name,
            trace,
            ..
        } => Some((inv_name.clone(), trace.states.len())),
        _ => None,
    };

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        InductOutputFormat::Human => {
            println!("induct: {}", file.display());
            println!("  candidate invariant: {invariant}");
            println!();
            println!("  Reachable state check:");
            println!("    states explored:  {}", stats.states_found);
            println!("    initial states:   {}", stats.initial_states);
            println!("    max depth:        {}", stats.max_depth);
            println!(
                "    invariant holds:  {}",
                if inv_holds {
                    "YES"
                } else {
                    "NO"
                }
            );

            if let Some((ref viol_name, trace_len)) = violation_info {
                println!();
                println!("  Violation:");
                println!("    invariant:    {viol_name}");
                println!("    trace length: {trace_len} states");
            }

            println!();
            if inv_holds && !hit_limit {
                println!("  Verdict: INVARIANT (holds for all {} reachable states)", stats.states_found);
                println!();
                println!("  Note: This confirms the invariant holds on reachable states.");
                println!("  Full inductiveness (Inv /\\ Next => Inv') requires checking");
                println!("  unreachable states too. Use symbolic methods for a complete");
                println!("  inductive proof.");
            } else if inv_holds && hit_limit {
                println!("  Verdict: HOLDS SO FAR (exploration limited to {} states)", stats.states_found);
                println!("  Use --max-states to increase the exploration bound.");
            } else {
                println!("  Verdict: NOT INVARIANT (violated within {} states)", stats.states_found);
            }
            println!("  elapsed: {elapsed:.2}s");
        }
        InductOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "invariant": invariant,
                "statistics": {
                    "states_explored": stats.states_found,
                    "initial_states": stats.initial_states,
                    "max_depth": stats.max_depth,
                    "elapsed_seconds": elapsed,
                },
                "invariant_holds": inv_holds,
                "exploration_complete": !hit_limit,
                "violation": violation_info.as_ref().map(|(name, len)| {
                    serde_json::json!({
                        "invariant": name,
                        "trace_length": len,
                    })
                }),
                "verdict": if inv_holds && !hit_limit {
                    "invariant"
                } else if inv_holds {
                    "holds_so_far"
                } else {
                    "not_invariant"
                },
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn find_operator<'a>(module: &'a Module, name: &str) -> Option<&'a OperatorDef> {
    module.units.iter().find_map(|unit| {
        if let Unit::Operator(def) = &unit.node {
            if def.name.node == name {
                return Some(def);
            }
        }
        None
    })
}

fn list_operators(module: &Module) -> Vec<String> {
    module
        .units
        .iter()
        .filter_map(|unit| {
            if let Unit::Operator(def) = &unit.node {
                Some(def.name.node.clone())
            } else {
                None
            }
        })
        .collect()
}
