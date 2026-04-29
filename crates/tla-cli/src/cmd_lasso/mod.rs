// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 lasso` — lasso-shaped counterexample analysis.
//!
//! A lasso trace has a "stem" (finite prefix reaching the loop entry) and a
//! "loop" (a cycle that repeats forever). This command:
//!
//! 1. Model-checks a TLA+ spec (optionally targeting a specific temporal property).
//! 2. If a liveness violation is found, reports the lasso decomposition
//!    directly from the model checker's prefix (stem) and cycle (loop).
//! 3. Reports the decomposition with action labels and statistics.

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

/// Output format for the lasso command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LassoOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Run lasso analysis on a TLA+ spec.
pub(crate) fn cmd_lasso(
    file: &Path,
    config: Option<&Path>,
    property: Option<&str>,
    max_states: usize,
    format: LassoOutputFormat,
) -> Result<()> {
    let start = Instant::now();

    // --- Parse and lower -----------------------------------------------------

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

    // --- Load config ---------------------------------------------------------

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

    // Inject user-specified property if provided.
    if let Some(prop) = property {
        if !parsed_config.properties.iter().any(|p| p == prop) {
            parsed_config.properties.push(prop.to_string());
        }
    }

    let has_properties = !parsed_config.properties.is_empty();

    // --- Run model check -----------------------------------------------------

    let mut mc = ModelChecker::new(&module, &parsed_config);
    mc.set_max_states(max_states);
    let check_result = mc.check();
    let stats = check_result.stats();

    let elapsed = start.elapsed().as_secs_f64();
    let is_success = matches!(check_result, CheckResult::Success(_));

    // --- Extract lasso from LivenessViolation --------------------------------

    let lasso = extract_lasso(&check_result);

    // --- Output ---------------------------------------------------------------

    match format {
        LassoOutputFormat::Human => {
            println!("lasso: {}", file.display());
            if let Some(prop) = property {
                println!("  property: {prop}");
            }
            println!(
                "  BFS explored {} states (depth {}) in {elapsed:.1}s",
                stats.states_found, stats.max_depth,
            );
            if !has_properties {
                println!();
                println!("  Warning: no temporal properties configured.");
                println!("  Use --property <name> or add PROPERTY to the .cfg file.");
            }
            match &lasso {
                Some(info) => {
                    println!();
                    println!("  Lasso found (property: {}):", info.property);
                    println!("    stem length:  {} states", info.stem_len);
                    println!("    loop length:  {} states", info.loop_len);
                    println!("    total trace:  {} states", info.stem_len + info.loop_len);
                    if !info.stem_actions.is_empty() {
                        println!();
                        println!("  Stem ({} steps):", info.stem_actions.len());
                        for (i, action) in info.stem_actions.iter().enumerate() {
                            println!("    [{i}] {action}");
                        }
                    }
                    if !info.loop_actions.is_empty() {
                        println!();
                        println!("  Loop ({} steps):", info.loop_actions.len());
                        for (i, action) in info.loop_actions.iter().enumerate() {
                            println!("    [{i}] {action}");
                        }
                    }
                }
                None => {
                    println!();
                    if is_success {
                        println!(
                            "  No lasso found — model checking passed with {} states.",
                            stats.states_found,
                        );
                    } else {
                        println!("  Violation found but no lasso structure detected.");
                        println!("  (Safety violations produce finite traces, not lassos.)");
                    }
                }
            }
        }
        LassoOutputFormat::Json => {
            let lasso_json = lasso.as_ref().map(|info| {
                serde_json::json!({
                    "property": info.property,
                    "stem_length": info.stem_len,
                    "loop_length": info.loop_len,
                    "stem_actions": info.stem_actions,
                    "loop_actions": info.loop_actions,
                })
            });

            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "property": property,
                "has_temporal_properties": has_properties,
                "statistics": {
                    "states_explored": stats.states_found,
                    "max_depth": stats.max_depth,
                    "elapsed_seconds": elapsed,
                },
                "model_check_passed": is_success,
                "lasso": lasso_json,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Lasso extraction
// ---------------------------------------------------------------------------

struct LassoInfo {
    property: String,
    stem_len: usize,
    loop_len: usize,
    stem_actions: Vec<String>,
    loop_actions: Vec<String>,
}

/// Extract lasso structure from a LivenessViolation result.
///
/// The model checker already provides `prefix` (stem) and `cycle` (loop)
/// as separate traces — no fingerprint comparison needed.
fn extract_lasso(check_result: &CheckResult) -> Option<LassoInfo> {
    match check_result {
        CheckResult::LivenessViolation {
            property,
            prefix,
            cycle,
            ..
        } => {
            let stem_actions: Vec<String> =
                prefix.action_labels.iter().map(|l| l.to_string()).collect();
            let loop_actions: Vec<String> =
                cycle.action_labels.iter().map(|l| l.to_string()).collect();

            Some(LassoInfo {
                property: property.clone(),
                stem_len: prefix.states.len(),
                loop_len: cycle.states.len(),
                stem_actions,
                loop_actions,
            })
        }
        _ => None,
    }
}
