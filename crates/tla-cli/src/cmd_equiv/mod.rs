// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 equiv` — equivalence checking between two TLA+ specifications.
//!
//! Checks whether two specs produce identical state spaces by running model
//! checking on both and comparing state counts, depth, and initial states.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::{CheckResult, CheckStats, Config, ModelChecker};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the equiv command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EquivOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Run equivalence checking between two TLA+ specs.
pub(crate) fn cmd_equiv(
    file_a: &Path,
    file_b: &Path,
    config_a: Option<&Path>,
    config_b: Option<&Path>,
    max_states: usize,
    format: EquivOutputFormat,
) -> Result<()> {
    let start = Instant::now();

    // Check both specs.
    let (stats_a, ok_a) = check_spec(file_a, config_a, max_states, FileId(0))?;
    let (stats_b, ok_b) = check_spec(file_b, config_b, max_states, FileId(1))?;

    let states_match = stats_a.states_found == stats_b.states_found;
    let depth_match = stats_a.max_depth == stats_b.max_depth;
    let init_match = stats_a.initial_states == stats_b.initial_states;
    let both_ok = ok_a && ok_b;

    let equivalent = states_match && depth_match && init_match && both_ok;

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        EquivOutputFormat::Human => {
            println!("equiv:");
            println!("  spec A: {}", file_a.display());
            println!("  spec B: {}", file_b.display());
            println!();
            println!(
                "  {:25} {:>12} {:>12}  {}",
                "metric", "spec A", "spec B", "match"
            );
            println!("  {:-<25} {:-<12} {:-<12}  {:-<5}", "", "", "", "");
            println!(
                "  {:25} {:>12} {:>12}  {}",
                "states",
                stats_a.states_found,
                stats_b.states_found,
                if states_match { "yes" } else { "NO" }
            );
            println!(
                "  {:25} {:>12} {:>12}  {}",
                "max depth",
                stats_a.max_depth,
                stats_b.max_depth,
                if depth_match { "yes" } else { "NO" }
            );
            println!(
                "  {:25} {:>12} {:>12}  {}",
                "initial states",
                stats_a.initial_states,
                stats_b.initial_states,
                if init_match { "yes" } else { "NO" }
            );
            println!(
                "  {:25} {:>12} {:>12}  {}",
                "check passed",
                if ok_a { "yes" } else { "no" },
                if ok_b { "yes" } else { "no" },
                if both_ok { "yes" } else { "NO" }
            );
            println!();
            println!(
                "  verdict: {}",
                if equivalent {
                    "EQUIVALENT (state spaces match)"
                } else {
                    "DIFFERENT (state spaces differ)"
                }
            );
            println!("  elapsed: {elapsed:.2}s");
        }
        EquivOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "spec_a": {
                    "file": file_a.display().to_string(),
                    "states": stats_a.states_found,
                    "max_depth": stats_a.max_depth,
                    "initial_states": stats_a.initial_states,
                    "passed": ok_a,
                },
                "spec_b": {
                    "file": file_b.display().to_string(),
                    "states": stats_b.states_found,
                    "max_depth": stats_b.max_depth,
                    "initial_states": stats_b.initial_states,
                    "passed": ok_b,
                },
                "comparison": {
                    "states_match": states_match,
                    "depth_match": depth_match,
                    "init_match": init_match,
                    "both_passed": both_ok,
                },
                "equivalent": equivalent,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Parse, lower, and model-check a single spec. Returns (stats, success).
fn check_spec(
    file: &Path,
    config: Option<&Path>,
    max_states: usize,
    file_id: FileId,
) -> Result<(CheckStats, bool)> {
    let source = read_source(file)?;
    let tree = parse_to_syntax_tree(&source);
    let lower_result = lower(file_id, &tree);
    if !lower_result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &lower_result.errors {
            let diagnostic = tla_core::lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!(
            "lowering failed for {}: {} error(s)",
            file.display(),
            lower_result.errors.len()
        );
    }
    let module = lower_result
        .module
        .with_context(|| format!("lowering produced no module for {}", file.display()))?;

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
            anyhow::anyhow!(
                "config parse failed for {}: {} error(s)",
                config_path_buf.display(),
                errors.len()
            )
        })?
    } else {
        Config {
            init: Some("Init".to_string()),
            next: Some("Next".to_string()),
            ..Default::default()
        }
    };

    let mut mc = ModelChecker::new(&module, &parsed_config);
    mc.set_max_states(max_states);
    mc.set_deadlock_check(false);
    let check_result = mc.check();
    let stats = check_result.stats().clone();
    let is_success = matches!(check_result, CheckResult::Success(_));

    Ok((stats, is_success))
}
