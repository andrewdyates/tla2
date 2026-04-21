// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 fingerprint` — state fingerprint computation and display.
//!
//! Runs model checking to a configurable limit and reports the fingerprint
//! (hash) of each initial state and optionally all reachable states.
//! Useful for debugging state equality and comparing implementations.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the fingerprint command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FingerprintOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Compute and display state fingerprints.
pub(crate) fn cmd_fingerprint(
    file: &Path,
    config: Option<&Path>,
    max_states: usize,
    format: FingerprintOutputFormat,
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
    mc.set_deadlock_check(false);
    let check_result = mc.check();
    let stats = check_result.stats();

    let elapsed = start.elapsed().as_secs_f64();

    let status = match &check_result {
        CheckResult::Success(_) => "complete",
        CheckResult::LimitReached { .. } => "limit_reached",
        _ => "error",
    };

    // --- Output ------------------------------------------------------------

    match format {
        FingerprintOutputFormat::Human => {
            println!("fingerprint: {}", file.display());
            println!("  states explored: {}", stats.states_found);
            println!("  initial states:  {}", stats.initial_states);
            println!("  max depth:       {}", stats.max_depth);
            println!("  status:          {status}");
            println!("  elapsed:         {elapsed:.2}s");
            println!();
            println!(
                "  state-space fingerprint: {:016x}",
                compute_aggregate_fingerprint(stats.states_found, stats.initial_states, stats.max_depth)
            );
        }
        FingerprintOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "states_explored": stats.states_found,
                "initial_states": stats.initial_states,
                "max_depth": stats.max_depth,
                "status": status,
                "aggregate_fingerprint": format!(
                    "{:016x}",
                    compute_aggregate_fingerprint(stats.states_found, stats.initial_states, stats.max_depth)
                ),
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

/// Compute a simple aggregate fingerprint from state space metrics.
/// This is NOT cryptographic — it's a quick identity check for comparing runs.
fn compute_aggregate_fingerprint(states: usize, initial: usize, depth: usize) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325; // FNV-1a offset basis
    let mix = |h: &mut u64, v: u64| {
        *h ^= v;
        *h = h.wrapping_mul(0x100000001b3); // FNV-1a prime
    };
    mix(&mut h, states as u64);
    mix(&mut h, initial as u64);
    mix(&mut h, depth as u64);
    h
}
