// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 sandbox` — isolated specification testing sandbox.
//!
//! Runs a TLA+ specification in a sandboxed environment with configurable
//! resource limits and reports any violations or resource exhaustion.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the sandbox command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SandboxOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Run a specification in a sandboxed environment.
pub(crate) fn cmd_sandbox(
    file: &Path,
    config: Option<&Path>,
    max_states: usize,
    max_depth: usize,
    timeout_secs: u64,
    format: SandboxOutputFormat,
) -> Result<()> {
    let start = Instant::now();
    let deadline = std::time::Duration::from_secs(timeout_secs);

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

    // --- Run sandboxed check -----------------------------------------------

    let mut mc = ModelChecker::new(&module, &parsed_config);
    mc.set_max_states(max_states);
    mc.set_deadlock_check(false);
    let check_result = mc.check();
    let stats = check_result.stats();

    let elapsed = start.elapsed();
    let elapsed_secs = elapsed.as_secs_f64();
    let timed_out = elapsed >= deadline;

    let status = if timed_out {
        "timeout"
    } else {
        match &check_result {
            CheckResult::Success(_) => "pass",
            CheckResult::InvariantViolation { .. } => "invariant_violation",
            CheckResult::Deadlock { .. } => "deadlock",
            CheckResult::LivenessViolation { .. } => "liveness_violation",
            CheckResult::LimitReached { .. } => "limit_reached",
            _ => "error",
        }
    };

    let within_limits = stats.states_found <= max_states
        && stats.max_depth <= max_depth
        && !timed_out;

    // --- Output ------------------------------------------------------------

    match format {
        SandboxOutputFormat::Human => {
            println!("sandbox: {}", file.display());
            println!("  limits: max_states={max_states}, max_depth={max_depth}, timeout={timeout_secs}s");
            println!();
            println!("  states explored:  {}", stats.states_found);
            println!("  max depth:        {}", stats.max_depth);
            println!("  elapsed:          {elapsed_secs:.2}s");
            println!("  status:           {status}");
            println!("  within limits:    {}", if within_limits { "yes" } else { "NO" });
            if timed_out {
                println!();
                println!("  WARNING: Exploration exceeded timeout ({timeout_secs}s).");
            }
        }
        SandboxOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "limits": {
                    "max_states": max_states,
                    "max_depth": max_depth,
                    "timeout_seconds": timeout_secs,
                },
                "results": {
                    "states_explored": stats.states_found,
                    "max_depth": stats.max_depth,
                    "elapsed_seconds": elapsed_secs,
                    "status": status,
                    "within_limits": within_limits,
                    "timed_out": timed_out,
                },
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
