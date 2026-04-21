// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 deadlock-free` — verify deadlock freedom with diagnostics.
//!
//! Runs model checking focused on deadlock detection and provides
//! detailed analysis of deadlock states when found.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the deadlock-free command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DeadlockfreeOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Check deadlock freedom with detailed diagnostics.
pub(crate) fn cmd_deadlockfree(
    file: &Path,
    config: Option<&Path>,
    max_states: usize,
    format: DeadlockfreeOutputFormat,
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

    let mut mc = ModelChecker::new(&module, &parsed_config);
    mc.set_max_states(max_states);
    mc.set_deadlock_check(true);
    let check_result = mc.check();
    let stats = check_result.stats();

    let (is_deadlock_free, deadlock_depth, deadlock_vars) = match &check_result {
        CheckResult::Deadlock { trace, .. } => {
            let depth = trace.states.len();
            let vars: Vec<String> = if let Some(last) = trace.states.last() {
                last.vars().map(|(name, val)| format!("{name} = {val}")).collect()
            } else {
                Vec::new()
            };
            (false, Some(depth), vars)
        }
        _ => (true, None, Vec::new()),
    };

    let elapsed = start.elapsed().as_secs_f64();

    match format {
        DeadlockfreeOutputFormat::Human => {
            println!("deadlock-free: {}", file.display());
            println!("  deadlock free: {}", if is_deadlock_free { "YES" } else { "NO" });
            println!("  states explored: {}", stats.states_found);
            println!("  max depth: {}", stats.max_depth);
            if let Some(depth) = deadlock_depth {
                println!();
                println!("  Deadlock found at depth {depth}:");
                for v in &deadlock_vars {
                    println!("    {v}");
                }
            }
            println!();
            println!("  elapsed: {elapsed:.2}s");
        }
        DeadlockfreeOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "deadlock_free": is_deadlock_free,
                "states_explored": stats.states_found,
                "max_depth": stats.max_depth,
                "deadlock_depth": deadlock_depth,
                "deadlock_state": deadlock_vars,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
