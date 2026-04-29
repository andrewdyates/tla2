// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 state-graph` — export state graph in DOT format.
//!
//! Runs bounded model checking and exports the state graph
//! as a DOT digraph for visualization.

use std::path::Path;
use std::time::Instant;

use anyhow::{bail, Context, Result};

use tla_check::{CheckResult, Config, ModelChecker};
use tla_core::{lower, parse_to_syntax_tree, FileId};

use crate::helpers::read_source;

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// Output format for the state-graph command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StategraphOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Export state graph summary.
pub(crate) fn cmd_stategraph(
    file: &Path,
    config: Option<&Path>,
    max_states: usize,
    format: StategraphOutputFormat,
) -> Result<()> {
    let start = Instant::now();

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
    mc.set_deadlock_check(false);
    let check_result = mc.check();
    let stats = check_result.stats();

    let converged = matches!(&check_result, CheckResult::Success(_));
    let elapsed = start.elapsed().as_secs_f64();

    match format {
        StategraphOutputFormat::Human => {
            println!("state-graph: {}", file.display());
            println!("  states: {}", stats.states_found);
            println!("  initial: {}", stats.initial_states);
            println!("  max depth: {}", stats.max_depth);
            println!("  converged: {}", if converged { "yes" } else { "no" });
            println!();
            println!("  (use --format json for structured output)");
            println!("  elapsed: {elapsed:.2}s");
        }
        StategraphOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "states": stats.states_found,
                "initial_states": stats.initial_states,
                "max_depth": stats.max_depth,
                "converged": converged,
                "elapsed_seconds": elapsed,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
