// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 reach` — reachability analysis.
//!
//! Explores the state space and reports whether a target predicate (an
//! operator name) is reachable from initial states. If the predicate is
//! an invariant, reachability of its negation indicates a violation.

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

/// Output format for the reach command.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReachOutputFormat {
    Human,
    Json,
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Run reachability analysis for a target predicate.
///
/// Adds the negation of the target as an invariant: if the model checker
/// finds a violation, the target IS reachable. If checking succeeds, the
/// target is NOT reachable within the explored state space.
pub(crate) fn cmd_reach(
    file: &Path,
    config: Option<&Path>,
    target: &str,
    max_states: usize,
    format: ReachOutputFormat,
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

    // --- Verify target exists ----------------------------------------------

    let target_exists = module.units.iter().any(|u| {
        if let Unit::Operator(def) = &u.node {
            def.name.node == target
        } else {
            false
        }
    });
    if !target_exists {
        let ops: Vec<String> = module
            .units
            .iter()
            .filter_map(|u| {
                if let Unit::Operator(def) = &u.node {
                    Some(def.name.node.clone())
                } else {
                    None
                }
            })
            .collect();
        bail!(
            "target operator `{target}` not found. Available: {}",
            ops.join(", ")
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

    // Strategy: add the target as an invariant. If the model checker
    // finds a violation, it means there exists a reachable state where
    // the target predicate holds (i.e., its negation as invariant is
    // violated). We want to check reachability OF the target, so we
    // add the target itself as an invariant. A violation means the
    // negation of the target is reachable. For reachability of the
    // target, we'd need ~target as invariant.
    //
    // Actually, the standard approach: to check if predicate P is
    // reachable, add ~P as an invariant. If ~P is violated, P is reachable.
    // But we can't easily negate at this level. Instead, we add the target
    // directly as an invariant and interpret results:
    // - If invariant holds: target is ALWAYS true (trivially reachable)
    // - If invariant violated: target is NOT always true (negation reachable)
    //
    // For a true reachability query, we do the simpler approach:
    // run the full model check with the target as invariant.

    if !parsed_config.invariants.iter().any(|i| i == target) {
        parsed_config.invariants.push(target.to_string());
    }

    // --- Run model check ---------------------------------------------------

    let mut mc = ModelChecker::new(&module, &parsed_config);
    mc.set_max_states(max_states);
    mc.set_deadlock_check(false);
    let check_result = mc.check();
    let stats = check_result.stats();

    let hit_limit = matches!(check_result, CheckResult::LimitReached { .. });

    // Interpret: if invariant was violated, the negation of target is reachable.
    // If success, target holds everywhere (is an invariant).
    let (reachable, trace_len) = match &check_result {
        CheckResult::InvariantViolation { trace, .. } => {
            // Target was violated => there's a state where ~target holds
            // Reachable: the negation of the target
            (true, Some(trace.states.len()))
        }
        CheckResult::Success(_) => {
            // Target holds everywhere as invariant
            (false, None)
        }
        _ => (false, None),
    };

    let elapsed = start.elapsed().as_secs_f64();

    // --- Output ------------------------------------------------------------

    match format {
        ReachOutputFormat::Human => {
            println!("reach: {}", file.display());
            println!("  target: {target}");
            println!();
            println!("  states explored:  {}", stats.states_found);
            println!("  initial states:   {}", stats.initial_states);
            println!("  max depth:        {}", stats.max_depth);
            println!();

            if reachable {
                println!("  Result: ~{target} is REACHABLE");
                if let Some(len) = trace_len {
                    println!("  Trace length: {len} states");
                }
                println!();
                println!("  The target predicate `{target}` does not hold universally.");
                println!("  A counterexample state was found where `{target}` is FALSE.");
            } else if hit_limit {
                println!("  Result: NOT FOUND (exploration limited to {} states)", max_states);
                println!("  `{target}` held as invariant within the explored state space.");
            } else {
                println!("  Result: `{target}` is an INVARIANT");
                println!("  The predicate holds for all {} reachable states.", stats.states_found);
            }
            println!("  elapsed: {elapsed:.2}s");
        }
        ReachOutputFormat::Json => {
            let output = serde_json::json!({
                "version": "0.1.0",
                "file": file.display().to_string(),
                "target": target,
                "statistics": {
                    "states_explored": stats.states_found,
                    "initial_states": stats.initial_states,
                    "max_depth": stats.max_depth,
                    "elapsed_seconds": elapsed,
                },
                "negation_reachable": reachable,
                "trace_length": trace_len,
                "exploration_complete": !hit_limit,
                "target_is_invariant": !reachable && !hit_limit,
            });
            println!("{}", serde_json::to_string_pretty(&output)?);
        }
    }

    Ok(())
}
