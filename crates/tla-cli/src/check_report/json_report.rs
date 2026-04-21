// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! JSON/JSONL model-checking result reporting.

use std::path::Path;

use anyhow::{bail, Context, Result};
use tla_check::{CheckResult, JsonOutput, SearchCompleteness, SoundnessProvenance};

use crate::cli_schema::OutputFormat;

use super::format_configured_bounds;

/// Context for JSON/JSONL result reporting.
pub(crate) struct JsonReportCtx<'a> {
    pub output_format: OutputFormat,
    pub checker_modules: &'a [&'a tla_core::ast::Module],
    pub module: &'a tla_core::ast::Module,
    pub file: &'a Path,
    pub config_path: &'a Path,
    pub workers: usize,
    pub soundness: &'a SoundnessProvenance,
    pub completeness: SearchCompleteness,
    pub config: &'a tla_check::Config,
    pub result: &'a CheckResult,
    pub elapsed: std::time::Duration,
    pub strategy_info: Option<&'a str>,
    pub max_states: usize,
    pub max_depth: usize,
}

/// Report model checking results in JSON/JSONL format.
pub(crate) fn report_check_json(ctx: &JsonReportCtx<'_>) -> Result<()> {
    // Extract variable names from all modules (main + extended)
    let mut variables: Vec<String> = Vec::new();

    for ext_mod in ctx.checker_modules {
        for unit in &ext_mod.units {
            if let tla_core::ast::Unit::Variable(vars) = &unit.node {
                for v in vars {
                    if !variables.contains(&v.node) {
                        variables.push(v.node.clone());
                    }
                }
            }
        }
    }

    for unit in &ctx.module.units {
        if let tla_core::ast::Unit::Variable(vars) = &unit.node {
            for v in vars {
                if !variables.contains(&v.node) {
                    variables.push(v.node.clone());
                }
            }
        }
    }

    variables.sort();

    let mut json_output = JsonOutput::new(
        ctx.file,
        Some(ctx.config_path),
        &ctx.module.name.node,
        ctx.workers,
    )
    .with_soundness(ctx.soundness.clone())
    .with_completeness(ctx.completeness)
    .with_spec_info(
        ctx.config.init.as_deref(),
        ctx.config.next.as_deref(),
        ctx.config.invariants.clone(),
        ctx.config.properties.clone(),
        variables,
    )
    .with_check_result(ctx.result, ctx.elapsed);

    if let Some(info) = ctx.strategy_info {
        json_output.add_info("I001", info);
    }
    if let Some(bounds) = format_configured_bounds(ctx.max_states, ctx.max_depth) {
        json_output.add_info("I002", &format!("Configured bounds: {}", bounds));
    }

    let json_str = if matches!(ctx.output_format, OutputFormat::Jsonl) {
        json_output.to_json_compact().context("serialize JSON")?
    } else {
        json_output.to_json().context("serialize JSON")?
    };
    println!("{}", json_str);

    match ctx.result {
        CheckResult::Success(_) | CheckResult::LimitReached { .. } => Ok(()),
        // Check completed with errors — JSON output already contains the full error.
        // Exit directly to avoid returning Err, which would trigger a second JSON
        // emission in main.rs's error handler (corrupting diagnose output parsing).
        CheckResult::InvariantViolation { .. }
        | CheckResult::PropertyViolation { .. }
        | CheckResult::LivenessViolation { .. }
        | CheckResult::Deadlock { .. }
        | CheckResult::Error { .. } => std::process::exit(1),
        _ => bail!(
            "Model checking produced a result variant unsupported by this tla2 version; upgrade tla2"
        ),
    }
}
