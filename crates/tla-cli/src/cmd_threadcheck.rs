// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 thread-check` -- verify a ConcurrentModel JSON from tRust.
//!
//! Reads a `ConcurrentModel` JSON file, generates a TLA+ module, runs the
//! model checker, and reports structured verification results.

use std::path::Path;

use anyhow::{Context, Result};
use tla_concurrent::{
    check_concurrent_model, CheckOptions, ConcurrentModel, MappedTrace, VerificationStatus,
};

use crate::cli_schema::ThreadCheckOutputFormat;

pub(crate) fn cmd_threadcheck(
    file: &Path,
    workers: usize,
    max_states: usize,
    max_depth: usize,
    emit_tla: bool,
    output: ThreadCheckOutputFormat,
) -> Result<()> {
    let json = std::fs::read_to_string(file)
        .with_context(|| format!("failed to read {}", file.display()))?;
    let model: ConcurrentModel = serde_json::from_str(&json)
        .with_context(|| format!("failed to parse ConcurrentModel from {}", file.display()))?;

    let options = CheckOptions {
        workers,
        max_states,
        max_depth,
        emit_tla,
    };

    let result = check_concurrent_model(&model, &options)?;

    if emit_tla {
        if let Some(tla) = &result.generated_tla {
            eprintln!("--- Generated TLA+ ---");
            eprintln!("{tla}");
            eprintln!("--- End TLA+ ---");
        }
    }

    let exit_code = match result.report.status {
        VerificationStatus::AllPropertiesHold => 0,
        VerificationStatus::DeadlockDetected
        | VerificationStatus::InvariantViolation
        | VerificationStatus::PropertyViolation
        | VerificationStatus::LivenessViolation => 1,
        _ => 2,
    };

    match output {
        ThreadCheckOutputFormat::Human => {
            println!("Status: {:?}", result.report.status);
            if let Some(prop) = &result.report.violated_property {
                println!("Violated: {prop}");
            }
            println!("States: {}", result.report.stats.states_found);
            if let Some(ref trace) = result.report.counterexample {
                println!();
                println!("Counterexample:");
                print!("{trace}");
            }

            if let (Some(ref prefix), Some(ref cycle)) = (
                &result.report.liveness_prefix,
                &result.report.liveness_cycle,
            ) {
                println!();
                println!("Liveness Counterexample:");
                print!("{}", MappedTrace::format_liveness(prefix, cycle));
            }
            println!(
                "Assumptions: thread_bound={}, memory_model={:?}",
                result.assumptions.thread_bound, result.assumptions.memory_model
            );
        }
        ThreadCheckOutputFormat::Json => {
            println!(
                "{}",
                serde_json::to_string_pretty(&result)
                    .context("failed to serialize result to JSON")?
            );
        }
    }

    std::process::exit(exit_code);
}
