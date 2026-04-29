// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 prove` command: theorem proving via Z3.

use std::path::Path;
use std::time::{Duration, Instant};

use anyhow::{bail, Context, Result};
use tla_core::{lower_error_diagnostic, lower_main_module, FileId};
use tla_prove::{ModuleResult, ProofOutcome, Prover};

use crate::{parse_or_report, read_source};

pub(crate) fn cmd_prove(
    file: &Path,
    timeout_secs: u64,
    theorem_filter: Option<&str>,
) -> Result<()> {
    let source = read_source(file)?;
    let tree = parse_or_report(file, &source)?;

    let hint_name = file
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty());
    let result = lower_main_module(FileId(0), &tree, hint_name);
    if !result.errors.is_empty() {
        let file_path = file.display().to_string();
        for err in &result.errors {
            let diagnostic = lower_error_diagnostic(&file_path, &err.message, err.span);
            diagnostic.eprint(&file_path, &source);
        }
        bail!("lower failed with {} error(s)", result.errors.len());
    }
    let module = result.module.context("lower produced no module")?;

    let filter_names: Option<Vec<&str>> = theorem_filter.map(|f| f.split(',').collect());

    let mut prover = Prover::new();
    prover.set_timeout(Duration::from_secs(timeout_secs));

    println!("Proving theorems in: {}", file.display());
    println!("Timeout per obligation: {}s", timeout_secs);
    if let Some(ref names) = filter_names {
        println!("Theorem filter: {}", names.join(", "));
    }
    println!();

    let start = Instant::now();
    let result = prover
        .check_module(&module)
        .map_err(|e| anyhow::anyhow!("Proof error: {}", e))?;
    let elapsed = start.elapsed();

    let theorems: Vec<_> = if let Some(ref names) = filter_names {
        result
            .theorems
            .iter()
            .filter(|t| names.iter().any(|n| *n == t.name))
            .collect()
    } else {
        result.theorems.iter().collect()
    };

    report_proof_results(&result, &theorems, elapsed)
}

fn report_proof_results(
    result: &ModuleResult,
    theorems: &[&tla_prove::TheoremResult],
    elapsed: Duration,
) -> Result<()> {
    let mut all_proved = true;

    for thm in theorems {
        let status = if thm.is_proved() {
            "PROVED"
        } else if thm.failed_count() > 0 {
            all_proved = false;
            "FAILED"
        } else {
            all_proved = false;
            "UNKNOWN"
        };

        println!(
            "THEOREM {}: {} ({} obligations, {:.3}s)",
            thm.name,
            status,
            thm.obligations.len(),
            thm.duration.as_secs_f64()
        );

        if !thm.is_proved() {
            for (i, obl) in thm.obligations.iter().enumerate() {
                let obl_status = match &obl.outcome {
                    ProofOutcome::Proved => "proved",
                    ProofOutcome::Failed { .. } => "FAILED",
                    ProofOutcome::Unknown { .. } => "unknown",
                };
                println!(
                    "  Obligation {}: {} (backend: {}, {:.3}s)",
                    i + 1,
                    obl_status,
                    obl.backend,
                    obl.duration.as_secs_f64()
                );

                if let ProofOutcome::Failed {
                    message,
                    counterexample,
                } = &obl.outcome
                {
                    println!("    {}", message);
                    if let Some(ce) = counterexample {
                        for (var, val) in ce {
                            println!("    {} = {}", var, val);
                        }
                    }
                }

                if let ProofOutcome::Unknown { reason } = &obl.outcome {
                    println!("    Reason: {}", reason);
                }
            }
        }
    }

    println!();
    println!("Summary:");
    println!("  Module: {}", result.name);
    println!(
        "  Theorems: {} proved, {} failed, {} unknown",
        theorems.iter().filter(|t| t.is_proved()).count(),
        theorems.iter().filter(|t| t.failed_count() > 0).count(),
        theorems
            .iter()
            .filter(|t| !t.is_proved() && t.failed_count() == 0)
            .count()
    );
    println!(
        "  Obligations: {} total, {} proved, {} failed, {} unknown",
        result.total_obligations(),
        result.proved_count(),
        result.failed_count(),
        result.unknown_count()
    );
    println!("  Cache hits: {}", prover_cache_note());
    println!("  Time: {:.3}s", elapsed.as_secs_f64());

    if all_proved && !theorems.is_empty() {
        println!();
        println!("All theorems proved successfully!");
        Ok(())
    } else if theorems.is_empty() {
        println!();
        println!("No theorems found in module.");
        Ok(())
    } else {
        println!();
        bail!("Some theorems could not be proved");
    }
}

fn prover_cache_note() -> &'static str {
    "(check prover.cache_size() for actual count)"
}
