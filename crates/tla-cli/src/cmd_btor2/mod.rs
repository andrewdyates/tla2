// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `tla2 btor2` subcommand: check BTOR2 hardware model checking benchmarks.
//!
//! Parses a BTOR2 file and runs the full HWMCC portfolio pipeline:
//! 1. Cone-of-influence (COI) reduction — eliminate irrelevant states/inputs
//! 2. Expression simplification — constant folding, identity elimination
//! 3. BMC preprocessing — try shallow bounded model checking first
//! 4. Full CHC solving — PDR/k-induction via z4-chc adaptive portfolio
//!
//! Output follows the HWMCC convention:
//!   - `sat` on stdout if the property is violated (bad state reachable)
//!   - `unsat` on stdout if the property holds (bad state unreachable)
//!   - `unknown` if the solver cannot determine the result

use std::path::Path;
use std::time::{Duration, Instant};

use anyhow::{Context, Result};

/// Run the `tla2 btor2` subcommand.
///
/// Reads and parses a BTOR2 file, then runs the full HWMCC portfolio
/// strategy: COI reduction -> BMC preprocessing -> full CHC solving.
pub(crate) fn cmd_btor2(
    file: &Path,
    verbose: bool,
    witness_file: Option<&Path>,
    timeout_secs: Option<u64>,
) -> Result<()> {
    let start = Instant::now();

    // Read the BTOR2 source.
    let source = std::fs::read_to_string(file)
        .with_context(|| format!("failed to read BTOR2 file: {}", file.display()))?;

    // Parse.
    let program =
        tla_btor2::parse_btor2(&source).map_err(|e| anyhow::anyhow!("BTOR2 parse error: {e}"))?;

    if verbose {
        eprintln!(
            "Parsed BTOR2: {} lines, {} state(s), {} input(s), {} bad property(ies), {} constraint(s)",
            program.lines.len(),
            program.num_states,
            program.num_inputs,
            program.bad_properties.len(),
            program.constraints.len(),
        );
    }

    if program.bad_properties.is_empty() {
        if verbose {
            eprintln!("No bad properties to check.");
        }
        println!("unsat");
        return Ok(());
    }

    // Run the full portfolio strategy (COI + BMC + CHC).
    let portfolio_config = tla_btor2::PortfolioConfig {
        time_budget: timeout_secs.map(Duration::from_secs),
        enable_coi: true,
        enable_simplify: true,
        enable_bmc: true,
        bmc_budget_fraction: 0.2,
        bmc_max_depth: 20,
        verbose,
    };

    let (results, stats) = tla_btor2::check_btor2_portfolio(&program, &portfolio_config)
        .map_err(|e| anyhow::anyhow!("BTOR2 portfolio error: {e}"))?;

    if verbose {
        eprintln!(
            "Portfolio stats: COI {}/{} states ({}/{} inputs), phase={:?}",
            stats.states_after_coi,
            stats.states_before_coi,
            stats.inputs_after_coi,
            stats.inputs_before_coi,
            stats.result_phase,
        );
        eprintln!(
            "  COI: {:.3}s, BMC: {:.3}s, CHC: {:.3}s, Total: {:.3}s",
            stats.coi_time.as_secs_f64(),
            stats.bmc_time.as_secs_f64(),
            stats.chc_time.as_secs_f64(),
            stats.total_time.as_secs_f64(),
        );
    }

    let elapsed = start.elapsed();
    let mut any_sat = false;
    let mut any_unknown = false;
    let mut witness_lines: Vec<String> = Vec::new();

    for (idx, result) in results.iter().enumerate() {
        match result {
            tla_btor2::Btor2CheckResult::Sat { trace } => {
                any_sat = true;
                if verbose {
                    eprintln!(
                        "Property {idx}: VIOLATED (counterexample with {} step(s))",
                        trace.len()
                    );
                    for (step_idx, step) in trace.iter().enumerate() {
                        let mut assignments: Vec<_> = step.iter().collect();
                        assignments.sort_by_key(|(k, _)| k.clone());
                        eprintln!("  Step {step_idx}:");
                        for (name, val) in &assignments {
                            eprintln!("    {name} = {val}");
                        }
                    }
                }

                // HWMCC witness format: "sat\nb<property_idx>\n" followed by
                // state assignments per frame.
                witness_lines.push(format!("b{idx}"));
                for step in trace {
                    let mut assignments: Vec<_> = step.iter().collect();
                    assignments.sort_by_key(|(k, _)| k.clone());
                    let frame: String = assignments
                        .iter()
                        .map(|(k, v)| format!("{k}={v}"))
                        .collect::<Vec<_>>()
                        .join(" ");
                    witness_lines.push(frame);
                }
                witness_lines.push(".".to_string());
            }
            tla_btor2::Btor2CheckResult::Unsat => {
                if verbose {
                    eprintln!("Property {idx}: HOLDS");
                }
            }
            tla_btor2::Btor2CheckResult::Unknown { reason } => {
                any_unknown = true;
                if verbose {
                    eprintln!("Property {idx}: UNKNOWN ({reason})");
                }
            }
        }
    }

    // Print HWMCC result to stdout.
    // For multi-property benchmarks, emit one verdict line per property so
    // that each `bad` statement's result is correctly attributed.
    if results.len() > 1 {
        for result in &results {
            match result {
                tla_btor2::Btor2CheckResult::Sat { .. } => println!("sat"),
                tla_btor2::Btor2CheckResult::Unsat => println!("unsat"),
                tla_btor2::Btor2CheckResult::Unknown { .. } => println!("unknown"),
            }
        }
    } else if any_sat {
        println!("sat");
    } else if any_unknown {
        println!("unknown");
    } else {
        println!("unsat");
    }

    // Write witness file if requested and there is a counterexample.
    if let Some(witness_path) = witness_file {
        if !witness_lines.is_empty() {
            let content = witness_lines.join("\n") + "\n";
            std::fs::write(witness_path, &content).with_context(|| {
                format!("failed to write witness file: {}", witness_path.display())
            })?;
            if verbose {
                eprintln!("Witness written to {}", witness_path.display());
            }
        }
    }

    if verbose {
        eprintln!("Elapsed: {:.3}s", elapsed.as_secs_f64());
    }

    Ok(())
}
