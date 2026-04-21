// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `tla2 aiger` subcommand: check AIGER bit-level hardware model checking benchmarks.
//!
//! Parses an AIGER file (.aag or .aig) and checks all safety properties
//! (bad-state literals) using either the SAT-based portfolio (BMC + k-induction
//! + IC3 variants) or the CHC-based z4-chc portfolio solver.
//!
//! Output follows the HWMCC convention:
//!   - `sat` on stdout if a bad state is reachable
//!   - `unsat` on stdout if all properties hold
//!   - `unknown` if the solver cannot determine the result

use std::path::Path;
use std::sync::mpsc;
use std::time::{Duration, Instant};

use anyhow::{Context, Result};

use crate::cli_schema::{AigerEngine, AigerPortfolio};

pub(crate) fn cmd_aiger(
    file: &Path,
    verbose: bool,
    witness_file: Option<&Path>,
    timeout_secs: Option<u64>,
    engine: AigerEngine,
    portfolio: AigerPortfolio,
) -> Result<()> {
    let start = Instant::now();

    let circuit = tla_aiger::parse_file(file)
        .map_err(|e| anyhow::anyhow!("AIGER parse error: {e}"))?;

    if verbose {
        eprintln!(
            "Parsed AIGER: maxvar={}, {} input(s), {} latch(es), {} AND(s), {} bad, {} constraint(s), {} justice, {} fairness",
            circuit.maxvar,
            circuit.inputs.len(),
            circuit.latches.len(),
            circuit.ands.len(),
            circuit.bad.len(),
            circuit.constraints.len(),
            circuit.justice.len(),
            circuit.fairness.len(),
        );
        let engine_desc = match engine {
            AigerEngine::Sat => match portfolio {
                AigerPortfolio::Default => "SAT (IC3 + BMC + k-induction portfolio)",
                AigerPortfolio::Full => "SAT (full IC3 portfolio)",
                AigerPortfolio::Competition => "SAT (competition portfolio)",
                AigerPortfolio::Adaptive => "SAT (adaptive preset-rotation portfolio, #4309)",
            },
            AigerEngine::Chc => "CHC (z4-chc adaptive portfolio)",
            AigerEngine::Bmc => "BMC only (bounded model checking, 1 thread)",
            AigerEngine::Kind => "k-induction only (1 thread)",
            AigerEngine::KindStrengthened => "strengthened k-induction (invariant discovery, 1 thread)",
            AigerEngine::Ic3 => "IC3/PDR only (1 thread)",
        };
        eprintln!("Engine: {engine_desc}");
    }

    let properties_count = if !circuit.bad.is_empty() {
        circuit.bad.len()
    } else {
        circuit.outputs.len()
    };

    if properties_count == 0 {
        if verbose {
            eprintln!("No safety properties to check.");
        }
        println!("unsat");
        return Ok(());
    }

    let timeout = timeout_secs.map(Duration::from_secs);
    let max_depth = 50_000usize;

    // Hard wall-clock deadline enforcement:
    // The portfolio's internal timeout mechanism relies on cooperative
    // cancellation (AtomicBool checked every ~1000 SAT decisions). When a
    // solver is stuck in a long SAT call, the portfolio's `handle.join()`
    // blocks indefinitely, causing the CLI to exceed the user-specified
    // timeout by 17+ minutes. Fix: spawn the engine call on a worker thread
    // and enforce a hard deadline from the main thread. If the deadline
    // expires, print "unknown" and exit immediately via process::exit().
    // The 5-second grace period gives cooperative cancellation time to work
    // for well-behaved engines, and process::exit() handles the rest.
    let results = if let Some(deadline) = timeout {
        let circuit_clone = circuit.clone();
        let (tx, rx) = mpsc::channel();
        std::thread::spawn(move || {
            let res = match engine {
                AigerEngine::Chc => tla_aiger::check_aiger(&circuit_clone, Some(deadline))
                    .unwrap_or_else(|e| {
                        vec![tla_aiger::AigerCheckResult::Unknown {
                            reason: format!("CHC error: {e}"),
                        }]
                    }),
                AigerEngine::Sat => {
                    check_aiger_sat_with_portfolio(&circuit_clone, Some(deadline), portfolio, verbose)
                }
                AigerEngine::Bmc
                | AigerEngine::Kind
                | AigerEngine::KindStrengthened
                | AigerEngine::Ic3 => {
                    check_aiger_single_engine(&circuit_clone, engine, max_depth, properties_count)
                }
            };
            let _ = tx.send(res);
        });

        // Wait for the result with a hard deadline: timeout + 5s grace period
        // for cooperative cancellation to take effect.
        let hard_deadline = deadline + Duration::from_secs(5);
        match rx.recv_timeout(hard_deadline) {
            Ok(results) => results,
            Err(_) => {
                if verbose {
                    eprintln!(
                        "Hard deadline exceeded ({:.1}s). Engines did not terminate \
                         within grace period. Exiting.",
                        hard_deadline.as_secs_f64(),
                    );
                }
                println!("unknown");
                // Use process::exit to terminate immediately. The portfolio
                // threads may still be stuck in SAT calls -- there is no safe
                // way to interrupt them from userspace since z4-sat's
                // cooperative cancellation failed within the grace period.
                // Exit code 124 follows the timeout(1) convention.
                std::process::exit(124);
            }
        }
    } else {
        // No timeout specified -- run without deadline enforcement.
        match engine {
            AigerEngine::Chc => tla_aiger::check_aiger(&circuit, timeout)
                .map_err(|e| anyhow::anyhow!("AIGER check error: {e}"))?,
            AigerEngine::Sat => {
                check_aiger_sat_with_portfolio(&circuit, timeout, portfolio, verbose)
            }
            AigerEngine::Bmc
            | AigerEngine::Kind
            | AigerEngine::KindStrengthened
            | AigerEngine::Ic3 => {
                check_aiger_single_engine(&circuit, engine, max_depth, properties_count)
            }
        }
    };

    let elapsed = start.elapsed();
    let mut any_sat = false;
    let mut any_unknown = false;
    let mut witness_lines: Vec<String> = Vec::new();

    for (idx, result) in results.iter().enumerate() {
        match result {
            tla_aiger::AigerCheckResult::Sat { trace } => {
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
            tla_aiger::AigerCheckResult::Unsat => {
                if verbose {
                    eprintln!("Property {idx}: HOLDS");
                }
            }
            tla_aiger::AigerCheckResult::Unknown { reason } => {
                any_unknown = true;
                if verbose {
                    eprintln!("Property {idx}: UNKNOWN ({reason})");
                }
            }
        }
    }

    // Print HWMCC result
    if results.len() > 1 {
        for result in &results {
            match result {
                tla_aiger::AigerCheckResult::Sat { .. } => println!("sat"),
                tla_aiger::AigerCheckResult::Unsat => println!("unsat"),
                tla_aiger::AigerCheckResult::Unknown { .. } => println!("unknown"),
            }
        }
    } else if any_sat {
        println!("sat");
    } else if any_unknown {
        println!("unknown");
    } else {
        println!("unsat");
    }

    // Write witness
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

/// Check AIGER safety properties using the SAT-based portfolio with a specific
/// portfolio mode. Uses `portfolio_check_detailed` for solver attribution when
/// verbose output is requested.
fn check_aiger_sat_with_portfolio(
    circuit: &tla_aiger::AigerCircuit,
    timeout: Option<Duration>,
    portfolio: AigerPortfolio,
    verbose: bool,
) -> Vec<tla_aiger::AigerCheckResult> {
    // Adaptive dispatches through portfolio_check_adaptive rather than the
    // static portfolio_check_detailed. See #4309.
    let portfolio_result = if matches!(portfolio, AigerPortfolio::Adaptive) {
        let adaptive_config = tla_aiger::AdaptivePortfolioConfig {
            timeout: timeout.unwrap_or(Duration::from_secs(3600)),
            ..Default::default()
        };
        tla_aiger::portfolio_check_adaptive(circuit, adaptive_config)
    } else {
        let mut config = match portfolio {
            AigerPortfolio::Default => tla_aiger::PortfolioConfig::default(),
            AigerPortfolio::Full => tla_aiger::full_ic3_portfolio(),
            AigerPortfolio::Competition => tla_aiger::competition_portfolio(),
            AigerPortfolio::Adaptive => unreachable!("handled above"),
        };
        if let Some(t) = timeout {
            config.timeout = t;
        }
        tla_aiger::portfolio_check_detailed(circuit, config)
    };

    if verbose {
        if !portfolio_result.solver_name.is_empty() {
            eprintln!(
                "Solved by: {} in {:.3}s",
                portfolio_result.solver_name, portfolio_result.time_secs
            );
        }
    }

    // Map the CheckResult to the existing AigerCheckResult type
    let n = if !circuit.bad.is_empty() {
        circuit.bad.len()
    } else {
        circuit.outputs.len()
    };

    if n == 0 {
        return vec![];
    }

    match portfolio_result.result {
        tla_aiger::CheckResult::Safe => {
            (0..n).map(|_| tla_aiger::AigerCheckResult::Unsat).collect()
        }
        tla_aiger::CheckResult::Unsafe { trace, .. } => {
            // Convert bool trace to i64 trace for compatibility
            let i64_trace: Vec<rustc_hash::FxHashMap<String, i64>> = trace
                .iter()
                .map(|step| {
                    step.iter()
                        .map(|(k, &v)| (k.clone(), if v { 1 } else { 0 }))
                        .collect()
                })
                .collect();

            if n == 1 {
                vec![tla_aiger::AigerCheckResult::Sat { trace: i64_trace }]
            } else {
                // Portfolio finds one violation; mark others as unknown
                let mut results = Vec::with_capacity(n);
                results.push(tla_aiger::AigerCheckResult::Sat { trace: i64_trace });
                for _ in 1..n {
                    results.push(tla_aiger::AigerCheckResult::Unknown {
                        reason: "other property not checked".into(),
                    });
                }
                results
            }
        }
        tla_aiger::CheckResult::Unknown { reason } => (0..n)
            .map(|_| tla_aiger::AigerCheckResult::Unknown {
                reason: reason.clone(),
            })
            .collect(),
    }
}

/// Check AIGER safety properties using a single engine (BMC, k-induction, or IC3).
///
/// Uses the convenience functions `check_bmc` / `check_kind` from tla-aiger,
/// or runs a single IC3 engine via the portfolio with one thread.
fn check_aiger_single_engine(
    circuit: &tla_aiger::AigerCircuit,
    engine: AigerEngine,
    max_depth: usize,
    properties_count: usize,
) -> Vec<tla_aiger::AigerCheckResult> {
    let ts = tla_aiger::transys::Transys::from_aiger(circuit);

    let bmc_result = match engine {
        AigerEngine::Bmc => tla_aiger::check_bmc(&ts, max_depth),
        AigerEngine::Kind => tla_aiger::check_kind(&ts, max_depth),
        AigerEngine::KindStrengthened => {
            // Run strengthened k-induction via portfolio config.
            let config = tla_aiger::PortfolioConfig {
                timeout: Duration::from_secs(3600),
                engines: vec![tla_aiger::EngineConfig::KindStrengthened],
                max_depth,
                preprocess: Default::default(),
            };
            let result = tla_aiger::portfolio_check(circuit, config);
            return check_result_to_aiger(result, properties_count);
        }
        AigerEngine::Ic3 => {
            // Run IC3 via single-engine portfolio config.
            let config = tla_aiger::PortfolioConfig {
                timeout: Duration::from_secs(3600),
                engines: vec![tla_aiger::EngineConfig::Ic3],
                max_depth,
                preprocess: Default::default(),
            };
            let result = tla_aiger::portfolio_check(circuit, config);
            return check_result_to_aiger(result, properties_count);
        }
        _ => unreachable!("only Bmc/Kind/KindStrengthened/Ic3 should reach here"),
    };

    // Convert BmcResult to AigerCheckResult
    match bmc_result.verdict {
        Some(true) => (0..properties_count)
            .map(|_| tla_aiger::AigerCheckResult::Unsat)
            .collect(),
        Some(false) => {
            let trace = if let Some(witness) = bmc_result.witness {
                witness
                    .iter()
                    .map(|step| {
                        step.iter()
                            .map(|lit| {
                                let name = format!("v{}", lit.var().0);
                                let val: i64 = if lit.is_positive() { 1 } else { 0 };
                                (name, val)
                            })
                            .collect()
                    })
                    .collect()
            } else {
                vec![]
            };

            if properties_count == 1 {
                vec![tla_aiger::AigerCheckResult::Sat { trace }]
            } else {
                let mut results = Vec::with_capacity(properties_count);
                results.push(tla_aiger::AigerCheckResult::Sat { trace });
                for _ in 1..properties_count {
                    results.push(tla_aiger::AigerCheckResult::Unknown {
                        reason: "other property not checked".into(),
                    });
                }
                results
            }
        }
        None => (0..properties_count)
            .map(|_| tla_aiger::AigerCheckResult::Unknown {
                reason: format!("reached bound {max_depth}"),
            })
            .collect(),
    }
}

/// Convert a CheckResult to a vector of AigerCheckResult.
fn check_result_to_aiger(
    result: tla_aiger::CheckResult,
    n: usize,
) -> Vec<tla_aiger::AigerCheckResult> {
    match result {
        tla_aiger::CheckResult::Safe => {
            (0..n).map(|_| tla_aiger::AigerCheckResult::Unsat).collect()
        }
        tla_aiger::CheckResult::Unsafe { trace, .. } => {
            let i64_trace: Vec<rustc_hash::FxHashMap<String, i64>> = trace
                .iter()
                .map(|step| {
                    step.iter()
                        .map(|(k, &v)| (k.clone(), if v { 1 } else { 0 }))
                        .collect()
                })
                .collect();
            if n == 1 {
                vec![tla_aiger::AigerCheckResult::Sat { trace: i64_trace }]
            } else {
                let mut results = Vec::with_capacity(n);
                results.push(tla_aiger::AigerCheckResult::Sat { trace: i64_trace });
                for _ in 1..n {
                    results.push(tla_aiger::AigerCheckResult::Unknown {
                        reason: "other property not checked".into(),
                    });
                }
                results
            }
        }
        tla_aiger::CheckResult::Unknown { reason } => (0..n)
            .map(|_| tla_aiger::AigerCheckResult::Unknown {
                reason: reason.clone(),
            })
            .collect(),
    }
}
