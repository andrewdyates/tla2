// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]

//! Benchmark z4-sat on DIMACS files
//!
//! Usage: cargo run --release --example bench_dimacs -- [DIMACS_FILE...]
//!
//! Reads DIMACS CNF files, solves them with z4-sat, and reports solve timing.

use std::time::Instant;
use z4_sat::{parse_dimacs, Solver};

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <dimacs_file>...", args[0]);
        eprintln!("       {} benchmarks/dimacs/*.cnf  (glob)", args[0]);
        std::process::exit(1);
    }

    let mut total_solve_time = 0.0;
    let mut total_overall_time = 0.0;
    let mut sat_count = 0;
    let mut unsat_count = 0;
    let mut error_count = 0;

    for path in &args[1..] {
        match std::fs::read_to_string(path) {
            Ok(content) => {
                let overall_start = Instant::now();
                match parse_dimacs(&content) {
                    Ok(formula) => {
                        let mut solver: Solver = formula.into_solver();
                        // Debug knobs for isolating preprocessing/inprocessing issues.
                        // These are intentionally scoped to this example binary.
                        if std::env::var("Z4_SAT_DISABLE_PREPROCESS").is_ok() {
                            solver.set_preprocess_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_BVE").is_ok() {
                            solver.set_bve_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_BCE").is_ok() {
                            solver.set_bce_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_SWEEP").is_ok() {
                            solver.set_sweep_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_PROBE").is_ok() {
                            solver.set_probe_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_SUBSUME").is_ok() {
                            solver.set_subsume_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_VIVIFY").is_ok() {
                            solver.set_vivify_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_HTR").is_ok() {
                            solver.set_htr_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_TRANSRED").is_ok() {
                            solver.set_transred_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_GATES").is_ok() {
                            solver.set_congruence_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_WALK").is_ok() {
                            solver.set_walk_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_WARMUP").is_ok() {
                            solver.set_warmup_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_FACTOR").is_ok() {
                            solver.set_factor_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_CONGRUENCE").is_ok() {
                            solver.set_congruence_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_DECOMPOSE").is_ok() {
                            solver.set_decompose_enabled(false);
                        }
                        if std::env::var("Z4_SAT_DISABLE_CONDITION").is_ok() {
                            solver.set_condition_enabled(false);
                        }
                        let solve_start = Instant::now();
                        let result = solver.solve().into_inner();
                        let solve_elapsed = solve_start.elapsed().as_secs_f64();
                        let overall_elapsed = overall_start.elapsed().as_secs_f64();
                        total_solve_time += solve_elapsed;
                        total_overall_time += overall_elapsed;

                        let status = match &result {
                            z4_sat::SatResult::Sat(_) => {
                                sat_count += 1;
                                "SAT"
                            }
                            z4_sat::SatResult::Unsat => {
                                unsat_count += 1;
                                "UNSAT"
                            }
                            z4_sat::SatResult::Unknown => "UNKNOWN",
                            #[allow(unreachable_patterns)]
                            _ => unreachable!(),
                        };

                        // Print stats in verbose mode (set VERBOSE=1)
                        if std::env::var("VERBOSE").is_ok() {
                            println!(
                                "{:6} {:8.3}ms  total: {:8.3}ms  c:{:>8} d:{:>8} r:{:>6} p:{:>10}  {}",
                                status,
                                solve_elapsed * 1000.0,
                                overall_elapsed * 1000.0,
                                solver.num_conflicts(),
                                solver.num_decisions(),
                                solver.num_restarts(),
                                solver.num_propagations(),
                                path
                            );
                        } else {
                            println!(
                                "{:6} {:8.3}ms  total: {:8.3}ms  {}",
                                status,
                                solve_elapsed * 1000.0,
                                overall_elapsed * 1000.0,
                                path
                            );
                        }
                    }
                    Err(e) => {
                        error_count += 1;
                        eprintln!("PARSE ERROR: {path} - {e}");
                    }
                }
            }
            Err(e) => {
                error_count += 1;
                eprintln!("READ ERROR: {path} - {e}");
            }
        }
    }

    println!("\n--- Summary ---");
    println!(
        "Total: {} files, {} SAT, {} UNSAT, {} errors",
        args.len() - 1,
        sat_count,
        unsat_count,
        error_count
    );
    println!("Total solve time: {total_solve_time:.3}s");
    println!("Total overall time: {total_overall_time:.3}s");
    if sat_count + unsat_count > 0 {
        println!(
            "Average solve time: {:.3}ms",
            total_solve_time * 1000.0 / f64::from(sat_count + unsat_count)
        );
    }
}
