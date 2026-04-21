// Copyright 2026 Andrew Yates.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Execution mode implementations for the Z4 CLI.
//!
//! Contains the interactive (stdin), piped, and file-based execution
//! paths. Extracted from `main.rs` to keep each file under 500 lines.

use std::io::{self, BufRead, Write};

use z4_dpll::Executor;
use z4_frontend::{collect_formula_stats, parse, Command, FormulaStats};

use super::{
    chc_runner, dimacs, eprintln_smt_error, exit_if_timed_out, stats_output, ProofConfig,
    ProofFormat, INTERRUPT_HANDLE, PROGRESS_ENABLED,
};

/// Create an executor with global timeout interrupt wired in (#2971).
fn new_executor() -> Executor {
    let mut executor = Executor::new();
    if let Some(handle) = INTERRUPT_HANDLE.get() {
        executor.set_interrupt(handle.clone());
    }
    // Wire progress flag so SAT solvers inside the SMT pipeline emit
    // periodic status lines when --progress is set.
    if PROGRESS_ENABLED.load(std::sync::atomic::Ordering::Relaxed) {
        executor.set_progress_enabled(true);
    }
    executor
}

/// Execute a command and print the result.
///
/// This centralizes executor.execute result handling to avoid duplication.
/// Output is printed to stdout, errors to stderr in SMT-LIB format.
///
/// Per SMT-LIB 2.6, when check-sat returns "unknown", the solver SHOULD
/// emit `(:reason-unknown ...)` so the user knows why satisfiability could
/// not be determined. We emit this to stderr automatically after printing
/// the "unknown" result to stdout.
fn execute_and_print(executor: &mut Executor, cmd: &Command) -> bool {
    match executor.execute(cmd) {
        Ok(Some(output)) => {
            safe_println!("{output}");
            // SMT-LIB compliance: emit reason-unknown to stderr when
            // check-sat produces "unknown", so users always know why.
            if output == "unknown" {
                if let Some(reason) = executor.get_reason_unknown() {
                    safe_eprintln!("(:reason-unknown {reason})");
                } else {
                    safe_eprintln!("(:reason-unknown unknown)");
                }
            }
            true
        }
        Ok(None) => true,
        Err(e) => {
            eprintln_smt_error(e);
            false
        }
    }
}

/// Print SMT-LIB executor statistics to stderr (Z3 `-st` style)
/// plus the canonical RunStatistics envelope.
fn print_smt_stats(
    executor: &Executor,
    formula_stats: Option<&FormulaStats>,
    stats_cfg: stats_output::StatsConfig,
) {
    if stats_cfg.human {
        let dpll_stats = executor.statistics();
        safe_eprintln!("{dpll_stats}");
        if let Some(formula_stats) = formula_stats {
            safe_eprintln!("{formula_stats}");
        }
    }

    // Canonical envelope
    let dpll_stats = executor.statistics();
    let elapsed = super::global_elapsed();
    let result_str = if executor.last_result_is_unsat() {
        "unsat"
    } else if executor.get_reason_unknown().is_some() {
        "unknown"
    } else {
        "sat"
    };
    let mut run_stats =
        stats_output::RunStatistics::new(stats_output::SolveMode::Smt, result_str, elapsed);
    run_stats.insert("conflicts", dpll_stats.conflicts);
    run_stats.insert("decisions", dpll_stats.decisions);
    run_stats.insert("propagations", dpll_stats.propagations);
    run_stats.insert("restarts", dpll_stats.restarts);
    run_stats.insert("smt.theory_conflicts", dpll_stats.theory_conflicts);
    run_stats.insert("smt.theory_propagations", dpll_stats.theory_propagations);
    run_stats.emit(stats_cfg);
}

fn write_alethe_proof(executor: &Executor, proof_config: &ProofConfig) {
    if proof_config.format != ProofFormat::Alethe {
        safe_eprintln!(
            "Error: proof file '{}' uses DRAT/LRAT format, but SMT-LIB solving produces Alethe proofs",
            proof_config.path
        );
        std::process::exit(1);
    }
    if !executor.last_result_is_unsat() {
        return;
    }
    let Some(proof) = executor.last_proof() else {
        safe_eprintln!(
            "Error: UNSAT result produced no proof despite --proof {}",
            proof_config.path
        );
        std::process::exit(1);
    };
    let rendered = z4_proof::export_alethe(proof, executor.terms());
    if let Err(error) = std::fs::write(&proof_config.path, rendered) {
        safe_eprintln!(
            "Error: failed to write proof file {}: {error}",
            proof_config.path
        );
        std::process::exit(1);
    }
}

pub(super) fn run_interactive(
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
    incremental: bool,
) {
    use std::io::IsTerminal;

    let stdin = io::stdin();
    let is_tty = stdin.is_terminal();

    // If stdin is piped (not a TTY) and not in incremental mode,
    // read all at once and process like a file.
    // When --incremental is set, always use the line-by-line path (#5360).
    if !is_tty && !incremental {
        use std::io::Read;
        let mut content = String::new();
        let read_result = stdin.lock().read_to_string(&mut content);
        if let Err(e) = read_result {
            eprintln_smt_error(format_args!("Error reading stdin: {e}"));
            std::process::exit(1);
        }

        // Check for DIMACS CNF format (content-based detection for stdin)
        if dimacs::is_dimacs_format(&content) {
            dimacs::run_dimacs_from_content(&content, stats_cfg, proof_config);
            return;
        }

        // Check for HORN logic
        if is_horn_logic(&content) {
            chc_runner::run_chc_from_content(&content, false, false, stats_cfg, proof_config);
            return;
        }

        // Standard DPLL(T) path
        match parse(&content) {
            Ok(commands) => {
                let formula_stats = collect_formula_stats(&commands);
                let mut executor = new_executor();
                if let Some(proof) = proof_config {
                    if proof.format != ProofFormat::Alethe {
                        safe_eprintln!(
                            "Error: proof file '{}' uses DRAT/LRAT format, but SMT-LIB mode requires Alethe output",
                            proof.path
                        );
                        std::process::exit(1);
                    }
                    executor.set_produce_proofs(true);
                }
                for cmd in &commands {
                    match cmd {
                        Command::Exit => {
                            if stats_cfg.any() {
                                print_smt_stats(&executor, Some(&formula_stats), stats_cfg);
                            }
                            if let Some(proof) = proof_config {
                                write_alethe_proof(&executor, proof);
                            }
                            return;
                        }
                        _ => {
                            if !execute_and_print(&mut executor, cmd) {
                                exit_if_timed_out();
                                std::process::exit(1);
                            }
                        }
                    }
                    exit_if_timed_out();
                }
                if stats_cfg.any() {
                    print_smt_stats(&executor, Some(&formula_stats), stats_cfg);
                }
                if let Some(proof) = proof_config {
                    write_alethe_proof(&executor, proof);
                }
            }
            Err(e) => {
                eprintln_smt_error(&e);
                std::process::exit(1);
            }
        }
        return;
    }

    // Line-by-line mode: TTY interactive OR piped incremental (#5360)
    if is_tty {
        safe_println!("{}", super::features::interactive_banner());
    }

    let mut stdout = io::stdout();
    let mut input_buffer = String::new();
    let mut executor = new_executor();
    let mut formula_stats = FormulaStats::default();
    if let Some(proof) = proof_config {
        if proof.format != ProofFormat::Alethe {
            safe_eprintln!(
                "Error: proof file '{}' uses DRAT/LRAT format, but SMT-LIB mode requires Alethe output",
                proof.path
            );
            std::process::exit(1);
        }
        executor.set_produce_proofs(true);
    }

    loop {
        exit_if_timed_out();
        if is_tty {
            safe_print!("> ");
        }
        let _ = stdout.flush();

        let mut line = String::new();
        let read_result = stdin.lock().read_line(&mut line);
        match read_result {
            Ok(0) => break,
            Ok(_) => {}
            Err(e) => {
                safe_eprintln!("Error reading input: {e}");
                break;
            }
        }

        input_buffer.push_str(&line);

        match parse(&input_buffer) {
            Ok(commands) => {
                input_buffer.clear();
                for cmd in &commands {
                    formula_stats.observe_command(cmd);
                    if matches!(cmd, Command::Exit) {
                        if stats_cfg.any() {
                            print_smt_stats(&executor, Some(&formula_stats), stats_cfg);
                        }
                        if let Some(proof) = proof_config {
                            write_alethe_proof(&executor, proof);
                        }
                        return;
                    }
                    execute_and_print(&mut executor, cmd);
                    // Flush after each command so pipe consumers see responses
                    // immediately (stdout is block-buffered when piped).
                    let _ = stdout.flush();
                    exit_if_timed_out();
                }
            }
            Err(_) => {
                let opens = input_buffer.matches('(').count();
                let closes = input_buffer.matches(')').count();
                if opens <= closes {
                    if let Ok(commands) = parse(&input_buffer) {
                        input_buffer.clear();
                        for cmd in &commands {
                            formula_stats.observe_command(cmd);
                            if matches!(cmd, Command::Exit) {
                                if stats_cfg.any() {
                                    print_smt_stats(&executor, Some(&formula_stats), stats_cfg);
                                }
                                if let Some(proof) = proof_config {
                                    write_alethe_proof(&executor, proof);
                                }
                                return;
                            }
                            execute_and_print(&mut executor, cmd);
                            let _ = stdout.flush();
                            exit_if_timed_out();
                        }
                    } else if let Err(e) = parse(&input_buffer) {
                        eprintln_smt_error(&e);
                        input_buffer.clear();
                    } else {
                        eprintln_smt_error("parse error: unexpected input");
                        input_buffer.clear();
                    }
                }
            }
        }
    }
    if stats_cfg.any() {
        print_smt_stats(&executor, Some(&formula_stats), stats_cfg);
    }
    if let Some(proof) = proof_config {
        write_alethe_proof(&executor, proof);
    }
}

pub(super) fn run_file(
    path: &str,
    stats_cfg: stats_output::StatsConfig,
    proof_config: Option<&ProofConfig>,
) {
    match std::fs::read_to_string(path) {
        Ok(content) => {
            // Check for DIMACS CNF format first (by extension or content)
            if dimacs::has_cnf_extension(path) || dimacs::is_dimacs_format(&content) {
                dimacs::run_dimacs_from_content(&content, stats_cfg, proof_config);
                return;
            }

            // Check for HORN logic and route to CHC solver if found
            if is_horn_logic(&content) {
                chc_runner::run_chc_from_content(&content, false, false, stats_cfg, proof_config);
                return;
            }

            // Parse and execute all commands (standard DPLL(T) path)
            match parse(&content) {
                Ok(commands) => {
                    let formula_stats = collect_formula_stats(&commands);
                    let mut executor = new_executor();
                    if let Some(proof) = proof_config {
                        if proof.format != ProofFormat::Alethe {
                            safe_eprintln!(
                                "Error: proof file '{}' uses DRAT/LRAT format, but SMT-LIB mode requires Alethe output",
                                proof.path
                            );
                            std::process::exit(1);
                        }
                        executor.set_produce_proofs(true);
                    }
                    for cmd in &commands {
                        match cmd {
                            Command::Exit => {
                                if stats_cfg.any() {
                                    print_smt_stats(&executor, Some(&formula_stats), stats_cfg);
                                }
                                if let Some(proof) = proof_config {
                                    write_alethe_proof(&executor, proof);
                                }
                                return;
                            }
                            _ => {
                                if !execute_and_print(&mut executor, cmd) {
                                    exit_if_timed_out();
                                    std::process::exit(1);
                                }
                            }
                        }
                        exit_if_timed_out();
                    }
                    if stats_cfg.any() {
                        print_smt_stats(&executor, Some(&formula_stats), stats_cfg);
                    }
                    if let Some(proof) = proof_config {
                        write_alethe_proof(&executor, proof);
                    }
                }
                Err(e) => {
                    eprintln_smt_error(&e);
                    std::process::exit(1);
                }
            }
        }
        Err(e) => {
            eprintln_smt_error(format_args!("Error reading file '{path}': {e}"));
            std::process::exit(1);
        }
    }
}

/// Check if content uses HORN logic
pub(super) fn is_horn_logic(content: &str) -> bool {
    // Fast check: look for "(set-logic HORN)" in the content
    // This is more efficient than parsing the entire file
    if let Ok(commands) = parse(content) {
        commands
            .iter()
            .any(|cmd| matches!(cmd, Command::SetLogic(logic) if logic == "HORN"))
    } else {
        // Fallback: simple string check for unparseable content
        content.contains("(set-logic HORN)")
    }
}
